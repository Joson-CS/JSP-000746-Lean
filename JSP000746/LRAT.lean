import Mathlib.Tactic.Sat.FromLRAT
import JSP000746.DIMACS
import JSP000746.SATEncoding
import JSP000746.Reduction

/-!
# JSP-000746 — Kernel-checked LRAT certificate

The command below reads the actual DIMACS and LRAT files from disk at
elaboration time.  Mathlib reconstructs the proof and the Lean kernel checks
the generated theorem.
-/

namespace JSP000746

open SATEncoding DIMACS
open Lean Elab Command

lrat_proof core_lrat_proof
  (include_str "../certificates/core.cnf")
  (include_str "../certificates/core.lrat")

/-!
`lrat_proof` deliberately presents its result as a reified propositional DNF.
For the semantic bridge it is more convenient to expose the checker's
underlying private `Sat.Fmla.proof`.  The command below only gives public names
to the formula and proof which the preceding `lrat_proof` command already
created.  Both declarations are type-checked by the kernel.
-/

syntax (name := exposeLratFmlaProof)
  "expose_lrat_fmla_proof " ident ppSpace "as " ident ppSpace ident : command

elab_rules : command
  | `(expose_lrat_fmla_proof $source:ident as $formula:ident $proof:ident) => do
      let currNamespace ← getCurrNamespace
      let sourceName := currNamespace ++ source.getId
      let formulaName := currNamespace ++ formula.getId
      let proofName := currNamespace ++ proof.getId
      let declarations := (← getEnv).constants.toList
      let ctxNeedle := sourceName.toString ++ ".ctx_"
      let proofNeedle := sourceName.toString ++ ".proof_"
      let some ctxName := declarations.findSome? fun (name, _) ↦
          if name.toString.contains ctxNeedle then some name else none
        | throwError "could not find the checked LRAT formula for {sourceName}"
      let some checkedProofName := declarations.findSome? fun (name, _) ↦
          if name.toString.contains proofNeedle then some name else none
        | throwError "could not find the checked LRAT proof for {sourceName}"
      Command.liftTermElabM do
        addDecl <| Declaration.defnDecl {
          name := formulaName
          levelParams := []
          type := mkConst ``Sat.Fmla
          value := mkConst ctxName
          hints := ReducibilityHints.regular 0
          safety := DefinitionSafety.safe
        }
        let expectedType := mkApp2 (mkConst ``Sat.Fmla.proof)
          (mkConst formulaName) (mkConst ``Sat.Clause.nil)
        let checkedProof ← Term.ensureHasType (some expectedType)
          (mkConst checkedProofName)
        addDecl <| Declaration.thmDecl {
          name := proofName
          levelParams := []
          type := expectedType
          value := checkedProof
        }

expose_lrat_fmla_proof core_lrat_proof as diskSatFormula disk_sat_fmla_proof

/-!
The checker stores its 888 input clauses as a balanced tree of `Sat.Fmla.and`
nodes.  Expose the two semantic blocks as ordinary lists without reducing the
project's exporter.  This makes the subsequent comparison local: 816 triangle
clauses and 72 additive clauses.
-/

private partial def collectLratClauses (e : Expr) : MetaM (Array Expr) := do
  if e.isAppOfArity ``Sat.Fmla.and 2 then
    return (← collectLratClauses (e.getArg! 0)) ++
      (← collectLratClauses (e.getArg! 1))
  else if e.isAppOfArity ``Sat.Fmla.one 1 then
    return #[e.getArg! 0]
  else
    throwError "unexpected checked LRAT formula node: {e}"

syntax (name := exposeLratFmlaBlocks)
  "expose_lrat_fmla_blocks " ident ppSpace "as " ident ppSpace ident : command

elab_rules : command
  | `(expose_lrat_fmla_blocks $source:ident as $triangles:ident $additives:ident) => do
      let currNamespace ← getCurrNamespace
      let sourceName := currNamespace ++ source.getId
      let triangleName := currNamespace ++ triangles.getId
      let additiveName := currNamespace ++ additives.getId
      let ctxNeedle := sourceName.toString ++ ".ctx_"
      let some ctxName := (← getEnv).constants.toList.findSome? fun (name, _) ↦
          if name.toString.contains ctxNeedle then some name else none
        | throwError "could not find the checked LRAT formula for {sourceName}"
      Command.liftTermElabM do
        let some ctxValue := (← getConstInfo ctxName).value? (allowOpaque := true)
          | throwError "checked LRAT formula {ctxName} has no definition"
        let clauses ← collectLratClauses ctxValue
        unless clauses.size = 888 do
          throwError "expected 888 checked clauses, found {clauses.size}"
        let triangleValue ← Lean.Meta.mkListLit (mkConst ``Sat.Clause)
          (clauses.extract 0 816).toList
        let additiveValue ← Lean.Meta.mkListLit (mkConst ``Sat.Clause)
          (clauses.extract 816 888).toList
        for (name, value) in [(triangleName, triangleValue), (additiveName, additiveValue)] do
          addDecl <| Declaration.defnDecl {
            name
            levelParams := []
            type := mkConst ``Sat.Fmla
            value
            hints := ReducibilityHints.regular 0
            safety := DefinitionSafety.safe
          }
          enableRealizationsForConst name

expose_lrat_fmla_blocks core_lrat_proof as diskTriangleClauses diskAdditiveClauses

/- The checked disk formula is the triangle block followed by the additive block. -/
set_option maxRecDepth 100000 in
theorem diskSatFormula_split :
    diskSatFormula = diskTriangleClauses ++ diskAdditiveClauses := by
  rfl

/-- Convert one Boolean edge clause to signed DIMACS integers. -/
def clauseToSigned (clause : Clause) : SignedDIMACSClause :=
  clause.map fun literal ↦ (literalToDIMACS literal).toInt

/-- Convert one Boolean edge clause to Mathlib's zero-based SAT literals. -/
def clauseToSat (clause : Clause) : Sat.Clause :=
  (clauseToSigned clause).map Sat.Literal.ofInt

/-- Convert a signed DIMACS formula exactly as Mathlib's parser does. -/
def signedFormulaToSat (formula : SignedDIMACSFormula) : Sat.Fmla :=
  formula.map fun clause ↦ (clause.map Sat.Literal.ofInt : Sat.Clause)

/-- The exported integer clauses, converted exactly as Mathlib's DIMACS parser does. -/
def exportedSatFormula : Sat.Fmla :=
  signedFormulaToSat exportedDIMACSFormula

/-- Mapping signed clauses to Mathlib clauses preserves concatenation. -/
theorem signedFormulaToSat_append (left right : SignedDIMACSFormula) :
    signedFormulaToSat (left ++ right) =
      signedFormulaToSat left ++ signedFormulaToSat right := by
  exact List.map_append

/-- The signed 816-clause triangle block produced by the deterministic exporter. -/
def exportedTriangleSigned : SignedDIMACSFormula :=
  orderedTriangleIndices.map fun t ↦ clauseToSigned (triangleClause t)

/-- The signed 72-clause additive block produced by the deterministic exporter. -/
def exportedAdditiveSigned : SignedDIMACSFormula :=
  orderedAdditiveIndices.map fun t ↦ clauseToSigned (additiveClause t)

/-- The signed exporter itself splits before any SAT-literal conversion. -/
theorem exportedDIMACSFormula_split :
    exportedDIMACSFormula = exportedTriangleSigned ++ exportedAdditiveSigned := by
  unfold exportedDIMACSFormula encodedDIMACSFormula orderedCoreCNF
  rw [List.map_append, List.map_append]
  simp only [exportedTriangleSigned, exportedAdditiveSigned, clauseToSigned,
    Function.comp_def, List.map_map]

/-- The 816 triangle clauses as consumed by Mathlib's LRAT checker. -/
def exportedTriangleClauses : Sat.Fmla :=
  signedFormulaToSat exportedTriangleSigned

/-- The 72 additive clauses as consumed by Mathlib's LRAT checker. -/
def exportedAdditiveClauses : Sat.Fmla :=
  signedFormulaToSat exportedAdditiveSigned

/-- The deterministic exporter has exactly the same 816/72 block decomposition. -/
theorem exportedSatFormula_split :
    exportedSatFormula = exportedTriangleClauses ++ exportedAdditiveClauses := by
  rw [exportedSatFormula, exportedDIMACSFormula_split, signedFormulaToSat_append]
  rfl

/-! ## Checked clause blocks agree with the deterministic exporter -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expands and checks the 72 concrete additive clauses against the disk block.
theorem diskAdditiveClauses_eq_exported :
    diskAdditiveClauses = exportedAdditiveClauses := by
  simp (config := { maxSteps := 500000 })
    [diskAdditiveClauses, exportedAdditiveClauses, exportedAdditiveSigned,
      signedFormulaToSat, clauseToSigned, orderedAdditiveIndices, orderedVertices,
      vertexOfFin, vertexValue, additiveClause, literalToDIMACS,
      DIMACSLiteral.toInt, Sat.Literal.ofInt, Sat.Clause, Sat.Clause.cons,
      Sat.Clause.nil]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expands and checks all 816 three-literal triangle clauses independently of the LRAT proof.
theorem diskTriangleClauses_eq_exported :
    diskTriangleClauses = exportedTriangleClauses := by
  simp (config := { maxSteps := 2000000 })
    [diskTriangleClauses, exportedTriangleClauses, exportedTriangleSigned,
      signedFormulaToSat, clauseToSigned, orderedTriangleIndices, orderedVertices,
      vertexOfFin, triangleClause, literalToDIMACS, DIMACSLiteral.toInt,
      Sat.Literal.ofInt, Sat.Clause, Sat.Clause.cons, Sat.Clause.nil]
  rfl

/-- The checker input and the formula constructed by the Lean exporter are identical. -/
theorem diskSatFormula_eq_exported : diskSatFormula = exportedSatFormula := by
  rw [diskSatFormula_split, exportedSatFormula_split,
    diskTriangleClauses_eq_exported, diskAdditiveClauses_eq_exported]

/-- Kernel-checked derivation of the empty clause from the exported formula. -/
theorem exported_sat_fmla_proof :
    Sat.Fmla.proof exportedSatFormula Sat.Clause.nil := by
  rw [← diskSatFormula_eq_exported]
  exact disk_sat_fmla_proof

/-! ## Semantic bridge from Mathlib SAT valuations to signed DIMACS -/

/-- Interpret a DIMACS Boolean valuation as Mathlib's zero-based SAT valuation. -/
def satValuationOfDIMACS (τ : DIMACSValuation) : Sat.Valuation := fun n ↦
  if h : n < 153 then τ ⟨n + 1, by omega⟩ = true else False

@[simp]
theorem satValuationOfDIMACS_at (τ : DIMACSValuation) (i : DIMACSVar) :
    satValuationOfDIMACS τ (i.1 - 1) ↔ τ i = true := by
  unfold satValuationOfDIMACS
  have hi : i.1 - 1 < 153 := by omega
  simp only [dif_pos hi]
  have heq : (⟨(i.1 - 1) + 1, by omega⟩ : DIMACSVar) = i := by
    apply Subtype.ext
    change (i.1 - 1) + 1 = i.1
    omega
  rw [heq]

/-- Structured signed literals are parsed with the expected zero-based index. -/
@[simp]
theorem satLiteral_ofInt_toInt (l : DIMACSLiteral) :
    Sat.Literal.ofInt l.toInt =
      if l.positive then Sat.Literal.pos (l.var.1 - 1)
      else Sat.Literal.neg (l.var.1 - 1) := by
  rcases l with ⟨⟨i, hi⟩, positive⟩
  cases positive <;> simp [DIMACSLiteral.toInt, Sat.Literal.ofInt] <;> omega

/-- A true DIMACS literal is not falsified by the corresponding SAT valuation. -/
theorem satLiteral_not_falsified_of_holds (τ : DIMACSValuation)
    (l : DIMACSLiteral) (h : l.Holds τ) :
    ¬(satValuationOfDIMACS τ).neg (Sat.Literal.ofInt l.toInt) := by
  rcases l with ⟨i, positive⟩
  cases positive with
  | false =>
      change τ i = false at h
      rw [satLiteral_ofInt_toInt]
      simp only [Bool.false_eq_true, ↓reduceIte, Sat.Valuation.neg]
      rw [satValuationOfDIMACS_at]
      intro htrue
      rw [htrue] at h
      contradiction
  | true =>
      change τ i = true at h
      rw [satLiteral_ofInt_toInt]
      simp only [Bool.true_eq, ↓reduceIte, Sat.Valuation.neg]
      rw [satValuationOfDIMACS_at]
      exact fun hfalse ↦ hfalse h

/-- One non-falsified member suffices for Mathlib's continuation-style clause semantics. -/
theorem satClause_satisfied_of_mem {v : Sat.Valuation} {l : Sat.Literal}
    {c : List Sat.Literal} (hmem : l ∈ c) (hnot : ¬v.neg l) :
    v.satisfies c := by
  induction c with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      change v.neg head → v.satisfies tail
      intro hhead
      rcases hmem with rfl | htail
      · exact (hnot hhead).elim
      · exact ih htail

/-- Signed-DIMACS satisfaction transports to Mathlib's parsed SAT formula. -/
theorem signedDIMACSSatisfies_implies_sat (τ : DIMACSValuation)
    (h : SignedDIMACSSatisfies τ exportedDIMACSFormula) :
    (satValuationOfDIMACS τ).satisfies_fmla exportedSatFormula := by
  constructor
  intro satClause hsatClause
  unfold exportedSatFormula signedFormulaToSat at hsatClause
  obtain ⟨signedClause, hsignedClause, rfl⟩ := List.mem_map.mp hsatClause
  obtain ⟨z, hz, l, hlz, hholds⟩ := h signedClause hsignedClause
  subst z
  apply satClause_satisfied_of_mem (List.mem_map.mpr ⟨l.toInt, hz, rfl⟩)
  exact satLiteral_not_falsified_of_holds τ l hholds

/-- The kernel-checked LRAT refutation proves the signed exported formula UNSAT. -/
theorem exportedDIMACS_unsatisfiable_verified :
    SignedDIMACSUnsatisfiable exportedDIMACSFormula := by
  intro τ h
  exact exported_sat_fmla_proof (satValuationOfDIMACS τ)
    (signedDIMACSSatisfies_implies_sat τ h)

/-! ## Certified mathematical consequences -/

theorem coreCNF_unsat : Unsatisfiable coreCNF :=
  exportedDIMACS_unsat_implies_coreCNF_unsat
    exportedDIMACS_unsatisfiable_verified

theorem finite18_proved : Finite18 :=
  coreCNF_unsat_implies_finite18 coreCNF_unsat

theorem jsp000746_holdsFrom18 : HoldsFrom18 :=
  finite18_implies_holdsFrom18 finite18_proved

theorem jsp000746_positiveInfinite : PositiveInfiniteStatement :=
  finite18_implies_positiveInfiniteStatement finite18_proved

end JSP000746
