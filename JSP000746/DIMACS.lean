import JSP000746.SATEncoding

/-!
# JSP-000746 — Deterministic DIMACS export

This module gives the 153 edge variables stable one-based DIMACS indices,
constructs a deterministic ordered version of the 888-clause core CNF, and
proves that its propositional semantics agrees with `SATEncoding.coreCNF`.

No `Finset` traversal order is used for serialization.  All ordered data is
generated from `List.ofFn` and lexicographically nested list traversals.
-/

namespace JSP000746.DIMACS

open SATEncoding

/-- The positive DIMACS variable range `1..153`. -/
abbrev DIMACSVar := {i : ℕ // 1 ≤ i ∧ i ≤ 153}

/-- Vertex `i+1`, used to generate all lists in numerical order. -/
def vertexOfFin (i : Fin 18) : SATVertex :=
  ⟨i.1 + 1, by
    constructor
    · omega
    · have hi := i.2
      omega⟩

/-- The zero-based position of a vertex labelled in `1..18`. -/
def finOfVertex (v : SATVertex) : Fin 18 :=
  ⟨v.1 - 1, by
    have hv := v.2.2
    omega⟩

@[simp]
theorem vertexOfFin_finOfVertex (v : SATVertex) : vertexOfFin (finOfVertex v) = v := by
  apply Subtype.ext
  change (v.1 - 1) + 1 = v.1
  have hv := v.2.1
  omega

/-- The vertices `[1, 2, ..., 18]` in that exact order. -/
def orderedVertices : List SATVertex :=
  List.ofFn vertexOfFin

theorem vertex_mem_orderedVertices (v : SATVertex) : v ∈ orderedVertices := by
  rw [orderedVertices, List.mem_ofFn']
  exact ⟨finOfVertex v, vertexOfFin_finOfVertex v⟩

/-- All edge variables in endpoint lexicographic order. -/
def orderedEdges : List EdgeVar :=
  orderedVertices.flatMap fun u ↦
    orderedVertices.filterMap fun v ↦
      if h : u < v then some ⟨(u, v), h⟩ else none

/-- All triples `a < b < c` in endpoint lexicographic order. -/
def orderedTriangleIndices : List TriangleIndex :=
  orderedVertices.flatMap fun a ↦
    orderedVertices.flatMap fun b ↦
      orderedVertices.filterMap fun c ↦
        if h : a < b ∧ b < c then some ⟨(a, b, c), h⟩ else none

/-- All pairs `a < b`, `a+b ≤ 18` in endpoint lexicographic order. -/
def orderedAdditiveIndices : List AdditiveIndex :=
  orderedVertices.flatMap fun a ↦
    orderedVertices.filterMap fun b ↦
      if h : a < b ∧ vertexValue a + vertexValue b ≤ 18 then
        some ⟨(a, b), h⟩
      else none

set_option maxRecDepth 100000 in
theorem orderedEdges_length : orderedEdges.length = 153 := by decide

set_option maxRecDepth 100000 in
theorem orderedEdges_nodup : orderedEdges.Nodup := by decide

set_option maxRecDepth 100000 in
theorem orderedEdges_complete : orderedEdges.toFinset = Finset.univ := by decide

/-- Every edge occurs in the deterministic lexicographic list. -/
theorem edge_mem_orderedEdges (e : EdgeVar) : e ∈ orderedEdges := by
  have : e ∈ orderedEdges.toFinset := by rw [orderedEdges_complete]; simp
  simpa using this

/-- Identify the fixed length of `orderedEdges` with `Fin 153`. -/
def fin153EquivEdgePosition : Fin 153 ≃ Fin orderedEdges.length where
  toFun i := ⟨i.1, by simpa [orderedEdges_length] using i.2⟩
  invFun i := ⟨i.1, by simpa [orderedEdges_length] using i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Convert zero-based `Fin 153` positions to one-based DIMACS variables. -/
def fin153EquivDIMACSVar : Fin 153 ≃ DIMACSVar where
  toFun i := ⟨i.1 + 1, by omega⟩
  invFun i := ⟨i.1 - 1, by omega⟩
  left_inv i := by
    apply Fin.ext
    change (i.1 + 1) - 1 = i.1
    omega
  right_inv i := by
    apply Subtype.ext
    change (i.1 - 1) + 1 = i.1
    have hi := i.2.1
    omega

/-- The lexicographic list position is a bijection from `Fin 153` to edges. -/
def edgePositionEquiv : Fin 153 ≃ EdgeVar :=
  fin153EquivEdgePosition.trans
    (orderedEdges_nodup.getEquivOfForallMemList orderedEdges edge_mem_orderedEdges)

/-- The stable equivalence between edge variables and one-based DIMACS variables. -/
def edgeIndexEquiv : EdgeVar ≃ DIMACSVar :=
  edgePositionEquiv.symm.trans fin153EquivDIMACSVar

/-- The stable one-based DIMACS index of an edge. -/
def edgeToVar (e : EdgeVar) : DIMACSVar := edgeIndexEquiv e

/-- The stable one-based DIMACS index as a natural number. -/
def edgeToIndex (e : EdgeVar) : ℕ := (edgeToVar e).1

/-- Reverse the stable DIMACS numbering. -/
def indexToEdge (i : DIMACSVar) : EdgeVar := edgeIndexEquiv.symm i

@[simp]
theorem indexToEdge_edgeToVar (e : EdgeVar) : indexToEdge (edgeToVar e) = e :=
  edgeIndexEquiv.symm_apply_apply e

@[simp]
theorem edgeToVar_indexToEdge (i : DIMACSVar) : edgeToVar (indexToEdge i) = i :=
  edgeIndexEquiv.apply_symm_apply i

theorem edgeToIndex_bounds (e : EdgeVar) :
    1 ≤ edgeToIndex e ∧ edgeToIndex e ≤ 153 :=
  (edgeToVar e).2

theorem edgeToIndex_injective : Function.Injective edgeToIndex := by
  intro e f h
  apply edgeIndexEquiv.injective
  exact Subtype.ext h

theorem edgeToIndex_covers (i : DIMACSVar) :
    edgeToIndex (indexToEdge i) = i.1 := by
  exact congrArg Subtype.val (edgeToVar_indexToEdge i)

set_option maxRecDepth 100000 in
theorem orderedEdges_indices :
    orderedEdges.map edgeToIndex = (List.range 153).map (· + 1) := by decide

set_option maxRecDepth 100000 in
theorem orderedTriangleIndices_length : orderedTriangleIndices.length = 816 := by decide

theorem triangleIndex_mem_ordered (t : TriangleIndex) : t ∈ orderedTriangleIndices := by
  rw [orderedTriangleIndices, List.mem_flatMap]
  refine ⟨t.1.1, vertex_mem_orderedVertices _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨t.1.2.1, vertex_mem_orderedVertices _, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨t.1.2.2, vertex_mem_orderedVertices _, ?_⟩
  simp [t.2]

theorem orderedTriangleIndices_complete :
    orderedTriangleIndices.toFinset = Finset.univ := by
  ext t
  simp [triangleIndex_mem_ordered]

theorem orderedTriangleIndices_nodup : orderedTriangleIndices.Nodup := by
  apply Multiset.coe_nodup.mp
  apply (Multiset.toFinset_card_eq_card_iff_nodup).mp
  change orderedTriangleIndices.toFinset.card = orderedTriangleIndices.length
  rw [orderedTriangleIndices_complete, Finset.card_univ, triangleIndex_count,
    orderedTriangleIndices_length]

set_option maxRecDepth 100000 in
theorem orderedAdditiveIndices_length : orderedAdditiveIndices.length = 72 := by decide

theorem additiveIndex_mem_ordered (t : AdditiveIndex) : t ∈ orderedAdditiveIndices := by
  rw [orderedAdditiveIndices, List.mem_flatMap]
  refine ⟨t.1.1, vertex_mem_orderedVertices _, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨t.1.2, vertex_mem_orderedVertices _, ?_⟩
  simp [t.2]

theorem orderedAdditiveIndices_complete :
    orderedAdditiveIndices.toFinset = Finset.univ := by
  ext t
  simp [additiveIndex_mem_ordered]

theorem orderedAdditiveIndices_nodup : orderedAdditiveIndices.Nodup := by
  apply Multiset.coe_nodup.mp
  apply (Multiset.toFinset_card_eq_card_iff_nodup).mp
  change orderedAdditiveIndices.toFinset.card = orderedAdditiveIndices.length
  rw [orderedAdditiveIndices_complete, Finset.card_univ, additiveIndex_count,
    orderedAdditiveIndices_length]

/-- The 816 triangle-free clauses, followed by the 72 additive clauses. -/
def orderedCoreCNF : List Clause :=
  orderedTriangleIndices.map triangleClause ++
    orderedAdditiveIndices.map additiveClause

theorem orderedCoreCNF_length : orderedCoreCNF.length = 888 := by
  simp [orderedCoreCNF, orderedTriangleIndices_length, orderedAdditiveIndices_length]

/-- List-based satisfaction, used before converting literals to DIMACS form. -/
def SatisfiesOrdered (σ : Assignment) (cnf : List Clause) : Prop :=
  ∀ clause ∈ cnf, ClauseSatisfied σ clause

theorem orderedCoreCNF_toFinset : orderedCoreCNF.toFinset = coreCNF := by
  ext clause
  simp [orderedCoreCNF, coreCNF, triangleFreeClauses, additiveTripleClauses,
    triangleIndex_mem_ordered, additiveIndex_mem_ordered]

theorem satisfies_orderedCoreCNF_iff_coreCNF (σ : Assignment) :
    SatisfiesOrdered σ orderedCoreCNF ↔ Satisfies σ coreCNF := by
  rw [← orderedCoreCNF_toFinset]
  simp only [SatisfiesOrdered, Satisfies, List.mem_toFinset]

/-! ## DIMACS literals and their semantics -/

/-- A DIMACS literal before serialization: a one-based variable and a sign. -/
structure DIMACSLiteral where
  var : DIMACSVar
  positive : Bool
deriving DecidableEq

/-- Positive literals serialize as `+index`; negative literals as `-index`. -/
def DIMACSLiteral.toInt (l : DIMACSLiteral) : Int :=
  if l.positive then Int.ofNat l.var.1 else -Int.ofNat l.var.1

theorem DIMACSLiteral.toInt_ne_zero (l : DIMACSLiteral) : l.toInt ≠ 0 := by
  rcases l with ⟨⟨i, hi⟩, positive⟩
  cases positive <;> simp [DIMACSLiteral.toInt] <;> omega

theorem DIMACSLiteral.toInt_abs (l : DIMACSLiteral) :
    l.toInt.natAbs = l.var.1 := by
  rcases l with ⟨⟨i, hi⟩, positive⟩
  cases positive <;> simp [DIMACSLiteral.toInt]

theorem DIMACSLiteral.toInt_abs_bounds (l : DIMACSLiteral) :
    1 ≤ l.toInt.natAbs ∧ l.toInt.natAbs ≤ 153 := by
  rw [l.toInt_abs]
  exact l.var.2

/-- Convert one SAT-level literal to its deterministically numbered DIMACS literal. -/
def literalToDIMACS (l : Literal) : DIMACSLiteral :=
  ⟨edgeToVar l.edge, l.positive⟩

abbrev DIMACSValuation := DIMACSVar → Bool
abbrev DIMACSClause := List DIMACSLiteral
abbrev DIMACSFormula := List DIMACSClause

/-- Transport an edge assignment across the proved edge/index bijection. -/
def assignmentToDIMACS (σ : Assignment) : DIMACSValuation :=
  fun i ↦ σ (indexToEdge i)

/-- Transport a DIMACS valuation back to an edge assignment. -/
def dimacsToAssignment (τ : DIMACSValuation) : Assignment :=
  fun e ↦ τ (edgeToVar e)

@[simp]
theorem assignmentToDIMACS_edgeToVar (σ : Assignment) (e : EdgeVar) :
    assignmentToDIMACS σ (edgeToVar e) = σ e := by
  simp [assignmentToDIMACS]

@[simp]
theorem dimacsToAssignment_indexToEdge (τ : DIMACSValuation) (i : DIMACSVar) :
    dimacsToAssignment τ (indexToEdge i) = τ i := by
  simp [dimacsToAssignment]

theorem assignmentToDIMACS_dimacsToAssignment (τ : DIMACSValuation) :
    assignmentToDIMACS (dimacsToAssignment τ) = τ := by
  funext i
  simp [assignmentToDIMACS]

theorem dimacsToAssignment_assignmentToDIMACS (σ : Assignment) :
    dimacsToAssignment (assignmentToDIMACS σ) = σ := by
  funext e
  simp [dimacsToAssignment]

def DIMACSLiteral.Holds (τ : DIMACSValuation) (l : DIMACSLiteral) : Prop :=
  τ l.var = l.positive

def DIMACSClauseSatisfied (τ : DIMACSValuation) (clause : DIMACSClause) : Prop :=
  ∃ l ∈ clause, l.Holds τ

def DIMACSSatisfies (τ : DIMACSValuation) (formula : DIMACSFormula) : Prop :=
  ∀ clause ∈ formula, DIMACSClauseSatisfied τ clause

/-- The structured DIMACS formula in the exact order that will be serialized. -/
def encodedDIMACSFormula : DIMACSFormula :=
  orderedCoreCNF.map fun clause ↦ clause.map literalToDIMACS

theorem literal_holds_toDIMACS (σ : Assignment) (l : Literal) :
    (literalToDIMACS l).Holds (assignmentToDIMACS σ) ↔ l.Holds σ := by
  simp [DIMACSLiteral.Holds, Literal.Holds, literalToDIMACS]

theorem clause_satisfied_toDIMACS (σ : Assignment) (clause : Clause) :
    DIMACSClauseSatisfied (assignmentToDIMACS σ) (clause.map literalToDIMACS) ↔
      ClauseSatisfied σ clause := by
  simp only [DIMACSClauseSatisfied, ClauseSatisfied, List.mem_map]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hholds⟩
    exact ⟨l, hl, (literal_holds_toDIMACS σ l).mp hholds⟩
  · rintro ⟨l, hl, hholds⟩
    exact ⟨literalToDIMACS l, ⟨l, hl, rfl⟩,
      (literal_holds_toDIMACS σ l).mpr hholds⟩

/-- Assignment semantics is preserved by the edge-index bijection. -/
theorem satisfies_orderedCoreCNF_iff_encodedDIMACS (σ : Assignment) :
    SatisfiesOrdered σ orderedCoreCNF ↔
      DIMACSSatisfies (assignmentToDIMACS σ) encodedDIMACSFormula := by
  constructor
  · intro h clause hclause
    rw [encodedDIMACSFormula, List.mem_map] at hclause
    obtain ⟨source, hsource, rfl⟩ := hclause
    exact (clause_satisfied_toDIMACS σ source).mpr (h source hsource)
  · intro h source hsource
    apply (clause_satisfied_toDIMACS σ source).mp
    exact h _ (by
      rw [encodedDIMACSFormula]
      exact List.mem_map.mpr ⟨source, hsource, rfl⟩)

/-! ## Signed integer DIMACS representation -/

abbrev SignedDIMACSClause := List Int
abbrev SignedDIMACSFormula := List SignedDIMACSClause

/-- The exact signed-integer formula written after the DIMACS header. -/
def exportedDIMACSFormula : SignedDIMACSFormula :=
  encodedDIMACSFormula.map fun clause ↦ clause.map DIMACSLiteral.toInt

theorem encodedDIMACSFormula_length : encodedDIMACSFormula.length = 888 := by
  simp [encodedDIMACSFormula, orderedCoreCNF_length]

theorem exportedDIMACSFormula_length : exportedDIMACSFormula.length = 888 := by
  simp [exportedDIMACSFormula, encodedDIMACSFormula_length]

/-- Semantics of a signed DIMACS integer, via its unique structured literal. -/
def SignedLiteralHolds (τ : DIMACSValuation) (z : Int) : Prop :=
  ∃ l : DIMACSLiteral, l.toInt = z ∧ l.Holds τ

def SignedDIMACSClauseSatisfied (τ : DIMACSValuation)
    (clause : SignedDIMACSClause) : Prop :=
  ∃ z ∈ clause, SignedLiteralHolds τ z

def SignedDIMACSSatisfies (τ : DIMACSValuation)
    (formula : SignedDIMACSFormula) : Prop :=
  ∀ clause ∈ formula, SignedDIMACSClauseSatisfied τ clause

def SignedDIMACSUnsatisfiable (formula : SignedDIMACSFormula) : Prop :=
  ∀ τ : DIMACSValuation, ¬SignedDIMACSSatisfies τ formula

theorem DIMACSLiteral.toInt_injective : Function.Injective DIMACSLiteral.toInt := by
  rintro ⟨⟨i, hi⟩, pi⟩ ⟨⟨j, hj⟩, pj⟩ h
  have hij : i = j := by
    have habs := congrArg Int.natAbs h
    simpa only [DIMACSLiteral.toInt_abs] using habs
  subst j
  cases pi <;> cases pj
  · rfl
  · simp only [DIMACSLiteral.toInt, Bool.false_eq_true, ↓reduceIte,
      Bool.true_eq] at h
    have hz : Int.ofNat i = 0 := by omega
    have : i = 0 := by simpa using hz
    exfalso
    omega
  · simp only [DIMACSLiteral.toInt, Bool.true_eq, ↓reduceIte,
      Bool.false_eq_true] at h
    have hz : Int.ofNat i = 0 := by omega
    have : i = 0 := by simpa using hz
    exfalso
    omega
  · rfl

theorem signed_clause_semantics (τ : DIMACSValuation) (clause : DIMACSClause) :
    SignedDIMACSClauseSatisfied τ (clause.map DIMACSLiteral.toInt) ↔
      DIMACSClauseSatisfied τ clause := by
  constructor
  · rintro ⟨z, hz, k, hk, hholds⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hz
    have : k = l := DIMACSLiteral.toInt_injective hk
    subst k
    exact ⟨l, hl, hholds⟩
  · rintro ⟨l, hl, hholds⟩
    exact ⟨l.toInt, List.mem_map.mpr ⟨l, hl, rfl⟩, l, rfl, hholds⟩

theorem encoded_iff_exported (τ : DIMACSValuation) :
    DIMACSSatisfies τ encodedDIMACSFormula ↔
      SignedDIMACSSatisfies τ exportedDIMACSFormula := by
  constructor
  · intro h clause hclause
    rw [exportedDIMACSFormula, List.mem_map] at hclause
    obtain ⟨source, hsource, rfl⟩ := hclause
    exact (signed_clause_semantics τ source).mpr (h source hsource)
  · intro h source hsource
    apply (signed_clause_semantics τ source).mp
    exact h _ (by
      rw [exportedDIMACSFormula]
      exact List.mem_map.mpr ⟨source, hsource, rfl⟩)

/--
The end-to-end semantic bridge from the ordered SAT clauses to the signed
integers that are serialized in `certificates/core.cnf`.
-/
theorem satisfies_orderedCoreCNF_iff_exportedDIMACS (σ : Assignment) :
    SatisfiesOrdered σ orderedCoreCNF ↔
      SignedDIMACSSatisfies (assignmentToDIMACS σ) exportedDIMACSFormula :=
  (satisfies_orderedCoreCNF_iff_encodedDIMACS σ).trans
    (encoded_iff_exported (assignmentToDIMACS σ))

/-- A future UNSAT proof about the exported DIMACS formula implies core UNSAT. -/
theorem exportedDIMACS_unsat_implies_coreCNF_unsat
    (hunsat : SignedDIMACSUnsatisfiable exportedDIMACSFormula) :
    Unsatisfiable coreCNF := by
  intro σ hcore
  apply hunsat (assignmentToDIMACS σ)
  exact (satisfies_orderedCoreCNF_iff_exportedDIMACS σ).mp
    ((satisfies_orderedCoreCNF_iff_coreCNF σ).mpr hcore)

/-- In fact the exported signed formula and `coreCNF` are equisatisfiable. -/
theorem coreCNF_unsat_iff_exportedDIMACS_unsat :
    Unsatisfiable coreCNF ↔ SignedDIMACSUnsatisfiable exportedDIMACSFormula := by
  constructor
  · intro hcore τ hexported
    let σ := dimacsToAssignment τ
    have htransport : assignmentToDIMACS σ = τ :=
      assignmentToDIMACS_dimacsToAssignment τ
    have hordered : SatisfiesOrdered σ orderedCoreCNF :=
      (satisfies_orderedCoreCNF_iff_exportedDIMACS σ).mpr (by
        simpa [htransport] using hexported)
    exact hcore σ ((satisfies_orderedCoreCNF_iff_coreCNF σ).mp hordered)
  · exact exportedDIMACS_unsat_implies_coreCNF_unsat

/-! ## Deterministic renderer -/

def renderSignedClause (clause : SignedDIMACSClause) : String :=
  String.intercalate " " (clause.map toString) ++ " 0\n"

/-- Exact contents of `certificates/core.cnf`. -/
def renderCoreDIMACS : String :=
  "p cnf 153 888\n" ++ String.join (exportedDIMACSFormula.map renderSignedClause)

end JSP000746.DIMACS
