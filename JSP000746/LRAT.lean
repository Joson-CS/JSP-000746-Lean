import Mathlib.Tactic.Sat.FromLRAT
import JSP000746.DIMACS
import JSP000746.SATEncoding

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

/-- The exported integer clauses, converted exactly as Mathlib's DIMACS parser does. -/
def exportedSatFormula : Sat.Fmla :=
  exportedDIMACSFormula.map fun clause ↦ clause.map Sat.Literal.ofInt

end JSP000746
