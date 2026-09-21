import JSP000746.Definitions

/-!
# JSP-000746 — Finite case n = 18

This file records the finite core as a proposition.  It is intentionally not
declared as a proved theorem at this stage: proving it is the later finite
SAT/certificate task.
-/

namespace JSP000746

/--
The finite 18-vertex core of JSP-000746.

Every triangle-free simple graph on the positive integers `{1, ..., 18}`
contains three distinct pairwise nonadjacent vertices `a`, `b`, and `c` with
`c = a + b`.
-/
def Finite18 : Prop :=
  ∀ G : SimpleGraph (Vertex 18),
    G.CliqueFree 3 → HasAdditiveIndependentTriple G

end JSP000746
