import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# JSP-000746 — Core definitions

The vertices of the graph in the original problem are the positive integers
`{1, ..., n}`.  We represent this interval literally as a subtype of `ℕ`.

Mathlib's `SimpleGraph` is already undirected and loopless.  We use
`SimpleGraph.CliqueFree 3` for triangle-freeness and
`SimpleGraph.IsNIndepSet 3` for an independent set of exactly three vertices.
-/

namespace JSP000746

/-- The vertex set `{1, ..., n}`. -/
abbrev Vertex (n : ℕ) := Set.Icc (1 : ℕ) n

/-- The positive-integer label of a vertex. -/
abbrev vertexValue {n : ℕ} (v : Vertex n) : ℕ := v.1

/--
`a`, `b`, and `c` form an additive independent triple when `c = a + b` and
the finset `{a, b, c}` is an independent set of cardinality three.

The cardinality condition deliberately makes the three vertices distinct.
For positive `a` and `b`, `c = a + b` already forces `c ≠ a` and `c ≠ b`;
the remaining condition `a ≠ b` is supplied by `IsNIndepSet 3`.
-/
def IsAdditiveIndependentTriple {n : ℕ} (G : SimpleGraph (Vertex n))
    (a b c : Vertex n) : Prop :=
  vertexValue c = vertexValue a + vertexValue b ∧
    G.IsNIndepSet 3 {a, b, c}

/-- A graph contains an additive independent triple. -/
def HasAdditiveIndependentTriple {n : ℕ} (G : SimpleGraph (Vertex n)) : Prop :=
  ∃ a b c : Vertex n, IsAdditiveIndependentTriple G a b c

/-- The JSP-000746 conclusion for one fixed endpoint `n`. -/
def HoldsAt (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Vertex n),
    G.CliqueFree 3 → HasAdditiveIndependentTriple G

/--
The original eventual form of Erdős Problem 895: the conclusion holds for all
sufficiently large `n`.
-/
def EventuallyHolds : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HoldsAt n

/-- The stronger SAT-reported form: the conclusion holds for every `n ≥ 18`. -/
def HoldsFrom18 : Prop :=
  ∀ n : ℕ, 18 ≤ n → HoldsAt n

/-- The vertex set of all positive integers, for the infinite-title formulation. -/
abbrev PositiveVertex := Set.Ici (1 : ℕ)

/-- An additive independent triple in a graph on all positive integers. -/
def IsPositiveAdditiveIndependentTriple (G : SimpleGraph PositiveVertex)
    (a b c : PositiveVertex) : Prop :=
  (c : ℕ) = (a : ℕ) + (b : ℕ) ∧
    G.IsNIndepSet 3 {a, b, c}

/-- A graph on all positive integers contains an additive independent triple. -/
def HasPositiveAdditiveIndependentTriple (G : SimpleGraph PositiveVertex) : Prop :=
  ∃ a b c : PositiveVertex, IsPositiveAdditiveIndependentTriple G a b c

/-- The infinite positive-integer formulation used by the JSP-000746 title. -/
def PositiveInfiniteStatement : Prop :=
  ∀ G : SimpleGraph PositiveVertex,
    G.CliqueFree 3 → HasPositiveAdditiveIndependentTriple G

end JSP000746
