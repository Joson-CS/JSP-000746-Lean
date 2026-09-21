import JSP000746.Definitions
import JSP000746.Finite18

/-!
# JSP-000746 — Reduction

The graph on `{1, ..., n}` is pulled back along the inclusion
`{1, ..., 18} ↪ {1, ..., n}`.  This is exactly the restriction to the first
18 positive-integer vertices.  Mathlib's `SimpleGraph.induce` is itself a
wrapper around the same `SimpleGraph.comap` operation.
-/

namespace JSP000746

/-- Inclusion of the first `m` positive integers into the first `n`. -/
def initialSegmentEmbedding {m n : ℕ} (h : m ≤ n) : Vertex m ↪ Vertex n where
  toFun v := ⟨v.1, v.2.1, v.2.2.trans h⟩
  inj' := by
    intro a b hab
    exact Subtype.ext (congrArg (fun v : Vertex n ↦ v.1) hab)

@[simp]
theorem initialSegmentEmbedding_value {m n : ℕ} (h : m ≤ n) (v : Vertex m) :
    vertexValue (initialSegmentEmbedding h v) = vertexValue v :=
  rfl

/-- Restrict a graph on `{1, ..., n}` to its first `m` vertices. -/
abbrev restrictToInitialSegment {m n : ℕ} (G : SimpleGraph (Vertex n)) (h : m ≤ n) :
    SimpleGraph (Vertex m) :=
  G.comap (initialSegmentEmbedding h)

/-- Inclusion of a finite positive interval into all positive integers. -/
def initialSegmentToPositiveEmbedding {n : ℕ} : Vertex n ↪ PositiveVertex where
  toFun v := ⟨v.1, v.2.1⟩
  inj' := by
    intro a b hab
    exact Subtype.ext (congrArg (fun v : PositiveVertex ↦ v.1) hab)

@[simp]
theorem initialSegmentToPositiveEmbedding_value {n : ℕ} (v : Vertex n) :
    (initialSegmentToPositiveEmbedding v : ℕ) = vertexValue v :=
  rfl

/-- An independent finset in a comapped graph remains independent after mapping it. -/
theorem map_isNIndepSet_of_comap {α β : Type*} {G : SimpleGraph β}
    (e : α ↪ β) {k : ℕ} {s : Finset α} (h : (G.comap e).IsNIndepSet k s) :
    G.IsNIndepSet k (s.map e) := by
  constructor
  · rw [SimpleGraph.isIndepSet_iff, Finset.coe_map]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    change ¬(G.comap e).Adj x y
    exact h.isIndepSet hx hy (fun hxy' ↦ hxy (congrArg e hxy'))
  · simpa only [Finset.card_map] using h.card_eq

/--
The genuine reduction: the finite 18-vertex proposition implies the claimed
result for every `n ≥ 18`.
-/
theorem finite18_implies_holdsFrom18
    (h18 : ∀ G : SimpleGraph (Vertex 18),
      G.CliqueFree 3 → HasAdditiveIndependentTriple G) :
    ∀ n : ℕ, 18 ≤ n →
      ∀ G : SimpleGraph (Vertex n),
        G.CliqueFree 3 → HasAdditiveIndependentTriple G := by
  intro n hn G htriangle
  let e : Vertex 18 ↪ Vertex n := initialSegmentEmbedding hn
  let G18 : SimpleGraph (Vertex 18) := G.comap e
  have htriangle18 : G18.CliqueFree 3 := by
    exact htriangle.comap (SimpleGraph.Embedding.comap e G).isContained
  obtain ⟨a, b, c, hadd, hind⟩ := h18 G18 htriangle18
  refine ⟨e a, e b, e c, ?_, ?_⟩
  · simpa [e] using hadd
  · let s : Finset (Vertex 18) := {a, b, c}
    have hs : (G.comap e).IsNIndepSet 3 s := by
      simpa [G18, s] using hind
    have hmap : G.IsNIndepSet 3 (s.map e) := by
      constructor
      · rw [SimpleGraph.isIndepSet_iff, Finset.coe_map]
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
        change ¬(G.comap e).Adj x y
        exact hs.isIndepSet hx hy (fun h ↦ hxy (congrArg e h))
      · simpa only [Finset.card_map] using hs.card_eq
    simpa [s] using hmap

/-- The `n ≥ 18` statement implies the original "all sufficiently large `n`" statement. -/
theorem holdsFrom18_implies_eventuallyHolds (h : HoldsFrom18) : EventuallyHolds :=
  ⟨18, h⟩

/-- The finite core also implies the original eventual formulation. -/
theorem finite18_implies_eventuallyHolds (h18 : Finite18) : EventuallyHolds :=
  holdsFrom18_implies_eventuallyHolds (finite18_implies_holdsFrom18 h18)

/--
The finite 18-vertex core implies the infinite formulation on all positive
integers by restriction to the first 18 vertices.
-/
theorem finite18_implies_positiveInfiniteStatement (h18 : Finite18) :
    PositiveInfiniteStatement := by
  intro G htriangle
  let e : Vertex 18 ↪ PositiveVertex := initialSegmentToPositiveEmbedding
  let G18 : SimpleGraph (Vertex 18) := G.comap e
  have htriangle18 : G18.CliqueFree 3 := by
    exact htriangle.comap (SimpleGraph.Embedding.comap e G).isContained
  obtain ⟨a, b, c, hadd, hind⟩ := h18 G18 htriangle18
  refine ⟨e a, e b, e c, ?_, ?_⟩
  · simpa [e] using hadd
  · let s : Finset (Vertex 18) := {a, b, c}
    have hs : (G.comap e).IsNIndepSet 3 s := by
      simpa [G18, s] using hind
    have hmap : G.IsNIndepSet 3 (s.map e) :=
      map_isNIndepSet_of_comap e hs
    simpa [s] using hmap

end JSP000746
