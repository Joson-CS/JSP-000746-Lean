import JSP000746.Finite18

/-!
# JSP-000746 — Finite Boolean/SAT encoding for `n = 18`

This file defines only the small, independent Boolean encoding.  It does not
invoke a SAT solver and does not contain or generate a proof certificate.

An unordered edge `{u, v}` is represented canonically by a pair with `u < v`.
Triangle indices likewise use `a < b < c`.  Additive indices use `a < b` and
`a + b ≤ 18`, so swapping `a` and `b` creates no duplicate.
-/

namespace JSP000746.SATEncoding

/-- The fixed SAT-level vertex type. -/
abbrev SATVertex := Vertex 18

/-- A potential undirected edge, represented once by its increasing endpoints. -/
abbrev EdgeVar := {p : SATVertex × SATVertex // p.1 < p.2}

/-- An unordered triple of distinct vertices, represented in increasing order. -/
abbrev TriangleIndex :=
  {p : SATVertex × SATVertex × SATVertex // p.1 < p.2.1 ∧ p.2.1 < p.2.2}

/--
A distinct additive triple index.  The increasing condition removes the
`(a,b)`/`(b,a)` duplication; its third vertex is determined as `a + b`.
-/
abbrev AdditiveIndex :=
  {p : SATVertex × SATVertex //
    p.1 < p.2 ∧ vertexValue p.1 + vertexValue p.2 ≤ 18}

/-- A Boolean truth assignment to the 153 possible undirected edges. -/
abbrev Assignment := EdgeVar → Bool

/-- A signed edge literal; `positive = true` means that the edge is present. -/
structure Literal where
  edge : EdgeVar
  positive : Bool
deriving DecidableEq

/-- A disjunctive clause and a conjunctive normal form. -/
abbrev Clause := List Literal
abbrev CNF := Finset Clause

/-- Propositional semantics of a literal under a Boolean assignment. -/
def Literal.Holds (σ : Assignment) (l : Literal) : Prop :=
  σ l.edge = l.positive

/-- At least one literal in the clause holds. -/
def ClauseSatisfied (σ : Assignment) (clause : Clause) : Prop :=
  ∃ l ∈ clause, l.Holds σ

/-- Every clause in a CNF is satisfied. -/
def Satisfies (σ : Assignment) (cnf : CNF) : Prop :=
  ∀ clause ∈ cnf, ClauseSatisfied σ clause

/-- A CNF has no Boolean satisfying assignment. -/
def Unsatisfiable (cnf : CNF) : Prop :=
  ∀ σ : Assignment, ¬Satisfies σ cnf

private abbrev triangleA (t : TriangleIndex) : SATVertex := t.1.1
private abbrev triangleB (t : TriangleIndex) : SATVertex := t.1.2.1
private abbrev triangleC (t : TriangleIndex) : SATVertex := t.1.2.2

private def triangleAB (t : TriangleIndex) : EdgeVar :=
  ⟨(triangleA t, triangleB t), t.2.1⟩

private def triangleAC (t : TriangleIndex) : EdgeVar :=
  ⟨(triangleA t, triangleC t), t.2.1.trans t.2.2⟩

private def triangleBC (t : TriangleIndex) : EdgeVar :=
  ⟨(triangleB t, triangleC t), t.2.2⟩

@[simp] theorem triangleAB_left_value (t : TriangleIndex) :
    (triangleAB t).1.1.1 = t.1.1.1 := rfl

@[simp] theorem triangleAB_right_value (t : TriangleIndex) :
    (triangleAB t).1.2.1 = t.1.2.1.1 := rfl

@[simp] theorem triangleAC_left_value (t : TriangleIndex) :
    (triangleAC t).1.1.1 = t.1.1.1 := rfl

@[simp] theorem triangleAC_right_value (t : TriangleIndex) :
    (triangleAC t).1.2.1 = t.1.2.2.1 := rfl

@[simp] theorem triangleBC_left_value (t : TriangleIndex) :
    (triangleBC t).1.1.1 = t.1.2.1.1 := rfl

@[simp] theorem triangleBC_right_value (t : TriangleIndex) :
    (triangleBC t).1.2.1 = t.1.2.2.1 := rfl

/-- The clause `¬ab ∨ ¬ac ∨ ¬bc` forbidding one triangle. -/
def triangleClause (t : TriangleIndex) : Clause :=
  [⟨triangleAB t, false⟩, ⟨triangleAC t, false⟩, ⟨triangleBC t, false⟩]

private abbrev additiveA (t : AdditiveIndex) : SATVertex := t.1.1
private abbrev additiveB (t : AdditiveIndex) : SATVertex := t.1.2

/-- The vertex labelled `a + b` for an additive index. -/
def additiveSum (t : AdditiveIndex) : SATVertex :=
  ⟨(additiveA t).1 + (additiveB t).1, by
    constructor
    · change 1 ≤ (additiveA t).1 + (additiveB t).1
      have ha := (additiveA t).2.1
      omega
    · change (additiveA t).1 + (additiveB t).1 ≤ 18
      exact t.2.2⟩

@[simp]
theorem additiveSum_value (t : AdditiveIndex) :
    vertexValue (additiveSum t) =
      vertexValue (additiveA t) + vertexValue (additiveB t) :=
  rfl

private theorem additiveA_lt_sum (t : AdditiveIndex) : additiveA t < additiveSum t := by
  change (additiveA t).1 < (additiveA t).1 + (additiveB t).1
  have hb := (additiveB t).2.1
  omega

private theorem additiveB_lt_sum (t : AdditiveIndex) : additiveB t < additiveSum t := by
  change (additiveB t).1 < (additiveA t).1 + (additiveB t).1
  have ha := (additiveA t).2.1
  omega

private def additiveAB (t : AdditiveIndex) : EdgeVar :=
  ⟨(additiveA t, additiveB t), t.2.1⟩

private def additiveASum (t : AdditiveIndex) : EdgeVar :=
  ⟨(additiveA t, additiveSum t), additiveA_lt_sum t⟩

private def additiveBSum (t : AdditiveIndex) : EdgeVar :=
  ⟨(additiveB t, additiveSum t), additiveB_lt_sum t⟩

@[simp] theorem additiveAB_left_value (t : AdditiveIndex) :
    (additiveAB t).1.1.1 = t.1.1.1 := rfl

@[simp] theorem additiveAB_right_value (t : AdditiveIndex) :
    (additiveAB t).1.2.1 = t.1.2.1 := rfl

@[simp] theorem additiveASum_left_value (t : AdditiveIndex) :
    (additiveASum t).1.1.1 = t.1.1.1 := rfl

@[simp] theorem additiveASum_right_value (t : AdditiveIndex) :
    (additiveASum t).1.2.1 = t.1.1.1 + t.1.2.1 := rfl

@[simp] theorem additiveBSum_left_value (t : AdditiveIndex) :
    (additiveBSum t).1.1.1 = t.1.2.1 := rfl

@[simp] theorem additiveBSum_right_value (t : AdditiveIndex) :
    (additiveBSum t).1.2.1 = t.1.1.1 + t.1.2.1 := rfl

/--
The clause `ab ∨ a(a+b) ∨ b(a+b)`: at least one edge must be present, so the
additive triple is not independent.
-/
def additiveClause (t : AdditiveIndex) : Clause :=
  [⟨additiveAB t, true⟩, ⟨additiveASum t, true⟩, ⟨additiveBSum t, true⟩]

/-- The actual deduplicated finset of additive vertex triples. -/
def additiveTriples : Finset (Finset SATVertex) :=
  Finset.univ.image fun t : AdditiveIndex ↦
    {additiveA t, additiveB t, additiveSum t}

/-- All triangle-free clauses. -/
def triangleFreeClauses : CNF :=
  (Finset.univ : Finset TriangleIndex).image triangleClause

/-- All clauses excluding independent additive triples. -/
def additiveTripleClauses : CNF :=
  (Finset.univ : Finset AdditiveIndex).image additiveClause

/-- The complete core CNF: triangle-free plus no independent additive triple. -/
def coreCNF : CNF :=
  triangleFreeClauses ∪ additiveTripleClauses

private theorem triangleClause_injective : Function.Injective triangleClause := by
  intro t u h
  have hAB : triangleAB t = triangleAB u := by
    have hh := congrArg (fun xs : List Literal ↦ xs.head?.map Literal.edge) h
    simpa [triangleClause] using hh
  have hBC : triangleBC t = triangleBC u := by
    have hh := congrArg (fun xs : List Literal ↦ (xs.drop 2).head?.map Literal.edge) h
    simpa [triangleClause] using hh
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun e : EdgeVar ↦ e.1.1) hAB
  · apply Prod.ext
    · exact congrArg (fun e : EdgeVar ↦ e.1.2) hAB
    · exact congrArg (fun e : EdgeVar ↦ e.1.2) hBC

private theorem clauseFamilies_disjoint :
    Disjoint triangleFreeClauses additiveTripleClauses := by
  rw [Finset.disjoint_left]
  intro clause htriangle hadditive
  rw [triangleFreeClauses, Finset.mem_image] at htriangle
  rw [additiveTripleClauses, Finset.mem_image] at hadditive
  obtain ⟨t, -, rfl⟩ := htriangle
  obtain ⟨u, -, h⟩ := hadditive
  simp [triangleClause, additiveClause] at h

/-! The following are kernel-reduced finite sanity checks, not comments. -/

set_option maxRecDepth 100000 in
theorem edgeVar_count : Fintype.card EdgeVar = 153 := by decide

set_option maxRecDepth 100000 in
theorem triangleIndex_count : Fintype.card TriangleIndex = 816 := by decide

set_option maxRecDepth 100000 in
theorem additiveIndex_count : Fintype.card AdditiveIndex = 72 := by decide

set_option maxRecDepth 100000 in
theorem additiveTriples_count : additiveTriples.card = 72 := by decide

theorem triangleFreeClauses_count : triangleFreeClauses.card = 816 := by
  rw [triangleFreeClauses, Finset.card_image_of_injective _ triangleClause_injective,
    Finset.card_univ, triangleIndex_count]

set_option maxRecDepth 100000 in
theorem additiveTripleClauses_count : additiveTripleClauses.card = 72 := by decide

theorem coreCNF_count : coreCNF.card = 888 := by
  rw [coreCNF, Finset.card_union_of_disjoint clauseFamilies_disjoint,
    triangleFreeClauses_count, additiveTripleClauses_count]

/-! ## Correctness bridge to the mathematical `Finite18` proposition -/

/-- The two clause families give exactly the semantics of the core CNF. -/
theorem satisfies_core_iff (σ : Assignment) :
    Satisfies σ coreCNF ↔
      (∀ t : TriangleIndex, ClauseSatisfied σ (triangleClause t)) ∧
      (∀ t : AdditiveIndex, ClauseSatisfied σ (additiveClause t)) := by
  constructor
  · intro h
    constructor
    · intro t
      exact h _ (by simp [coreCNF, triangleFreeClauses])
    · intro t
      exact h _ (by simp [coreCNF, additiveTripleClauses])
  · rintro ⟨htriangle, hadditive⟩ clause hclause
    rw [coreCNF, Finset.mem_union] at hclause
    rcases hclause with hclause | hclause
    · rw [triangleFreeClauses, Finset.mem_image] at hclause
      obtain ⟨t, -, rfl⟩ := hclause
      exact htriangle t
    · rw [additiveTripleClauses, Finset.mem_image] at hclause
      obtain ⟨t, -, rfl⟩ := hclause
      exact hadditive t

/-- Encode a mathematical graph by the truth values of its canonical edge variables. -/
noncomputable def assignmentOfGraph (G : SimpleGraph SATVertex) : Assignment := by
  classical
  exact fun e ↦ decide (G.Adj e.1.1 e.1.2)

@[simp]
theorem assignmentOfGraph_eq_true_iff (G : SimpleGraph SATVertex) (e : EdgeVar) :
    assignmentOfGraph G e = true ↔ G.Adj e.1.1 e.1.2 := by
  classical
  simp [assignmentOfGraph]

@[simp]
theorem assignmentOfGraph_eq_false_iff (G : SimpleGraph SATVertex) (e : EdgeVar) :
    assignmentOfGraph G e = false ↔ ¬G.Adj e.1.1 e.1.2 := by
  classical
  simp [assignmentOfGraph]

private theorem assignmentOfGraph_satisfies_triangleClause
    (G : SimpleGraph SATVertex) (htriangle : G.CliqueFree 3) (t : TriangleIndex) :
    ClauseSatisfied (assignmentOfGraph G) (triangleClause t) := by
  classical
  by_cases hab : G.Adj (triangleA t) (triangleB t)
  · by_cases hac : G.Adj (triangleA t) (triangleC t)
    · have hbc : ¬G.Adj (triangleB t) (triangleC t) := by
        intro hbc
        exact htriangle _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
      refine ⟨⟨triangleBC t, false⟩, by simp [triangleClause], ?_⟩
      change assignmentOfGraph G (triangleBC t) = false
      rw [assignmentOfGraph_eq_false_iff]
      simpa [triangleBC] using hbc
    · refine ⟨⟨triangleAC t, false⟩, by simp [triangleClause], ?_⟩
      change assignmentOfGraph G (triangleAC t) = false
      rw [assignmentOfGraph_eq_false_iff]
      simpa [triangleAC] using hac
  · refine ⟨⟨triangleAB t, false⟩, by simp [triangleClause], ?_⟩
    change assignmentOfGraph G (triangleAB t) = false
    rw [assignmentOfGraph_eq_false_iff]
    simpa [triangleAB] using hab

private theorem assignmentOfGraph_satisfies_additiveClause
    (G : SimpleGraph SATVertex) (hno : ¬HasAdditiveIndependentTriple G)
    (t : AdditiveIndex) :
    ClauseSatisfied (assignmentOfGraph G) (additiveClause t) := by
  classical
  by_cases hab : G.Adj (additiveA t) (additiveB t)
  · refine ⟨⟨additiveAB t, true⟩, by simp [additiveClause], ?_⟩
    change assignmentOfGraph G (additiveAB t) = true
    rw [assignmentOfGraph_eq_true_iff]
    simpa [additiveAB] using hab
  · by_cases hac : G.Adj (additiveA t) (additiveSum t)
    · refine ⟨⟨additiveASum t, true⟩, by simp [additiveClause], ?_⟩
      change assignmentOfGraph G (additiveASum t) = true
      rw [assignmentOfGraph_eq_true_iff]
      simpa [additiveASum] using hac
    · by_cases hbc : G.Adj (additiveB t) (additiveSum t)
      · refine ⟨⟨additiveBSum t, true⟩, by simp [additiveClause], ?_⟩
        change assignmentOfGraph G (additiveBSum t) = true
        rw [assignmentOfGraph_eq_true_iff]
        simpa [additiveBSum] using hbc
      · exfalso
        apply hno
        refine ⟨additiveA t, additiveB t, additiveSum t, additiveSum_value t, ?_⟩
        rw [← SimpleGraph.isNClique_compl]
        apply SimpleGraph.is3Clique_triple_iff.mpr
        constructor
        · simp [t.2.1.ne, hab]
        constructor
        · simp [(additiveA_lt_sum t).ne, hac]
        · simp [(additiveB_lt_sum t).ne, hbc]

/--
If a mathematical graph is triangle-free and lacks the desired additive
independent triple, its Boolean edge assignment satisfies the core CNF.
-/
theorem assignmentOfGraph_satisfies_core (G : SimpleGraph SATVertex)
    (htriangle : G.CliqueFree 3) (hno : ¬HasAdditiveIndependentTriple G) :
    Satisfies (assignmentOfGraph G) coreCNF := by
  rw [satisfies_core_iff]
  exact ⟨assignmentOfGraph_satisfies_triangleClause G htriangle,
    assignmentOfGraph_satisfies_additiveClause G hno⟩

/--
The main soundness theorem for future certification: an UNSAT proof for the
finite Boolean core CNF yields the existing mathematical proposition
`Finite18`.
-/
theorem coreCNF_unsat_implies_finite18 (hunsat : Unsatisfiable coreCNF) : Finite18 := by
  intro G htriangle
  by_contra hno
  exact hunsat (assignmentOfGraph G)
    (assignmentOfGraph_satisfies_core G htriangle hno)

end JSP000746.SATEncoding
