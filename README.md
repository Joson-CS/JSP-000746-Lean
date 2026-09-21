# Lean Formalization of JSP-000746

This repository contains a Lean 4 formalization intended for submission to the
Justin Sun Prize as problem **JSP-000746**.

## Result

The underlying problem asks for three independent vertices of the form
`a`, `b`, and `a + b` in a triangle-free graph. In the finite formulation, the
vertex set is the positive integer interval `{1, ..., n}`. This formalization
proves that every such graph has the required three distinct independent
vertices whenever `n ≥ 18`. It also proves the corresponding statement for a
triangle-free graph on all positive integers.

The final Lean theorems are:

```lean
JSP000746.jsp000746_holdsFrom18 : HoldsFrom18
JSP000746.jsp000746_positiveInfinite : PositiveInfiniteStatement
```

Here, `HoldsFrom18` is the finite statement for every `n ≥ 18`, while
`PositiveInfiniteStatement` is the infinite statement on the positive
integers.

## Proof architecture

The proof follows this certified chain:

```text
mathematical statement
→ finite n = 18 reduction
→ 153 SAT variables
→ 888 clauses
→ deterministic DIMACS export
→ CaDiCaL LRAT certificate
→ Mathlib LRAT replay
→ Lean kernel verification
→ final theorem
```

The 153 Boolean variables represent the unordered pairs of 18 vertices. The
CNF contains 816 triangle-free clauses and 72 clauses excluding independent
additive triples, for a total of 888 clauses. Lean formally connects this
Boolean encoding to the `SimpleGraph` statement and proves the reduction from
the 18-vertex result to every `n ≥ 18` and to the positive-integer infinite
graph.

CaDiCaL is **not** part of the trusted base. It is used only to produce an LRAT
certificate. Mathlib reads and replays the actual DIMACS and LRAT files, and
the resulting proof is checked by the Lean kernel. Correctness therefore does
not depend on trusting the SAT solver or its UNSAT answer.

## Reproduction

```bash
git clone https://github.com/Joson-CS/JSP-000746-Lean.git
cd JSP-000746-Lean
lake build
```

The proof release is fixed at:

```yaml
tag: v1.0-proof
commit: e9004a8352cf99e85645090e2082f3f391507aa5
```

Clean-room verification has been performed from a fresh clone of this fixed
revision:

```text
lake build
Build completed successfully
```

## Certificate hashes

```text
core.cnf
260B7C50FAC4FCC4525F7253EB37A8750BF744CFF5BB41E92A314CDEA1CCAB45

core.lrat
2F8729BD57E5EE6D24292E2B51FC72AFAD884BEDF5234B808615568FE9BAC582
```

These hashes identify the exact CNF and LRAT files replayed by the Lean build.

## Axiom audit

Running `#print axioms` on the certified finite theorem and the final infinite
theorem reports only Lean/Mathlib's standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

The proof contains no:

```text
sorry
admit
custom axiom
native_decide
```

## Main files

```text
JSP000746/Definitions.lean
JSP000746/Finite18.lean
JSP000746/Reduction.lean
JSP000746/SATEncoding.lean
JSP000746/DIMACS.lean
JSP000746/LRAT.lean
certificates/core.cnf
certificates/core.lrat
```

- `Definitions.lean` states the finite and infinite mathematical problems.
- `Finite18.lean` defines the exact 18-vertex proposition.
- `Reduction.lean` proves the reductions from the 18-vertex core.
- `SATEncoding.lean` defines the independent finite Boolean encoding and its
  soundness theorem.
- `DIMACS.lean` gives deterministic variable numbering, clause ordering, and
  the formal DIMACS semantics bridge.
- `LRAT.lean` replays the certificate and derives the final theorems.

This repository is submitted, or intended for submission, as a Lean
formalization of JSP-000746. It does not claim that an award has been granted.
