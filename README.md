# Lean Formalization of JSP-000746

This repository contains a Lean 4 formalization intended for submission to the
Justin Sun Prize as problem **JSP-000746**.

## Result

The finite problem concerns triangle-free graphs whose vertex set is the
positive integer interval `{1, ..., n}`. This repository proves that, for every
`n ≥ 18`, every such graph contains three distinct, pairwise independent
vertices `a`, `b`, and `a + b`.

The core finite theorem is:

```lean
JSP000746.jsp000746_holdsFrom18 : HoldsFrom18
```

The positive-integer infinite corollary, derived from the finite theorem by
restricting an infinite graph to its first 18 vertices, is:

```lean
JSP000746.jsp000746_positiveInfinite : PositiveInfiniteStatement
```

## Proof architecture

The proof follows this certified chain:

```text
mathematical statement
→ finite n = 18 reduction
→ 153 SAT variables
→ 888 clauses
→ deterministic DIMACS export
→ CaDiCaL-generated LRAT certificate
→ Mathlib LRAT replay
→ Lean kernel verification
→ final theorem
```

The exact encoding size is:

```text
153 Boolean variables
816 triangle-free clauses
72 additive-triple clauses
888 clauses total
```

The variables represent the unordered pairs of 18 vertices. Lean formally
connects this Boolean encoding to the `SimpleGraph` statement and proves the
reduction from the 18-vertex result to every `n ≥ 18` and then to the
positive-integer infinite graph.

CaDiCaL is **not** part of the trusted base. It only generates the LRAT
certificate. Mathlib reads the actual CNF and LRAT files, replays the
certificate, and submits the resulting proof term to the Lean kernel for
verification. Correctness therefore does not depend on trusting the solver or
its UNSAT answer.

## Reproduction

```bash
git clone https://github.com/Joson-CS/JSP-000746-Lean.git
cd JSP-000746-Lean
lake build
```

The fixed verification environment is:

```yaml
Lean: 4.34.0
mathlib commit: 5ed2965256430c3649e86755f9576b54eca72435
```

## First public proof snapshot

```text
tag:
v1.0-proof

commit:
e9004a8352cf99e85645090e2082f3f391507aa5
```

The tag `v1.0-proof` resolves to commit
`e9004a8352cf99e85645090e2082f3f391507aa5`.

Clean-room verification has been performed from a fresh clone of this
snapshot:

```text
lake build
Build completed successfully
```

## Certificate hashes

```text
certificates/core.cnf
260B7C50FAC4FCC4525F7253EB37A8750BF744CFF5BB41E92A314CDEA1CCAB45

certificates/core.lrat
2F8729BD57E5EE6D24292E2B51FC72AFAD884BEDF5234B808615568FE9BAC582
```

These hashes identify the exact CNF and LRAT files replayed by the Lean build.
The repository's `.gitattributes` rules keep both certificate files unchanged
byte-for-byte across platforms.

## Certificate provenance

```text
CaDiCaL 3.0.1
s UNSATISFIABLE
exit code 20
```

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

This repository is intended for submission as a Lean formalization of JSP-000746. No award status is claimed.
