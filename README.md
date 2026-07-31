# EUF ITP Lean

A Lean 4 development for proofs about equality with uninterpreted functions
(EUF).

The current formalization provides:

- arity-indexed function signatures and ground terms;
- finite colored signatures, colorability, and local/shared formula colors;
- semantic interpolation conditions for two colored conjunctive formulas;
- color-partitioned EUF clauses and color-indexed partial interpolants for
  theory-lemma leaves;
- a generic clausal resolution calculus with a semantic soundness theorem;
- colored LRAT-style proof leaves and a color-indexed partial-interpolant
  invariant for clausal proofs;
- a sound fixed-signature EUF interpolation extractor producing equality Horn
  clauses from alternating A/B congruence-closure certificates;
- equality and disequality literals, interpreted conjunctively;
- standard EUF interpretations and satisfaction;
- equality derivations closed under reflexivity, symmetry, transitivity, and
  function congruence;
- abstract congruence closures presented by convergent D-rules and C-rules;
- certified congruence graphs and undirected graph connectivity; and
- `unsatisfiable_of_congruence_graph_conflict`, proving that a graph path
  between the two sides of an asserted disequality makes the formula
  unsatisfiable.

Build the project with:

```sh
lake build
```
