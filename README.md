<!-- SPDX-License-Identifier: MIT -->

# CraigCongruence

A Lean 4 development for proofs about equality with uninterpreted functions
(EUF).

The current formalization provides:

- arity-indexed function signatures and ground terms;
- finite colored signatures, colorability, and local/shared formula colors;
- semantic interpolation conditions for two colored conjunctive formulas;
- color-partitioned EUF clauses and color-indexed partial interpolants for
  theory-lemma leaves;
- a generic clausal resolution calculus with a semantic soundness theorem;
- a semantics- and sharedness-preserving embedding of equality Horn summaries
  into general EUF CNFs;
- colored LRAT-style proof leaves and a color-indexed partial-interpolant
  invariant for clausal proofs;
- interpolation folds over explicitly colored resolution chains and builds
  clause annotations incrementally alongside an LRAT trace;
- direct shared-interface extraction certificates for colorable clausal
  proofs, together with trace-level ownership, dependency restrictions, and
  proof-relevant pruning witnesses;
- incremental semantic pruning of colorable LRAT-like traces, proving that
  the selected finite shared interface is a clausal Craig interpolant;
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

## Library structure

The single Lake package contains six libraries with explicit import
dependencies:

- `Basic`: ground terms and literals, semantics, clauses and CNFs, colored
  signatures and clausal forms, equality Horn formulas, and Horn-to-CNF
  conversion;
- `CongruenceClosure`: equality derivations and abstract congruence-closure
  certificates;
- `EUFInterpolation`: semantic interpolation for conjunctions of literals and
  direct interpolant extraction from a congruence-closure conflict;
- `ClausalProofs`: resolution steps, chains, traces, refutations, and their
  semantic soundness theorems;
- `ClausalProofInterpolation`: colored theory leaves, partial-interpolant
  rules, trace annotation, pruning, and complete clausal interpolation; and
- `Archived`: preserved results that are not dependencies of the end-to-end
  interpolation result.

The dependency graph is:

```text
Basic -> CongruenceClosure -> EUFInterpolation -----+
  |                                                  |
  +-> ClausalProofs ---------------------------------+-> ClausalProofInterpolation
CongruenceClosure -> Archived
```

The default `lake build` verifies the executable and all libraries it uses.
The archived library can be checked separately with:

```sh
