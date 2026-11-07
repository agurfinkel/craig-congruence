import VersoManual
import ClausalProofInterpolation

open Verso.Genre Manual
open EUF

#doc (Manual) "From theory conflicts to a clausal interpolant" =>

# One conflict supplies two obligations

A theory propagation from assumptions Gamma to p can enter resolution as
the clause `not Gamma or p`. A theory conflict enters as `not Gamma`.
Ordinary resolution can then combine theory reasoning with Boolean clauses.
It needs a valid theory leaf and, for local interpolation, a suitable shared
annotation at that leaf.

`EqualityTheoryCertificate` pairs a colored clause with an equality-exchange
conflict over its two falsifying parts. The same conflict proves the clause
valid and extracts its Horn annotation. This keeps validity and the
interpolation claim tied to one explanation. `annotation` fixes the
summarized side to 0; the surrounding local invariant supports either side.

The bridge accepts an already checked conflict regardless of how its
equality evidence was built. It does not require the indexed certificate
format. The more general `ColoredProofLeaf.theory` accepts a valid theory
lemma and an explicit proof owner, while its interpolation annotation is
supplied separately. Those general interfaces remain useful when evidence
comes from another verified construction.

`TheoryLemmaAnnotation.toPartialInterpolant` embeds the Horn summary into
CNF using the equivalence and sharedness theorems. No special mixed
resolution rule is needed after this point.

[Inspect the theory bridge](source/ClausalProofInterpolation/TheoryLemmaCertificate.lean.html)
and [the leaf contract](source/ClausalProofInterpolation/TheoryLemmaInterpolation.lean.html).

# A clause annotation describes what happens when the clause is false

At a proof clause C, split its owned occurrences into C_A and C_B. Write
`not C_A` for the cube falsifying every literal in the A part. The partial
interpolant J obeys:

```
A and not C_A entail J
J and B and not C_B are inconsistent
J uses only shared symbols
```

These are the fields of `IsPartialInterpolantAt` for side 0. At the empty
clause both falsifying cubes are empty and hence true. The invariant becomes
the Craig conditions without any further elimination step.

An A input clause receives false as its annotation: A and the falsification
of that same clause are already inconsistent. A B input clause receives true:
the contradiction sits entirely on the B side. These choices follow from
the displayed invariant. They should be checked against it before comparing
with another labeled interpolation convention.

# Why disjunction on one pivot and conjunction on the other

Resolution removes a pivot from the left parent and its complement from the
right. `PartitionedResolutionStep` records which side owns that pivot and
how falsifying the result projects to the parents. On the owning side, the
pivot's truth value selects one falsified parent part. On the other side,
both parent parts are falsified. Its four projection fields are substantial
hypotheses; pivot availability alone does not establish them.

If A owns the pivot, a falsified result gives one of the two A-side
annotations, so the result annotation is their disjunction. On the B side,
either disjunct contradicts the corresponding falsified parent. If B owns
the pivot, A obtains both annotations, so the result uses their conjunction;
the pivot value then selects the B-side contradiction.

`CNF.disjoin` represents disjunction by distributing over pairs of clauses
and removing repeated literals in each combined clause. A proved semantic
equivalence justifies this operation. Conjunction is list append. Neither
operation claims to minimize the interpolant, and distribution may enlarge it.

[Inspect the projection hypotheses and combination proofs](source/ClausalProofInterpolation/PartialInterpolant.lean.html)
and [CNF disjunction](source/Basic/Clause.lean.html).

# Fold explicit steps, then read the empty clause

`ResolutionStep` specifies the exact non-pivot membership of a duplicate-free
resolvent. It permits different literal orders. `ResolutionChain` starts
from an anchor and resolves against earlier indexed clauses. `ClauseTrace`
appends leaves and justified derived clauses. These are explicit resolution
certificates: reconstructing a chain from RUP hints or unit propagation lies
outside this calculus.

`ClauseAnnotation.resolve` combines one pair of annotated parents.
`ResolutionChainPartitioning` supplies the occurrence partitions and pivot
choices for intermediate results. `ClauseTraceInterpolation` extends the
annotation database alongside the trace. Its general leaf constructor accepts
an already proved annotation for that clause, so the invariant is the real
local obligation.

`InterpolatedClauseRefutation.sound` reads the annotation at a designated
empty-clause index. The completed certificate stores a database of correct
annotations; `ofTrace` is the constructor that records an incremental
construction before packaging it. The soundness endpoint needs the correct
annotation at the contradiction, independently of how it was obtained.

[Inspect clausal soundness](source/ClausalProofs/ClausalProof.lean.html) and
[the annotation fold](source/ClausalProofInterpolation/ClausalInterpolationTrace.lean.html).
