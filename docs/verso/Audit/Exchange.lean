import VersoManual
import ClausalProofInterpolation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open EUF

#doc (Manual) "Why equality exchange produces Horn clauses" =>

# A conditional contribution

Suppose x, y, u, and v are shared constants, and F is private to A:

```
A: u = F(x), v = F(y)
B: x = y, u != v
```

B supplies x = y. Congruence then lets A derive u = v, which contradicts B.
A alone does not entail u = v: choose distinct x and y and give F distinct
values there. What A does entail is the conditional equality
`x = y -> u = v`. That implication uses only shared symbols and contradicts
B. The dependency on x = y is exactly the information that must survive
elimination of F.

A conjunction of unconditional shared equalities cannot express this
contribution. The extractor therefore uses equality Horn clauses. The
checked example calculates this particular implication in the examples
chapter.

# Preserve the reason for each message

`EqualityExchangeProof` records a shared equality produced by one side.
Its local `DerivesEq` proof may use that side's input together with shared
equalities received from the other side. `EqualityExchangeDependencies`
stores the proofs of those received equalities. The mutually inductive
objects form a finite, well-founded explanation: a dependency cannot cite
the communication step currently being constructed.

`TermNaming` fixes a representative original term for each internal name.
`SharedEqualityEdge` proves that the equality between two representatives
is shared. Fresh class names therefore disappear when a message becomes an
interpolant atom. The core type does not require the set of names to be
finite; each supplied exchange proof uses finitely much evidence.

For a producer on side 0, extraction emits the Horn implication from its
received equalities to its conclusion. For a producer on side 1, extraction
emits no new clause. Both cases retain the clauses extracted recursively
from dependencies. This asymmetry reflects the chosen orientation: I must
follow from A, while B will use I to reconstruct the conflict.

# Two induction arguments explain soundness

The entailment induction shows that A satisfies every emitted implication.
At an A node, assume its premises; the local equality derivation proves its
conclusion. At a B node, there is no new implication to establish, but the
clauses collected from its dependencies still follow from A.

The reconstruction induction starts with a model of B and I. At a B node,
the local derivation recovers the equality from B and the recursively
recovered premises. At an A node, the implication in I recovers the
conclusion once those premises hold. Thus B and I can recover every equality
needed to replay the final conflict.

The terminal disequality determines how extraction finishes. If B owns it,
the recovered equalities directly contradict B. If A owns it, extraction
adds a negative Horn clause saying that its received premises cannot all
hold. B and the earlier clauses recover those premises and violate that
negative clause. Sharedness follows independently from the edge and
dependency invariants; neither semantic argument substitutes for it.

`EqualityInterpolationConflict.sound` packages these results. Its essential
inputs remain visible in this checked use:

```lean
example {sig : ColoredSignature 2} {naming : TermNaming sig}
    {formulas : InterpolationColor → Cube sig}
    (conflict :
      EqualityInterpolationConflict sig naming formulas)
    (colors :
      ∀ side, Cube.IsColor sig side (formulas side)) :
    IsInterpolant sig (formulas 0) (formulas 1)
      conflict.interpolant :=
  conflict.sound colors
```

[Inspect extraction and the induction proofs](source/EUFInterpolation/InterpolationProcedure.lean.html).

# Equality evidence can come from different producers

`DerivesEq` admits assumptions, reflexivity, symmetry, transitivity, and
function congruence. Its soundness proof is an induction on those rules.
An indexed `EqualityCertificate` replays the same rules from a newest-first
database. Each step can refer only to the previous database; its `Fin`
indices rule out forward references. Replay constructs `DerivesEq` evidence
without running a congruence-closure search.

The abstract closure adapter offers another route. D-rules name function
applications; C-rules identify class names. `AbstractCongruenceClosure`
assumes ground convergence and conservativity for the represented input.
`ofAbstractClosure` uses those hypotheses to turn joinable names into an
exchange derivation. The interpolation proof depends on that resulting
derivation, so it can also accept evidence produced without a rewrite system.

Convergence and conservativity are fields to supply, not properties proved
for a concrete closure implementation here. Likewise, the indexed certificate
is already typed Lean evidence: membership and compatibility proofs are
part of its constructors. A parser and checker for untrusted serialized
indices would have further work to do.

[Inspect equality replay](source/CongruenceClosure/EqualityCertificate.lean.html),
[abstract closure](source/CongruenceClosure/AbstractCongruenceClosure.lean.html), and
[certificate adapters](source/EUFInterpolation/InterpolationCertificate.lean.html).
