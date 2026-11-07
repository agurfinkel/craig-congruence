import VersoManual
import ClausalProofInterpolation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open EUF

#doc (Manual) "A shared cut can replace local annotations" =>

Some refutations already expose the information that must cross from A to B
as shared clauses. Those clauses can serve as the interpolant directly.
The proof then establishes that A entails each selected clause and that B
contradicts their conjunction. This route avoids computing a partial
interpolant for each theory leaf, but it requires a discipline on dependencies.

# The cut permits communication in one direction

Choose a source side and assign an owner to every trace clause.
`ParentAllowed` permits same-owner dependencies. A target-owned inference
may additionally consume a source-owned parent when that parent is shared.
A source-owned inference cannot consume a target-owned parent. The anchor
and every parent actually referenced by the resolution chain must satisfy
this restriction.

This asymmetry is the reason a source clause remains a consequence of the
source inputs alone. The target can read a source clause through the shared
interface, but the source cannot rely on a fact that needs the target inputs.
Vocabulary colorability by itself would not prevent such a circular
justification.

`ColorableClauseTrace` carries the owner database, input memberships, and
derived-step restrictions. Derived clauses have a vocabulary-availability
proof at their owner. Theory leaves can contain differently owned literal
parts and need only EUF validity: a valid lemma is available under either
side's semantic assumptions. Theory-leaf ownership therefore does not mean
that all of its symbols belong to that owner.

# Select the shared source clauses

`allSharedSource` selects every shared source-owned clause occurrence in the
finite trace. It need not select a minimal interface, nor only clauses that
the target actually consumes. The coverage property ensures that every
possible crossing permitted by the coloring has a clause in the interface.

The pruning induction assigns two meanings to trace clauses. A source-owned
clause follows from the source input. A target-owned clause follows from the
target input together with the interface. For a crossing dependency, the
target reads the source parent directly from that interface. For a same-owner
dependency, it uses the preceding entailment database. Resolution soundness
then proves the next clause.

If the empty clause belongs to the target, the target entailment refutes the
interface together with the target inputs. If it belongs to the source, it
is itself a shared source clause and is selected into the interface, which
is already false. Both cases establish the same interpolant specification.

The endpoint is short because the construction has already established
those obligations:

```lean
example {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {source : Fin 2}
    (proof : ColorableClauseRefutation inputs source) :
    IsClausalInterpolantAt inputs source proof.interface :=
  proof.interpolant
```

# Semantic pruning and explicit trace pruning

`SemanticallyPrunedColorableTrace` stores the selected interface and the
entailment induction. `ColorableClauseRefutation.interpolant` constructs this
semantic result from the supplied coloring.

`PrunedColorableTrace` describes a stronger, separate output: explicit
source derivations and an explicit target refutation after cutting the
interface. `SharedInterfaceCertificate` packages those two proof objects
without the coloring bookkeeping. Its soundness theorem is implemented,
and an explicit pruning witness converts to it. The current automatic
semantic pass does not construct that pair of sliced resolution traces.

The selection and extraction functions are noncomputable because the generic
signature supplies neither decidable term equality nor an executable color
test. Finite selection and its soundness have been proved; an executable
exporter needs a concrete representation and decision procedures. Likewise,
finding a coloring that satisfies the cut, or reordering an arbitrary proof
to expose one, is an additional producer obligation.

[Inspect selection, pruning, and both certificate interfaces](source/ClausalProofInterpolation/SharedInterfaceInterpolation.lean.html).
