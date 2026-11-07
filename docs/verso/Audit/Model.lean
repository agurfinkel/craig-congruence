import VersoManual
import ClausalProofInterpolation

open Verso.Genre Manual
open EUF

#doc (Manual) "The model and the claim" =>

# What an interpolant promises

Write A and B for the two inputs. An interpolant I must satisfy three
conditions: A entails I; I together with B is inconsistent; and every
symbol in I is shared. The third condition is a separate proof obligation.
A formula may satisfy both semantic conditions and still fail interpolation
by exposing a private function.

The library states these conditions twice because its two layers consume
different inputs. `IsInterpolant` takes conjunctions of ground literals and
returns a conjunction of equality Horn clauses. `IsClausalInterpolantAt`
takes two CNFs and a side to summarize, and accepts a CNF interpolant.
Side 0 is A; side 1 is B; `side.rev` is the opposite side. Both specifications
also record input inconsistency. That field follows from the semantic
conditions, but keeping it explicit makes the intended problem visible.

All semantic statements quantify over `Interpretation`: a nonempty domain
and a meaning for every function symbol. Terms are ground. A signature
indexes symbols by arity, so a term cannot apply a function to the wrong
number of arguments. Constants are simply applications of arity-zero symbols.
No finite-domain assumption or solver-specific representation enters these
semantics.

[Inspect the syntax](source/Basic/Syntax.lean.html),
[semantics](source/Basic/Semantics.lean.html), and
[clausal specification](source/ClausalProofInterpolation/Specification.lean.html).

# Three representations, three meanings

A cube conjoins literals; a clause disjoins them; a CNF conjoins clauses.
The distinction matters most at the empty value: the empty cube and empty
CNF mean true, while the empty clause means false. `CNF.falsum` is a CNF
containing that empty clause.

`Cube` and `Clausal.Clause` wrap private lists. They are distinct types even
though both store ordered literal collections. This prevents a clause from
silently becoming a conjunction. `Clause.falsifyingCube` performs the
deliberate crossing: it complements every literal and conjoins the results.
Falsifying a theory clause therefore supplies a conjunctive EUF conflict.

An equality Horn clause says that a list of equalities implies an equality,
or implies false when its optional conclusion is absent. `toCNF` translates
each implication into a disjunction of negated premises and its positive
conclusion. The bridge proves both semantic equivalence and sharedness;
the clausal layer does not need to reinterpret the equality proof.

[Inspect the Horn representation](source/Basic/Horn.lean.html) and
[its CNF embedding](source/Basic/HornToCNF.lean.html).

# Availability is different from ownership

Symbol colors describe vocabulary. A symbol is local to a partition or
shared across an adjacent boundary. For two inputs there is one shared
boundary. A term is available on a side when every symbol in it is allowed
there; its exact color describes that availability. An equality using an
A-local symbol and a B-local symbol is unavailable on either side and cannot
be a colorable literal in the admitted proof objects.

Occurrence ownership describes proof organization. A shared literal can
belong to either part of a colored clause. `ColoredClause` stores those parts
and proves their vocabulary is available to the corresponding owner.
`ClausePartition` additionally proves that concatenating the parts recovers
the original clause up to permutation. This permits reordering, while
preserving the original occurrences and their multiplicities.

These are supplied colors, checked against supplied syntax. The library
does not infer the exact intersection of two external symbol tables. An
auditor connecting a producer must check that the declared shared vocabulary
matches the intended problem.

[Inspect color availability](source/Basic/Color.lean.html),
[colored clauses](source/Basic/Colored.lean.html), and
[occurrence partitions](source/ClausalProofInterpolation/PartialInterpolant.lean.html).
