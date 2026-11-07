import VersoManual
import ClausalProofInterpolation

open Verso.Genre Manual

#doc (Manual) "What the development establishes" =>

# Audit the supplied evidence before reading the endpoint

The main results establish soundness for supplied certificates. To audit an
application, start with the intended input partition and shared vocabulary.
Then identify which evidence supports its interpolant: an alternating
equality conflict, local clause annotations, or a shared proof cut. Read the
hypotheses of that route before interpreting its final Craig theorem.

For equality exchange, inspect the local derivations, shared representatives,
and terminal disequality. The extractor proves that the certificate yields
a Horn interpolant. The development does not construct a certificate for
every inconsistent pair of inputs, prove termination of such a search, or
prove completeness of an implemented closure engine.

For local clausal interpolation, inspect theory annotations and the four
resolution projection obligations. The generic fold proves that these
annotations compose. It does not infer their occurrence partitions, choose
pivot owners, or reconstruct explicit chains from operational solver hints.
`InterpolatedClauseRefutation` is a container of already correct annotations;
its type alone does not certify their provenance through a particular
interpolation algorithm.

For shared-interface extraction, inspect ownership and each allowed parent
dependency. The semantic pruning pass constructs a sound interface from
that coloring. It does not prove that every refutation admits this discipline
or produce an operational proof-reordering algorithm. The explicit sliced
trace format has its own constructor obligations.

# Solver correspondence is a separate claim

The library models equality and disequality over uninterpreted functions.
Its generic resolution objects require an involutive literal complement;
their semantic soundness here is instantiated with EUF interpretations.
It does not model arbitrary SMT theories or Z3's internal memory and proof
data structures.

An external producer would need to preserve terms, arities, clause
normalization, input membership, symbol colors, and occurrence ownership.
Its equality explanations would need to produce local derivations and
exchange boundaries. Its Boolean hints would need to produce the explicit
resolution chains. These obligations can be discharged by verified
translation or by a checker for an untrusted certificate format. Neither
follows merely from proving a matching mathematical interpolant.

The examples provide useful correspondence evidence at the level of
hand-constructed Lean certificates. Historical Z3 observations live in the
research notebook. The manual's claims about the current proof development
are anchored in the imported Lean modules.

# Where the main argument lives

`Basic` supplies syntax, semantics, colors, Horn formulas, and CNFs.
`CongruenceClosure` supplies equality derivations, indexed replay, and the
abstract closure interface. `EUFInterpolation` extracts Horn summaries.
`ClausalProofs` supplies explicit resolution and colored leaves.
`ClausalProofInterpolation` supplies both local interpolation and shared-cut
extraction. The manual also imports `Z3Proof43Trace` explicitly because the
root interpolation library does not import that longer example.

`Archived` preserves older graph and naming results. Those files are outside
the dependency closure of these endpoints. They need not be read to justify
the current extraction theorems.

The documentation build elaborates the examples and obtains the reference
declarations from Lean. A separate axiom audit prints the dependencies of
selected soundness endpoints and rejects axioms other than Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. This check detects an admitted
proof at those endpoints; it does not decide whether their specifications
capture the intended external problem. The prose and supplied hypotheses
remain the human auditor's responsibility.

[Read the generated axiom dependency report](axioms.txt).
