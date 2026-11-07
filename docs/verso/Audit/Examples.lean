import VersoManual
import ClausalProofInterpolation
import ClausalProofInterpolation.Z3Proof43Trace

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open EUF

#doc (Manual) "Examples that distinguish the obligations" =>

# The private-function example calculates a Horn summary

`Z3HornGap` formalizes the example from the exchange chapter. B first produces
the shared equality x = y. A consumes it to derive u = v using its private
function F, then B uses that equality to close its explicit disequality.
The extracted formula contains the single implication from x = y to u = v.
The calculation and its semantic specification are separately checked:

```lean
example : Z3HornGap.conflict.interpolant =
    Z3HornGap.interpolant :=
  Z3HornGap.calculated_interpolant

example : IsInterpolant Z3HornGap.signature
    Z3HornGap.formulaA Z3HornGap.formulaB
    Z3HornGap.interpolant :=
  Z3HornGap.isInterpolant
```

This example isolates expressiveness. An unconditional shared equality
summary loses the premise; an expression containing F loses sharedness.
The Lean result proves the chosen summary satisfies all the conditions. It
does not establish the behavior of another version of Z3.

[Inspect the complete exchange certificate](source/EUFInterpolation/Z3HornGap.lean.html).

# A congruence lemma enters as an ordinary theory leaf

`EqualityTheoryCertificateExample` certifies the clause
`x != y or F(x) = F(y)`. Color 0 supplies x = y. Color 1 consumes it in an
indexed congruence step, deriving F(x) = F(y) and contradicting the falsifying
disequality. The shared annotation is the singleton equality x = y.

The example derives both the clause's validity and its annotation from the
same conflict. `clausalAnnotation` embeds it in the ordinary clausal
annotation type, even with no surrounding input clauses. This demonstrates
the theory-leaf bridge. It does not yet demonstrate an imported external
certificate or a whole refutation using this particular leaf.

[Inspect equality replay and the leaf embedding](source/ClausalProofInterpolation/EqualityTheoryCertificateExample.lean.html).

# Proof 43 separates symbol sharing from Boolean occurrence

The Proof 43 instance contains an A-local constant a, a B-local constant c,
and shared b, d, and F. B asserts `b = c` and `F(c) = F(d)`. Its consequences
therefore include `F(b) = F(d)`. A's clauses contradict that equality. The
shared interpolant is its negation.

`Z3Proof43.z3_interpolant` proves the proposed CNF satisfies the Craig
conditions directly. `Z3Proof43Trace` additionally constructs the normalized
refutation skeleton with four input leaves, three theory leaves, and four
derived clauses. Its resolution chains contain ten binary steps. The file
proves the theory leaves valid, supplies their annotations and occurrence
partitions, and combines annotations to the empty clause.

The atom p abbreviates `F(b) = F(d)`. Its symbols are all shared, yet p
occurs in the original input only on the A side. The McMillan-style ownership
used in this example follows Boolean occurrence rather than equating every
vocabulary-shared atom with a B-owned pivot. In particular, the first
theory-leaf annotation is `not p`. An auditor who conflates vocabulary and
occurrence ownership will predict a different calculation.

The current calculation yields the unit CNF containing `not p`. These checked
examples state both the exact computed result and its Craig property:

```lean
example : Z3Proof43Trace.annotationEmpty.interpolant =
    [Clausal.Clause.ofList [Z3Proof43Trace.p.negate]] :=
  Z3Proof43Trace.calculated_interpolant

example : IsClausalInterpolantAt Z3Proof43.inputs 0
    Z3Proof43Trace.annotationEmpty.interpolant :=
  Z3Proof43Trace.trace_interpolant_sound
```

The example uses `ClauseAnnotation.resolve` directly to combine the ten
steps; it does not instantiate the generic indexed annotation-database fold.
Its proof is still an instance of the same local invariant. The clause
skeleton, EUF meanings, and normalization choices were transcribed in Lean;
a verified parser from a Z3 proof log is outside this example.

[Inspect the input and direct endpoint](source/ClausalProofInterpolation/Z3Proof43.lean.html)
and [the explicit trace and annotation calculation](source/ClausalProofInterpolation/Z3Proof43Trace.lean.html).
