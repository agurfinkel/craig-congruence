-- SPDX-License-Identifier: MIT

import Basic.Horn
import CongruenceClosure.EquationalTheory

/-!
Finite, locally checkable certificates for ground equality derivations.

The certificate is deliberately LRAT-like: every new equality is justified by
one local rule whose references range only over the previously checked
database.  The checker therefore does not run congruence closure.  It merely
replays assumption, equivalence, and congruence steps into the semantic
`DerivesEq` relation.

The database is stored newest-first, so adding a step conses its conclusion.
This keeps the dependent indexing small while still enforcing acyclicity.
-/

namespace EUF

/-- One locally checkable equality inference over an earlier database. -/
inductive EqualityCertificateStep
    (formula : Cube sig) (previous : List (Equality sig)) :
    Equality sig → Type where
  | refl (term : Term sig) :
      EqualityCertificateStep formula previous ⟨term, term⟩
  | assumption (equality : Equality sig)
      (member : equality.literal ∈ formula) :
      EqualityCertificateStep formula previous equality
  | symm (source : Fin previous.length) :
      EqualityCertificateStep formula previous
        ⟨(previous.get source).right, (previous.get source).left⟩
  | trans (first second : Fin previous.length)
      (compatible : (previous.get first).right =
        (previous.get second).left) :
      EqualityCertificateStep formula previous
        ⟨(previous.get first).left, (previous.get second).right⟩
  | congr {arity : Nat} (function : sig.Function arity)
      (sources : Fin arity → Fin previous.length) :
      EqualityCertificateStep formula previous
        ⟨Term.app function (fun index => (previous.get (sources index)).left),
          Term.app function (fun index =>
            (previous.get (sources index)).right)⟩

namespace EqualityCertificateStep

/-- A locally valid step preserves the semantic equality-derivation relation. -/
def sound
    {formula : Cube sig} {previous : List (Equality sig)}
    {result : Equality sig}
    (step : EqualityCertificateStep formula previous result)
    (previousSound : ∀ index : Fin previous.length,
      DerivesEq formula (previous.get index).left
        (previous.get index).right) :
    DerivesEq formula result.left result.right := by
  cases step with
  | refl term =>
      exact .refl term
  | assumption equality member =>
      exact .assumption member
  | symm source =>
      exact (previousSound source).symm
  | trans first second compatible =>
      apply (previousSound first).trans
      simpa only [compatible] using previousSound second
  | congr function sources =>
      exact .congr function (fun index => previousSound (sources index))

end EqualityCertificateStep

/-- A finite equality proof DAG. Every new node may reference only nodes in
the tail, so malformed forward or cyclic references are unrepresentable. -/
inductive EqualityCertificate (formula : Cube sig) :
    List (Equality sig) → Type where
  | empty : EqualityCertificate formula []
  | add
      {previous : List (Equality sig)} {result : Equality sig}
      (certificate : EqualityCertificate formula previous)
      (step : EqualityCertificateStep formula previous result) :
      EqualityCertificate formula (result :: previous)

namespace EqualityCertificate

/-- Replay every checked node into `DerivesEq`. -/
def derivation
    {formula : Cube sig} {equalities : List (Equality sig)}
    (certificate : EqualityCertificate formula equalities) :
    ∀ index : Fin equalities.length,
      DerivesEq formula (equalities.get index).left
        (equalities.get index).right := by
  induction certificate with
  | empty =>
      intro index
      exact Fin.elim0 index
  | @add previous result certificate step previousSound =>
      intro index
      refine Fin.cases ?_ (fun earlier => ?_) index
      · exact step.sound previousSound
      · exact previousSound earlier

/-- The most recently added equality is the certificate conclusion. -/
def conclusion
    {formula : Cube sig} {result : Equality sig}
    {previous : List (Equality sig)}
    (certificate : EqualityCertificate formula (result :: previous)) :
    DerivesEq formula result.left result.right :=
  certificate.derivation 0

end EqualityCertificate

end EUF
