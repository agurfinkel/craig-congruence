-- SPDX-License-Identifier: MIT

import CongruenceClosure.EquationalTheory

namespace EUF

/-! # Abstract congruence closure

The definitions in this file mechanize the core of Definitions 1 and 2 of
Bachmair, Tiwari, and Vigneron, "Abstract Congruence Closure". The original
signature is extended with a disjoint type of fresh constants. D-rules describe
applications of original symbols to class constants, while C-rules rewrite one
class constant to another.
-/

/-- Extend `signature` by a disjoint type `K` of fresh constants. -/
def ExtendedSignature (signature : Signature) (K : Type) : Signature where
  Function arity := signature.Function arity ⊕ (if arity = 0 then K else Empty)

namespace ExtendedSignature

/-- Embed an original function symbol into the extended signature. -/
def function {signature : Signature} {K : Type} {arity : Nat}
    (symbol : signature.Function arity) :
    (ExtendedSignature signature K).Function arity :=
  .inl symbol

/-- Regard a fresh class constant as a ground term of the extended signature. -/
def constant {signature : Signature} {K : Type} (name : K) :
    Term (ExtendedSignature signature K) :=
  .constant (.inr name)

/-- Homomorphically embed an original ground term into the extended signature. -/
def term {signature : Signature} {K : Type} :
    Term signature → Term (ExtendedSignature signature K)
  | .app symbol arguments =>
      .app (function symbol) (fun i => term (arguments i))

end ExtendedSignature

/-- A D-rule `f(c₁, ..., cₙ) → c` records the class of an application of an
original function symbol to class constants. -/
structure DRule (signature : Signature) (K : Type) where
  arity : Nat
  function : signature.Function arity
  arguments : Fin arity → K
  result : K

namespace DRule

def left (rule : DRule signature K) :
    Term (ExtendedSignature signature K) :=
  .app (.inl rule.function)
    (fun i => ExtendedSignature.constant (rule.arguments i))

def right (rule : DRule signature K) :
    Term (ExtendedSignature signature K) :=
  ExtendedSignature.constant rule.result

end DRule

/-- A C-rule rewrites one fresh class constant to another. -/
structure CRule (K : Type) where
  left : K
  right : K

namespace CRule

def leftTerm {signature : Signature} (rule : CRule K) :
    Term (ExtendedSignature signature K) :=
  ExtendedSignature.constant rule.left

def rightTerm {signature : Signature} (rule : CRule K) :
    Term (ExtendedSignature signature K) :=
  ExtendedSignature.constant rule.right

end CRule

/-- An abstract rewrite system consists exclusively of D-rules and C-rules. A
predicate presentation keeps the mathematical definition independent of a
particular finite container or implementation. -/
structure AbstractRewriteSystem (signature : Signature) (K : Type) where
  dRule : DRule signature K → Prop
  cRule : CRule K → Prop

namespace AbstractRewriteSystem

variable {signature : Signature} {K : Type}
variable {system : AbstractRewriteSystem signature K}
variable {left middle right : Term (ExtendedSignature signature K)}

/-- One rewrite step, including closure under arbitrary term contexts. -/
inductive Rewrites (system : AbstractRewriteSystem signature K) :
    Term (ExtendedSignature signature K) →
      Term (ExtendedSignature signature K) → Prop where
  | dRule (rule : DRule signature K) :
      system.dRule rule → Rewrites system rule.left rule.right
  | cRule (rule : CRule K) :
      system.cRule rule → Rewrites system rule.leftTerm rule.rightTerm
  | argument {arity : Nat}
      (function : (ExtendedSignature signature K).Function arity)
      (arguments : Fin arity → Term (ExtendedSignature signature K))
      (index : Fin arity) (reduct : Term (ExtendedSignature signature K)) :
      Rewrites system (arguments index) reduct →
      Rewrites system (.app function arguments)
        (.app function (fun i => if i = index then reduct else arguments i))

/-- Reflexive-transitive rewriting. -/
inductive RewritesStar (system : AbstractRewriteSystem signature K) :
    Term (ExtendedSignature signature K) →
      Term (ExtendedSignature signature K) → Prop where
  | refl (term) : RewritesStar system term term
  | tail {first middle last} :
      RewritesStar system first middle →
      system.Rewrites middle last →
      RewritesStar system first last

theorem RewritesStar.single (rewrite : system.Rewrites left right) :
    system.RewritesStar left right :=
  .tail (.refl left) rewrite

theorem RewritesStar.trans
    (first : system.RewritesStar left middle)
    (second : system.RewritesStar middle right) :
    system.RewritesStar left right := by
  induction second with
  | refl => exact first
  | tail _ step ih => exact .tail ih step

/-- Two terms are joinable if they rewrite to a common term. -/
def Joinable (system : AbstractRewriteSystem signature K)
    (left right : Term (ExtendedSignature signature K)) : Prop :=
  ∃ common, system.RewritesStar left common ∧ system.RewritesStar right common

/-- The symmetric, reflexive, transitive closure of rewriting. -/
inductive Equivalent (system : AbstractRewriteSystem signature K) :
    Term (ExtendedSignature signature K) →
      Term (ExtendedSignature signature K) → Prop where
  | refl (term) : Equivalent system term term
  | rewrite {a b} :
      system.Rewrites a b → Equivalent system a b
  | symm {a b} :
      Equivalent system a b → Equivalent system b a
  | trans {a b c} :
      Equivalent system a b →
      Equivalent system b c →
      Equivalent system a c

theorem RewritesStar.equivalent
    (rewrites : system.RewritesStar left right) :
    system.Equivalent left right := by
  induction rewrites with
  | refl => exact .refl _
  | tail _ step ih => exact .trans ih (.rewrite step)

theorem equivalent_of_joinable (joinable : system.Joinable left right) :
    system.Equivalent left right := by
  rcases joinable with ⟨common, leftSteps, rightSteps⟩
  exact .trans leftSteps.equivalent rightSteps.equivalent.symm

/-- Ground confluence of the abstract rewrite system. All terms in this
development are ground, so no separate ground-term restriction is necessary. -/
def Confluent (system : AbstractRewriteSystem signature K) : Prop :=
  ∀ source left right,
    system.RewritesStar source left →
    system.RewritesStar source right →
    system.Joinable left right

theorem joinable_refl (term : Term (ExtendedSignature signature K)) :
    system.Joinable term term :=
  ⟨term, .refl term, .refl term⟩

theorem joinable_of_rewrites (rewrite : system.Rewrites left right) :
    system.Joinable left right :=
  ⟨right, RewritesStar.single rewrite, .refl right⟩

theorem Joinable.symm (joinable : system.Joinable left right) :
    system.Joinable right left := by
  rcases joinable with ⟨common, leftSteps, rightSteps⟩
  exact ⟨common, rightSteps, leftSteps⟩

theorem Joinable.trans
    (confluent : system.Confluent)
    (first : system.Joinable left middle)
    (second : system.Joinable middle right) :
    system.Joinable left right := by
  rcases first with ⟨firstCommon, leftSteps, middleFirstSteps⟩
  rcases second with ⟨secondCommon, middleSecondSteps, rightSteps⟩
  rcases confluent middle firstCommon secondCommon
      middleFirstSteps middleSecondSteps with
    ⟨common, firstCommonSteps, secondCommonSteps⟩
  exact ⟨common, leftSteps.trans firstCommonSteps,
    rightSteps.trans secondCommonSteps⟩

/-- In a confluent system, rewrite equivalence is the same as rewriting to a
common term. This is the `↔* = →* ◦ ←*` property used in Definition 2(iii)
of the paper. -/
theorem joinable_of_equivalent
    (confluent : system.Confluent)
    (equivalent : system.Equivalent left right) :
    system.Joinable left right := by
  induction equivalent with
  | refl term => exact joinable_refl term
  | rewrite step => exact joinable_of_rewrites step
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans confluent ih₂

theorem equivalent_iff_joinable (confluent : system.Confluent) :
    system.Equivalent left right ↔ system.Joinable left right :=
  ⟨joinable_of_equivalent confluent, equivalent_of_joinable⟩

/-- Absence of infinite rewrite sequences. -/
def Terminating (system : AbstractRewriteSystem signature K) : Prop :=
  WellFounded (fun reduct source => system.Rewrites source reduct)

/-- A ground-convergent rewrite system is terminating and confluent. -/
def GroundConvergent (system : AbstractRewriteSystem signature K) : Prop :=
  system.Terminating ∧ system.Confluent

/-- A fresh constant represents an original term when the embedded term and
the constant are equivalent through the abstract rewrite system. -/
def Represents (system : AbstractRewriteSystem signature K) (name : K)
    (term : Term signature) : Prop :=
  system.Equivalent (ExtendedSignature.term term)
    (ExtendedSignature.constant name)

end AbstractRewriteSystem

/-- An abstract congruence closure in the sense of Bachmair, Tiwari, and
Vigneron.

`represents_original` is Definition 2(i), `ground_convergent` is Definition
2(ii), and `conservative` is Definition 2(iii). The latter states that the
finite abstract system characterizes the entire, generally infinite,
equational theory of the input formula. Disequality literals do not generate
equations and are therefore ignored by `DerivesEq`. -/
structure AbstractCongruenceClosure (formula : Formula signature)
    (system : AbstractRewriteSystem signature K) : Prop where
  represents_original :
    ∀ name : K, ∃ term : Term signature, system.Represents name term
  ground_convergent : system.GroundConvergent
  conservative :
    ∀ left right : Term signature,
      DerivesEq formula left right ↔
        system.Joinable (ExtendedSignature.term left)
          (ExtendedSignature.term right)

namespace AbstractCongruenceClosure

/-- Every equality recognized by an abstract congruence closure is a semantic
consequence of the original formula. -/
theorem entails_equality_of_joinable
    (closure : AbstractCongruenceClosure formula system)
    (joinable : system.Joinable (ExtendedSignature.term left)
      (ExtendedSignature.term right)) :
    Entails formula [Literal.eq left right] := by
  have derivation : DerivesEq formula left right :=
    (closure.conservative left right).mpr joinable
  intro interpretation satisfies literal member
  simp only [List.mem_singleton] at member
  subst literal
  exact derivation.sound satisfies

end AbstractCongruenceClosure

end EUF
