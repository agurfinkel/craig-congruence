-- SPDX-License-Identifier: MIT

import Basic.Colored
import ClausalProofs.ClausalProof

/-!
Common colored EUF proof leaves and refutations. Theory leaves retain only a
valid theory clause and its proof owner; interpolation evidence is supplied by
the interpolation procedure that needs it.
-/

namespace EUF

/-- A theory lemma is a colorable clause which is valid in EUF. Mixed theory
lemmas are allowed, but no literal occurrence itself is mixed. -/
structure TheoryLemma (sig : ColoredSignature 2)
    extends ColoredClause sig where
  valid : EUF.Clause.Valid (Clausal.Clause.append (part 0) (part 1))

instance : Coe (TheoryLemma sig) (ColoredClause sig) :=
  ⟨TheoryLemma.toColoredClause⟩

instance : Coe (TheoryLemma sig) (Clause sig) :=
  ⟨fun lemma => (lemma : ColoredClause sig).toClause⟩

/-- Leaves admitted by a colored clausal proof. An input leaf records its
input partition. A theory leaf records a valid EUF clause and the side that
owns it in this proof; it does not require an interpolation annotation. -/
inductive ColoredProofLeaf (inputs : ColoredCNF sig) : Clause sig → Type where
  | input (side : Fin 2) (member : clause ∈ inputs.part side) :
      ColoredProofLeaf inputs clause
  | theory (owner : Fin 2) (lemma : TheoryLemma sig) :
      ColoredProofLeaf inputs lemma

namespace ColoredProofLeaf

/-- Leaf clauses are satisfied by every interpretation satisfying the input
clauses: input leaves are assumptions and theory leaves are EUF-valid. -/
theorem sound {sig : ColoredSignature 2}
    {inputs : ColoredCNF sig} {clause : Clause sig}
    (leaf : ColoredProofLeaf inputs clause)
    (interpretation : Interpretation sig)
    (satisfiesInputs : inputs.Satisfied interpretation) :
    clause.Satisfied interpretation := by
  cases leaf with
  | input side member => exact satisfiesInputs side _ member
  | theory _ lemma => exact lemma.valid interpretation

end ColoredProofLeaf

/-- A clausal refutation with colored input leaves and owned valid theory
leaves. -/
abbrev ColoredClauseRefutation (inputs : ColoredCNF sig) :=
  ClauseRefutation (ColoredProofLeaf inputs)

namespace ColoredClauseRefutation

/-- Existence of a colored refutation implies that the inputs are
EUF-unsatisfiable. -/
theorem inputs_unsatisfiable
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    (refutation : ColoredClauseRefutation inputs) :
    inputs.Unsatisfiable := by
  rintro ⟨interpretation, satisfiesInputs⟩
  have satisfiesTrace := refutation.trace.sound interpretation (by
    intro clause leaf
    exact leaf.sound interpretation satisfiesInputs)
  exact Clause.not_satisfied_nil interpretation
    (satisfiesTrace Clausal.Clause.empty refutation.contradiction)

end ColoredClauseRefutation

end EUF
