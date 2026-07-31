-- SPDX-License-Identifier: MIT

import Basic.Clause

/-!
Colored clausal representations for the two-part interpolation setting.
`ColoredClause` partitions literal occurrences, while `ColoredCNF` partitions
input clauses and records their color correctness.
-/

namespace EUF

/-- A coloring of a clause assigns every literal occurrence to one formula
position. Shared literals may be put in either part; a local literal can only
be put in its owning part because of `part_color`.

Keeping the two parts separately is also exactly what is needed to negate the
clause into the pair of conjunctive inputs used for theory interpolation. -/
structure ColoredClause (sig : ColoredSignature 2) where
  part : Fin 2 → Clause sig.toSignature
  part_color : ∀ partition, Formula.IsColor sig partition (part partition)

namespace ColoredClause

/-- The underlying disjunctive clause, forgetting ownership. -/
def literals (clause : ColoredClause sig) : Clause sig.toSignature :=
  clause.part 0 ++ clause.part 1

/-- The conjunction which falsifies the literals owned by one color. -/
def falsifyingPart (clause : ColoredClause sig) (partition : Fin 2) :
  Formula sig.toSignature :=
  (clause.part partition).map Literal.negate

theorem falsifyingPart_color (clause : ColoredClause sig) (partition : Fin 2) :
  Formula.IsColor sig partition (clause.falsifyingPart partition) := by
  intro literal member
  simp only [falsifyingPart, List.mem_map] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  have originalColor := clause.part_color partition original originalMember
  exact ⟨(Literal.colorable_negate_iff sig original).mpr originalColor.1,
    (Literal.availableIn_negate_iff sig partition original).mpr originalColor.2⟩

end ColoredClause

/-- A two-part clausal EUF input. Every clause in a part contains only local
symbols of that part and symbols shared across boundary `0`. -/
structure ColoredCNF (sig : ColoredSignature 2) where
  part : Fin 2 → CNF sig.toSignature
  part_color : ∀ partition clause, clause ∈ part partition →
    Formula.IsColor sig partition clause

namespace ColoredCNF

def Satisfied (inputs : ColoredCNF sig)
  (interpretation : Interpretation sig.toSignature) : Prop :=
  ∀ partition, (inputs.part partition).Satisfied interpretation

def Satisfiable (inputs : ColoredCNF sig) : Prop :=
  ∃ interpretation : Interpretation sig.toSignature,
    inputs.Satisfied interpretation

def Unsatisfiable (inputs : ColoredCNF sig) : Prop :=
  ¬inputs.Satisfiable

end ColoredCNF

end EUF
