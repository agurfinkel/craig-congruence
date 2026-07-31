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
structure ColoredClause (colored : ColoredSignature 2) where
  part : Fin 2 → Clause colored.toSignature
  part_color : ∀ i, Formula.IsColor colored i (part i)

namespace ColoredClause

/-- The underlying disjunctive clause, forgetting ownership. -/
def literals (clause : ColoredClause colored) : Clause colored.toSignature :=
  clause.part 0 ++ clause.part 1

/-- The conjunction which falsifies the literals owned by one color. -/
def falsifyingPart (clause : ColoredClause colored) (side : Fin 2) :
    Formula colored.toSignature :=
  (clause.part side).map Literal.negate

theorem falsifyingPart_color (clause : ColoredClause colored) (side : Fin 2) :
    Formula.IsColor colored side (clause.falsifyingPart side) := by
  intro literal member
  simp only [falsifyingPart, List.mem_map] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  have originalColor := clause.part_color side original originalMember
  exact ⟨(Literal.colorable_negate_iff colored original).mpr originalColor.1,
    (Literal.availableIn_negate_iff colored side original).mpr originalColor.2⟩

end ColoredClause

/-- A two-part clausal EUF input. Every clause in a part contains only local
symbols of that part and symbols shared across boundary `0`. -/
structure ColoredCNF (colored : ColoredSignature 2) where
  part : Fin 2 → CNF colored.toSignature
  part_color : ∀ side clause, clause ∈ part side →
    Formula.IsColor colored side clause

namespace ColoredCNF

def Satisfied (inputs : ColoredCNF colored)
    (interpretation : Interpretation colored.toSignature) : Prop :=
  ∀ side, (inputs.part side).Satisfied interpretation

def Satisfiable (inputs : ColoredCNF colored) : Prop :=
  ∃ interpretation : Interpretation colored.toSignature,
    inputs.Satisfied interpretation

def Unsatisfiable (inputs : ColoredCNF colored) : Prop :=
  ¬inputs.Satisfiable

end ColoredCNF

end EUF
