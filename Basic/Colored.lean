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
  part : Fin 2 → Clause sig
  part_color : ∀ partition, Clause.IsColor sig partition (part partition)

namespace ColoredClause

/-- The underlying disjunctive clause, forgetting ownership. -/
def toClause (clause : ColoredClause sig) : Clause sig :=
  Clausal.Clause.append (clause.part 0) (clause.part 1)

/-- The conjunction which falsifies the literals owned by one color. -/
def falsifyingPart (clause : ColoredClause sig) (partition : Fin 2) :
  Cube sig :=
  Clause.falsifyingCube (clause.part partition)

theorem falsifyingPart_color (clause : ColoredClause sig) (partition : Fin 2) :
  Cube.IsColor sig partition (clause.falsifyingPart partition) := by
  intro literal member
  change literal ∈ Cube.mapLiterals
    (Cube.ofList (Clausal.Clause.literals (clause.part partition)))
      Literal.negate at member
  rw [Cube.mem_mapLiterals_iff] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  have originalColor := clause.part_color partition original (by
    simpa using originalMember)
  exact ⟨(Literal.colorable_negate_iff sig original).mpr originalColor.1,
    (Literal.availableIn_negate_iff sig partition original).mpr originalColor.2⟩

end ColoredClause

/-- A two-part clausal EUF input. Every clause in a part contains only local
symbols of that part and symbols shared across boundary `0`. -/
structure ColoredCNF (sig : ColoredSignature 2) where
  part : Fin 2 → CNF sig
  part_color : ∀ partition clause, clause ∈ part partition →
    Clause.IsColor sig partition clause

namespace ColoredCNF

def Satisfied (inputs : ColoredCNF sig)
  (interpretation : Interpretation sig) : Prop :=
  ∀ partition, (inputs.part partition).Satisfied interpretation

def Satisfiable (inputs : ColoredCNF sig) : Prop :=
  ∃ interpretation : Interpretation sig,
    inputs.Satisfied interpretation

def Unsatisfiable (inputs : ColoredCNF sig) : Prop :=
  ¬inputs.Satisfiable

end ColoredCNF

end EUF
