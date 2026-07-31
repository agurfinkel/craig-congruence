-- SPDX-License-Identifier: MIT

import Archived.CongruenceGraph

/-!
A small checked example of the archived congruence-graph API, proving that the
conjunction `x = y` and `x ≠ y` is unsatisfiable.
-/

namespace EUF.Examples

inductive Function : Nat → Type
  | x : Function 0
  | y : Function 0

def exampleSignature : Signature where
  Function := Function

def x : Term exampleSignature := .constant .x
def y : Term exampleSignature := .constant .y

def contradictory : Formula exampleSignature :=
  [.eq x y, .ne x y]

def contradictoryGraph : CongruenceGraph contradictory where
  Edge left right := DerivesEq contradictory left right
  edge_derivable edge := edge

def contradictoryConflict : contradictoryGraph.Conflict where
  left := x
  right := y
  disequality := by simp [contradictory]
  connected := .edge (.assumption (by simp [contradictory]))

example : Unsatisfiable contradictory :=
  unsatisfiable_of_congruence_graph_conflict
    contradictoryGraph contradictoryConflict

end EUF.Examples
