-- SPDX-License-Identifier: MIT

import CongruenceClosure.EquationalTheory

/-!
Certified congruence graphs, undirected path connectivity, and their semantic
soundness. The final theorem turns a path connecting the endpoints of an input
disequality into an EUF unsatisfiability certificate.
-/

namespace EUF

/-- A congruence graph consists of edges certified by congruence-closure
derivations from the cube's equality literals. -/
structure CongruenceGraph (formula : Cube σ) where
  Edge : Term σ → Term σ → Prop
  edge_derivable :
    ∀ {left right}, Edge left right → DerivesEq formula left right

/-- Undirected path connectivity in a congruence graph. -/
inductive CongruenceGraph.Connected
    {σ : Signature} {formula : Cube σ}
    (graph : CongruenceGraph formula) : Term σ → Term σ → Prop where
  | refl (term) : graph.Connected term term
  | edge {left right} : graph.Edge left right → graph.Connected left right
  | symm {left right} :
      graph.Connected left right → graph.Connected right left
  | trans {left middle right} :
      graph.Connected left middle →
      graph.Connected middle right →
      graph.Connected left right

theorem CongruenceGraph.connected_sound
    (graph : CongruenceGraph formula)
    (satisfies : Satisfies interpretation formula)
    (connected : graph.Connected left right) :
    interpretation.eval left = interpretation.eval right := by
  induction connected with
  | refl => rfl
  | edge edge =>
      exact (graph.edge_derivable edge).sound satisfies
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- A graph conflicts with a cube when it connects the two sides of one of
the cube's disequalities. -/
structure CongruenceGraph.Conflict
    {σ : Signature} {formula : Cube σ}
    (graph : CongruenceGraph formula) where
  left : Term σ
  right : Term σ
  disequality : Literal.ne left right ∈ formula
  connected : graph.Connected left right

/-- A congruence graph that disagrees with an asserted disequality is a
certificate that the conjunction is unsatisfiable. -/
theorem unsatisfiable_of_congruence_graph_conflict
    (graph : CongruenceGraph formula)
    (conflict : graph.Conflict) :
    Unsatisfiable formula := by
  rintro ⟨interpretation, satisfies⟩
  have equal :
      interpretation.eval conflict.left =
        interpretation.eval conflict.right :=
    graph.connected_sound satisfies conflict.connected
  have notEqual :
      interpretation.eval conflict.left ≠
        interpretation.eval conflict.right :=
    satisfies _ conflict.disequality
  exact notEqual equal

end EUF
