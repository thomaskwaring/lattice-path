import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! Edges of a subgraph -/

lemma Subgraph.edgeSet_spanningCoe (G' : G.Subgraph) :
    G'.spanningCoe.edgeSet = G'.edgeSet := by grind

/-! Edges of a connected component -/

def ConnectedComponent.edgeSet (C : ConnectedComponent G) : Set (Sym2 V) :=
  ⋃ v ∈ C.supp, G.incidenceSet v

lemma ConnectedComponent.mem_edgeSet_iff (C : ConnectedComponent G) (e : Sym2 V) :
    e ∈ C.edgeSet ↔ e ∈ G.edgeSet ∧ ∃ v ∈ C.supp, v ∈ e := by
  simp_rw [ConnectedComponent.edgeSet, Set.mem_iUnion, mem_supp_iff, exists_prop, incidenceSet]
  grind

lemma exists_connectedComponent_of_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ C : G.ConnectedComponent, e ∈ C.edgeSet := by
  induction e with | h x y
  use G.connectedComponentMk x
  exact ConnectedComponent.mem_edgeSet_iff _ _ |>.mpr ⟨he, x, by simp⟩

lemma ConnectedComponent.eq_of_common_edge {e : Sym2 V} {c c' : G.ConnectedComponent}
    (hc : e ∈ c.edgeSet) (hc' : e ∈ c'.edgeSet) : c = c' := by
  induction e with | h x y
  simp_rw [mem_edgeSet_iff, mem_edgeSet, Sym2.mem_iff] at hc hc'
  obtain ⟨u, huc, hue⟩ := hc.2
  obtain ⟨v, hvc, hve⟩ := hc'.2
  have : u = v ∨ G.Adj u v := by grind [G.symm hc.1]
  apply ConnectedComponent.eq_of_common_vertex huc
  cases this
  case inl h => exact h ▸ hvc
  case inr h => rwa [c'.mem_supp_congr_adj h]

lemma pairwise_disjoint_edgeSet_connectedComponent (G : SimpleGraph V) :
    Pairwise fun c c' : G.ConnectedComponent => Disjoint c.edgeSet c'.edgeSet := by
  simp_rw [Set.disjoint_left]
  intro _ _ h _ he he'
  exact h <| ConnectedComponent.eq_of_common_edge he he'

lemma Sym2.exists_mem (e : Sym2 V) : ∃ v : V, v ∈ e := by cases e; simp

lemma iUnion_edgeSet_eq_edgeSet : ⋃ c : G.ConnectedComponent, c.edgeSet = G.edgeSet := by
  ext e
  simp [ConnectedComponent.mem_edgeSet_iff, Sym2.exists_mem]

theorem ConnectedComponent.edgeSet_eq_edgeSet_toSubgraph (c : G.ConnectedComponent) :
    c.toSubgraph.edgeSet = c.edgeSet := by
  ext e; cases e
  simp only [Subgraph.edgeSet, Sym2.fromRel, Set.mem_setOf_eq, Sym2.lift_mk, Subgraph.induce_adj,
    mem_supp_iff, Subgraph.top_adj, mem_edgeSet_iff, mem_edgeSet, Sym2.mem_iff]
  grind [connectedComponentMk_eq_of_adj]



end SimpleGraph
