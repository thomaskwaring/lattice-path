import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SimpleGraph

variable {V : Type _} {G : SimpleGraph V}

theorem Connected.subset_connected_complement (h : G.Connected) (s : Set V) (hs : s.Nonempty) :
    s = Set.univ ∨ ∃ (u v : V), u ∈ s ∧ v ∉ s ∧ G.Adj u v := by
  simp_rw [Classical.or_iff_not_imp_left, Set.ne_univ_iff_exists_notMem]
  intro ⟨v, hv⟩
  obtain ⟨u, hu⟩ := hs
  obtain ⟨p⟩ := h u v
  have : DecidablePred (· ∉ s) := fun _ => Classical.propDecidable _
  let i : ℕ := List.findIdx (fun u ↦ decide (u ∉ s)) p.support
  have : v ∈ p.support := Walk.end_mem_support p
  have : i < p.support.length := by grind
  have : p.support[0] = u := by
    rw [←p.getVert_eq_support_getElem] <;> grind [Walk.getVert_zero]
  have : 0 < i := by apply List.lt_findIdx_of_not <;> grind
  refine ⟨p.support[i-1], p.support[i], by grind, by grind, ?_⟩
  rw [show p.support[i] = p.support[i-1 + 1] by grind]
  exact p.isChain_adj_support.getElem ..

theorem Walk.shrink_of_directed_sSup (Hs : Set <| SimpleGraph V) (H₀ : Hs)
    (h_dir : DirectedOn (· ≤ ·) Hs) {u v : V} (p : (sSup Hs).Walk u v) :
    ∃ H ∈ Hs, ∃ (p' : H.Walk u v),
      p'.edges = p.edges ∧ p'.support = p.support := by
  induction p with
  | nil => refine ⟨H₀, by grind, Walk.nil, by simp⟩
  | @cons u v w h_adj p ih =>
    obtain ⟨H₁, hH₁, p', hp'⟩ := ih
    rw [sSup_adj] at h_adj
    replace ⟨H₂, hH₂, h_adj⟩ : ∃ H₂ ∈ Hs, H₂.Adj u v := h_adj
    obtain ⟨H, hH, h⟩ := h_dir H₁ hH₁ H₂ hH₂
    let p'' : H.Walk v w := Walk.map (Hom.ofLE h.1) p'
    have : p''.edges = p'.edges ∧ p''.support = p'.support := by simp [p'']
    have : H.Adj u v := by grind [SimpleGraph.le_iff_adj]
    exact ⟨H, hH, Walk.cons this p'', by grind [support_cons, edges_cons]⟩

theorem sSup_acyclic_of_directed_of_acyclic (Hs : Set <| SimpleGraph V) (H₀ : Hs)
    (h_acyc : ∀ H ∈ Hs, H.IsAcyclic) (h_dir : DirectedOn (· ≤ ·) Hs) : IsAcyclic (sSup Hs) := by
  intro u p hp
  obtain ⟨H, hH, p', hp'⟩ := p.shrink_of_directed_sSup Hs H₀ h_dir
  suffices p'.IsCycle by exact (h_acyc H) hH p' this
  rw [Walk.isCycle_def, Walk.isTrail_def] at hp ⊢
  refine ⟨by grind, ?_, by grind⟩
  rw [ne_eq, ←Walk.nil_iff_eq_nil, Walk.nil_iff_support_eq] at hp ⊢
  grind

theorem exists_maximal_acyclic_extension {H : SimpleGraph V} (hHG : H ≤ G) (hH : H.IsAcyclic) :
    ∃ H' : SimpleGraph V, H ≤ H' ∧ Maximal (fun H => H ≤ G ∧ H.IsAcyclic) H' := by
  let s : Set (SimpleGraph V) := {H : SimpleGraph V | H ≤ G ∧ H.IsAcyclic}
  apply zorn_le_nonempty₀ s
  · intro c hcs hc y hy
    refine ⟨sSup c, ⟨?_, ?_⟩, CompleteLattice.le_sSup c⟩
    · simp only [sSup_le_iff]
      grind
    · exact sSup_acyclic_of_directed_of_acyclic c ⟨y, hy⟩ (by grind) hc.directedOn
  · grind

theorem add_edge_acyclic [DecidableEq V] {G : SimpleGraph V} (hG : IsAcyclic G) (x y : V)
    (hxy : ¬ Reachable G x y) : IsAcyclic <| G ⊔ fromEdgeSet {s(x,y)} := by
  have x_neq_y : x ≠ y := fun c => (c ▸ hxy) (Reachable.refl y)
  have h_add_remove : G = (G ⊔ fromEdgeSet {s(x,y)}) \ fromEdgeSet {s(x,y)} := by
    simp only [sup_sdiff_right_self]
    apply edgeSet_inj.mp; ext e;
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_diff,
      Set.mem_singleton_iff, iff_self_and]
    intro he c
    rw [c, mem_edgeSet] at he
    exact hxy <| Adj.reachable he
  have h_bridge : (G ⊔ fromEdgeSet {s(x,y)}).IsBridge s(x,y) := by
    simpa [isBridge_iff, x_neq_y, ←h_add_remove]
  intro u c hc
  apply isBridge_iff_adj_and_forall_cycle_notMem.mp at h_bridge
  let c' : G.Walk u u := Walk.transfer c G (by
    intro e he
    have eneq : e ≠ s(x,y) := fun h => h_bridge.2 c hc (h ▸ he)
    simpa [eneq] using Walk.edges_subset_edgeSet c he
  )
  exact hG c' (Walk.IsCycle.transfer (qc := hc) ..)

theorem Connected.connected_of_maximal_acyclic [Inhabited V] (T : SimpleGraph V) (hG : G.Connected)
    (h : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) T) : T.Connected := by
  rw [connected_iff_exists_forall_reachable]
  simp only [Maximal, and_imp] at h
  obtain ⟨hT, h⟩ := h
  contrapose! h
  let ⟨v, hv⟩ := h default
  let s : Set V := T.connectedComponentMk default
  have hus : default ∈ s := ConnectedComponent.connectedComponentMk_mem
  have hvs : v ∉ s := by
    intro hvs
    apply hv
    apply ConnectedComponent.reachable_of_mem_supp (T.connectedComponentMk default)
    all_goals grind
  obtain foo := Connected.subset_connected_complement hG s ⟨default, hus⟩
  rcases foo with _ | ⟨u', v', huv⟩
  · grind
  · let T' := (T ⊔ fromEdgeSet {s(u', v')})
    suffices T'.IsAcyclic by
      rw [le_iff_adj] at hT
      refine ⟨T', ?_, this, le_sup_left, ?_⟩
      · have : G.Adj v' u' := G.symm huv.2.2
        simp only [sup_le_iff, le_iff_adj, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, ne_eq, and_imp, T']
        grind
      · rw [le_iff_adj]
        push_neg
        refine ⟨u', v', ?_, ?_⟩
        · simp only [sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff, ne_eq, true_and, T']
          grind
        · intro hc
          have : _ := ConnectedComponent.mem_supp_congr_adj (T.connectedComponentMk default) hc
          grind
    simp_rw [T']
    have : DecidableEq V := Classical.decEq V
    apply add_edge_acyclic (hG := hT.2)
    intro hc
    rw [←ConnectedComponent.eq] at hc
    suffices T.connectedComponentMk u' = s by
      exact (hc ▸ this ▸ huv.2.1) ConnectedComponent.connectedComponentMk_mem
    simp_rw [s, SetLike.coe, ConnectedComponent.supp_inj, ←ConnectedComponent.mem_supp_iff]
    grind

theorem Connected.has_spanning_tree [Inhabited V] (hG : G.Connected) {H : SimpleGraph V}
    (hHG : H ≤ G) (hH : H.IsAcyclic) : ∃ T ≤ G, H ≤ T ∧ T.IsTree := by
  obtain ⟨T, hHT, hT⟩ := exists_maximal_acyclic_extension hHG hH
  exact ⟨T, hT.1.1, hHT, hG.connected_of_maximal_acyclic T hT, hT.1.2⟩


end SimpleGraph
