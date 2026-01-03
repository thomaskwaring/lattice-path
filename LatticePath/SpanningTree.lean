import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SimpleGraph

variable {V : Type _} {G : SimpleGraph V}

theorem Walk.exists_mem_contains_edges_of_directed (Hs : Set <| SimpleGraph V) (hHs : Hs.Nonempty)
    (h_dir : DirectedOn (· ≤ ·) Hs) {u v : V} (p : (sSup Hs).Walk u v) :
    ∃ H ∈ Hs, ∀ e ∈ p.edges, e ∈ H.edgeSet := by
  induction p with
  | nil => exact ⟨hHs.some, hHs.some_mem, by simp⟩
  | @cons u v w h_adj p ih =>
    obtain ⟨H₁, hH₁, ih⟩ := ih
    obtain ⟨H₂, hH₂, h_adj⟩ : ∃ H₂ ∈ Hs, H₂.Adj u v := h_adj
    obtain ⟨H, hH, h₁, h₂⟩ := h_dir H₁ hH₁ H₂ hH₂
    simpa using ⟨H, hH, (le_iff_adj.mp h₂) _ _ h_adj, fun a ha => edgeSet_mono h₁ (ih a ha)⟩

theorem sSup_acyclic_of_directed_of_acyclic (Hs : Set <| SimpleGraph V)
    (h_acyc : ∀ H ∈ Hs, H.IsAcyclic) (h_dir : DirectedOn (· ≤ ·) Hs) : IsAcyclic (sSup Hs) := by
  rcases Hs.eq_empty_or_nonempty with hemp | hnemp
  · rw [hemp, sSup_empty]
    exact isAcyclic_bot
  · intro u p hp
    obtain ⟨H, hH, hpH⟩ := p.exists_mem_contains_edges_of_directed Hs hnemp h_dir
    exact h_acyc H hH (p.transfer H hpH) <| Walk.IsCycle.transfer hp hpH

theorem exists_maximal_acyclic_extension {H : SimpleGraph V} (hHG : H ≤ G) (hH : H.IsAcyclic) :
    ∃ H' : SimpleGraph V, H ≤ H' ∧ Maximal (fun H => H ≤ G ∧ H.IsAcyclic) H' := by
  let s : Set (SimpleGraph V) := {H : SimpleGraph V | H ≤ G ∧ H.IsAcyclic}
  apply zorn_le_nonempty₀ s
  · intro c hcs hc y hy
    refine ⟨sSup c, ⟨?_, ?_⟩, CompleteLattice.le_sSup c⟩
    · simp only [sSup_le_iff]
      grind
    · exact sSup_acyclic_of_directed_of_acyclic c (by grind) hc.directedOn
  · grind

theorem add_edge_acyclic [DecidableEq V] {G : SimpleGraph V} (hG : IsAcyclic G) (x y : V)
    (hxy : ¬ Reachable G x y) : IsAcyclic <| G ⊔ fromEdgeSet {s(x,y)} := by
  have x_neq_y : x ≠ y := fun c => (c ▸ hxy) (Reachable.refl y)
  have h_add_remove : (G ⊔ fromEdgeSet {s(x,y)}) \ fromEdgeSet {s(x,y)} = G := by
    simpa using fun h => hxy h.reachable
  have h_bridge : (G ⊔ fromEdgeSet {s(x,y)}).IsBridge s(x,y) := by
    simpa [isBridge_iff, x_neq_y, h_add_remove]
  intro u c hc
  apply isBridge_iff_adj_and_forall_cycle_notMem.mp at h_bridge
  let c' : G.Walk u u := Walk.transfer c G (by
    intro e he
    have eneq : e ≠ s(x,y) := fun h => h_bridge.2 c hc (h ▸ he)
    simpa [eneq] using Walk.edges_subset_edgeSet c he
  )
  exact hG c' (Walk.IsCycle.transfer (qc := hc) ..)

theorem reachable_eq_of_maximal_acyclic (F : SimpleGraph V)
    (h : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) F) : F.Reachable = G.Reachable := by
  simp only [Maximal, and_imp] at h
  obtain ⟨hF, h⟩ := h
  apply funext; intro u; apply funext; intro v
  refine propext ⟨fun hr => hr.mono hF.1, ?_⟩
  contrapose! h
  obtain ⟨p⟩ := h.1
  let s : Set V := F.connectedComponentMk u
  have hus : u ∈ s := ConnectedComponent.connectedComponentMk_mem
  have hvs : v ∉ s := h.2 ∘ (F.connectedComponentMk u).reachable_of_mem_supp hus
  obtain ⟨⟨⟨u', v'⟩, huv⟩, _, hu, hv⟩ := p.exists_boundary_dart s hus hvs
  let F' := (F ⊔ fromEdgeSet {s(u', v')})
  suffices F'.IsAcyclic by
    rw [le_iff_adj] at hF
    refine ⟨F', ?_, this, le_sup_left, ?_⟩
    · have : G.Adj v' u' := G.symm huv
      simp only [sup_le_iff, le_iff_adj, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, ne_eq, and_imp, F']
      grind
    · rw [le_iff_adj]
      push_neg
      refine ⟨u', v', ?_, ?_⟩
      · simpa [F'] using Or.inr huv.ne
      · intro hc
        have : _ := ConnectedComponent.mem_supp_congr_adj (F.connectedComponentMk u) hc
        grind
  have : DecidableEq V := Classical.decEq V
  apply add_edge_acyclic (hG := hF.2)
  intro hc
  rw [←ConnectedComponent.eq] at hc
  suffices F.connectedComponentMk u' = s by
    exact (hc ▸ this ▸ hv) ConnectedComponent.connectedComponentMk_mem
  simp_rw [s, SetLike.coe, ConnectedComponent.supp_inj, ←ConnectedComponent.mem_supp_iff]
  grind

theorem maximal_acyclic_of_reachable_eq {F : SimpleGraph V} (hF : F ≤ G ∧ F.IsAcyclic)
    (h : F.Reachable = G.Reachable) : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) F := by
  by_contra!
  obtain ⟨F', hF'⟩ := exists_gt_of_not_maximal (P := fun H => H ≤ G ∧ H.IsAcyclic) hF this
  obtain ⟨e, he⟩ := Set.exists_of_ssubset <| edgeSet_strict_mono hF'.1
  have : (F ⊔ fromEdgeSet {e}).IsAcyclic := by
    apply hF'.2.2.anti
    refine sup_le_iff.mpr ⟨by grind, ?_⟩
    rw [←F'.fromEdgeSet_edgeSet]
    grind [fromEdgeSet_mono]
  have e_ndiag : ¬ e.IsDiag := F'.edgeSet_subset_setOf_not_isDiag he.1
  have F_sdiff_eq : (F ⊔ fromEdgeSet {e}) \ fromEdgeSet {e} = F := by
    simpa using he.2
  have h_bridge : (F ⊔ fromEdgeSet {e}).IsBridge e := by
    apply isAcyclic_iff_forall_edge_isBridge.mp this
    simpa using Or.inr e_ndiag
  simp only [IsBridge, F_sdiff_eq] at h_bridge
  cases e
  case h u v =>
    simp only [Sym2.lift_mk] at h_bridge
    suffices G.Reachable u v by exact (h ▸ h_bridge.2) this
    apply Reachable.mono hF'.2.1
    apply Adj.reachable
    simpa using he.1

/-- Every graph has a spanning forest. -/
theorem exists_extension_acyclic_reachable_eq {H : SimpleGraph V} (hHG : H ≤ G)
    (hH : H.IsAcyclic) : ∃ F ≤ G, H ≤ F ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable := by
  obtain ⟨F, hHF, hF⟩ := exists_maximal_acyclic_extension hHG hH
  exact ⟨F, hF.1.1, hHF, hF.1.2, reachable_eq_of_maximal_acyclic F hF⟩

theorem Connected.connected_of_maximal_acyclic (T : SimpleGraph V) (hG : G.Connected)
    (h : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) T) : T.Connected := by
  have : Nonempty V := hG.nonempty
  refine ⟨fun u v => ?_⟩
  rw [reachable_eq_of_maximal_acyclic T h]
  exact hG u v

theorem Connected.exists_extension_isTree_le (hG : G.Connected) {H : SimpleGraph V} (hHG : H ≤ G)
  (hH : H.IsAcyclic) : ∃ T ≤ G, H ≤ T ∧ T.IsTree := by
  obtain ⟨T, hHT, hT⟩ := exists_maximal_acyclic_extension hHG hH
  exact ⟨T, hT.1.1, hHT, hG.connected_of_maximal_acyclic T hT, hT.1.2⟩


end SimpleGraph
