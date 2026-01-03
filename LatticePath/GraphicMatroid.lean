import Mathlib.Data.Set.Defs
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import LatticePath.SpanningTree

open SimpleGraph

variable {V : Type _} {G : SimpleGraph V}

@[grind]
def SimpleGraph.Indep (s : Set <| Sym2 V) : Prop :=
  s ⊆ G.edgeSet ∧ (fromEdgeSet s).IsAcyclic

@[grind →]
lemma SimpleGraph.Indep.subset_ground {s} (hs : G.Indep s) : s ⊆ G.edgeSet := hs.1

@[grind →]
lemma SimpleGraph.Indep.isAcyclic_fromEdgeSet {s} (hs : G.Indep s) :
    (fromEdgeSet s).IsAcyclic := hs.2

lemma SimpleGraph.edgeSet_disjoint_diagSet : Disjoint G.edgeSet {e | e.IsDiag} := by
  grind [Set.disjoint_iff, not_isDiag_of_mem_edgeSet]

lemma SimpleGraph.Indep.disjoint_diagSet {s} (hs : G.Indep s) : Disjoint s {e | e.IsDiag} :=
  Disjoint.mono_left hs.subset_ground <| G.edgeSet_disjoint_diagSet

@[grind →]
theorem SimpleGraph.fromEdgeSet_le_of_subset_edgeSet {s : Set <| Sym2 V} (hs : s ⊆ G.edgeSet) :
    (fromEdgeSet s) ≤ G := by
  simp_rw [le_iff_adj, fromEdgeSet_adj, ←mem_edgeSet]
  grind

@[grind →]
theorem SimpleGraph.Indep.eq_fromEdgeSet_edgeSet {s : Set <| Sym2 V} (hs : G.Indep s) :
  (fromEdgeSet s).edgeSet = s := by
  rw [edgeSet_eq_iff]
  exact ⟨rfl, hs.disjoint_diagSet⟩

@[grind →]
lemma SimpleGraph.Indep.fromEdgeSet_le {s} (hs : G.Indep s) : (fromEdgeSet s) ≤ G :=
  fromEdgeSet_le_of_subset_edgeSet hs.subset_ground

theorem SimpleGraph.edgeSet_indep_iff {H : SimpleGraph V} :
    G.Indep H.edgeSet ↔ H ≤ G ∧ H.IsAcyclic := by
  simp [Indep]

theorem SimpleGraph.indep_empty : G.Indep ∅ := by simp [Indep]

theorem SimpleGraph.indep_subset {s t : Set <| Sym2 V} (ht : G.Indep t) (hst : s ⊆ t) :
    G.Indep s := by
  have : fromEdgeSet s ≤ fromEdgeSet t := fromEdgeSet_mono hst
  grind [IsAcyclic.anti]

theorem SimpleGraph.maximal_indep_iff_subset_edgeSet_and_maximal (s : Set <| Sym2 V) :
    Maximal G.Indep s ↔ s ⊆ G.edgeSet ∧ Maximal (fun H => H ≤ G ∧ H.IsAcyclic) (fromEdgeSet s) := by
  constructor
  · intro h
    refine ⟨h.prop.1, ⟨?_, h.prop.2⟩, ?_⟩
    · exact h.prop.fromEdgeSet_le
    · intro H hH hle
      have : G.Indep H.edgeSet := G.edgeSet_indep_iff.mpr hH
      rw [←edgeSet_subset_edgeSet, h.prop.eq_fromEdgeSet_edgeSet] at ⊢ hle
      exact h.le_of_ge this hle
  · intro ⟨hsub, hs⟩
    have hs_indep : G.Indep s := ⟨hsub, hs.prop.2⟩
    refine ⟨hs_indep, fun t ht_indep hle => ?_⟩
    simp_rw [Set.le_eq_subset]
    rw [←ht_indep.eq_fromEdgeSet_edgeSet, ←hs_indep.eq_fromEdgeSet_edgeSet, edgeSet_subset_edgeSet]
    apply hs.le_of_ge
    constructor
    · exact ht_indep.fromEdgeSet_le
    · exact ht_indep.isAcyclic_fromEdgeSet
    · exact fromEdgeSet_mono hle

theorem SimpleGraph.maximal_indep_iff_indep_and_reachable_eq (s : Set <| Sym2 V) :
    Maximal G.Indep s ↔ G.Indep s ∧ (fromEdgeSet s).Reachable = G.Reachable := by
  rw [G.maximal_indep_iff_subset_edgeSet_and_maximal]
  constructor
  · intro ⟨hsub, hmax⟩
    constructor
    · exact ⟨hsub, hmax.prop.2⟩
    · exact reachable_eq_of_maximal_acyclic _ hmax
  · intro ⟨hindep, hreach⟩
    constructor
    · exact hindep.subset_ground
    · refine maximal_acyclic_of_reachable_eq ⟨?_, ?_⟩ hreach
      · exact hindep.fromEdgeSet_le
      · exact hindep.isAcyclic_fromEdgeSet

theorem SimpleGraph.exists_adj_not_reachable_of_reachable_not_le (G H : SimpleGraph V)
    (h : ¬ G.Reachable ≤ H.Reachable) : ∃ (u v : V), G.Adj u v ∧ ¬ H.Reachable u v := by
  obtain ⟨u, v, ⟨p⟩, huvH⟩ : ∃ u v, G.Reachable u v ∧ ¬ H.Reachable u v := by
    contrapose! h
    simpa [LE.le]
  let s : Set V := H.connectedComponentMk u
  have hus : u ∈ s := ConnectedComponent.connectedComponentMk_mem
  have hvs : v ∉ s := huvH ∘ (H.connectedComponentMk u).reachable_of_mem_supp hus
  obtain ⟨⟨⟨u', v'⟩, huv : G.Adj u' v'⟩, -, hu : u' ∈ s, hv : v' ∉ s⟩ :=
    p.exists_boundary_dart s hus hvs
  use u', v', huv
  intro hcon
  replace hcon := ConnectedComponent.sound hcon
  suffices H.connectedComponentMk u' = s by
    apply hv
    simp_rw [← this, hcon]
    rfl
  simp_rw [s, SetLike.coe, ConnectedComponent.supp_inj, ← ConnectedComponent.mem_supp_iff]
  grind

theorem SimpleGraph.indep_aug {s t : Set <| Sym2 V} (hs : G.Indep s) (hs_max : ¬ Maximal G.Indep s)
    (ht : Maximal G.Indep t) : ∃ e ∈ t \ s, G.Indep (insert e s) := by
  rw [G.maximal_indep_iff_indep_and_reachable_eq] at ht hs_max
  push_neg at hs_max
  specialize hs_max hs
  obtain ⟨u, v, huvG, huvs⟩ :
      ∃ (u v : V), (fromEdgeSet t).Adj u v ∧ ¬ (fromEdgeSet s).Reachable u v := by
    apply exists_adj_not_reachable_of_reachable_not_le
    have : (fromEdgeSet s).Reachable ≤ G.Reachable := by
      intro u v
      apply Reachable.mono
      grind
    grind
  refine ⟨s(u, v), ⟨?_, ?_⟩, ?_, ?_⟩
  · rwa [←ht.1.eq_fromEdgeSet_edgeSet, mem_edgeSet]
  · contrapose! huvs
    apply Adj.reachable
    simpa [huvs] using huvG.ne
  · refine Set.insert_subset ?_ hs.subset_ground
    rw [mem_edgeSet]
    apply le_iff_adj (G := fromEdgeSet t) |>.mp
    · exact ht.1.fromEdgeSet_le
    · exact huvG
  · have : fromEdgeSet (insert s(u, v) s) = (fromEdgeSet s) ⊔ (fromEdgeSet {s(u, v)}) := by
      rw [←edgeSet_inj, edgeSet_sup, hs.eq_fromEdgeSet_edgeSet,
        edgeSet_fromEdgeSet, edgeSet_fromEdgeSet]
      have : ¬ s(u, v).IsDiag := by simpa using huvG.ne
      have : ∀ e ∈ s, ¬ e.IsDiag :=
        fun _ he hcon => (Set.disjoint_iff.mp hs.disjoint_diagSet) ⟨he, hcon⟩
      grind
    rw [this]
    have : DecidableEq V := Classical.decEq _
    exact add_edge_acyclic hs.isAcyclic_fromEdgeSet _ _ huvs

open Matroid

theorem SimpleGraph.indep_maximal (X : Set <| Sym2 V) (hX : X ⊆ G.edgeSet) :
    ExistsMaximalSubsetProperty G.Indep X := by
  intro s hs hsX
  obtain ⟨H, hle, hmax⟩ :=
    exists_maximal_acyclic_extension (fromEdgeSet_mono hsX) hs.isAcyclic_fromEdgeSet
  refine ⟨H.edgeSet, ?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rwa [←hs.eq_fromEdgeSet_edgeSet, edgeSet_subset_edgeSet]
  · rw [edgeSet_subset_edgeSet]
    trans fromEdgeSet X
    · exact hmax.prop.1
    · exact fromEdgeSet_le_of_subset_edgeSet hX
  · rw [fromEdgeSet_edgeSet]
    exact hmax.prop.2
  · have : _ := hmax.prop.1
    rw [←edgeSet_subset_edgeSet, edgeSet_fromEdgeSet] at this
    grind
  · intro t ⟨ht_indep, ht_subs⟩ hHt
    suffices fromEdgeSet t ≤ H by
      simpa [←edgeSet_subset_edgeSet, ht_indep.eq_fromEdgeSet_edgeSet] using this
    apply hmax.le_of_ge
    · exact ⟨fromEdgeSet_mono ht_subs, ht_indep.isAcyclic_fromEdgeSet⟩
    · rwa [←edgeSet_subset_edgeSet, ht_indep.eq_fromEdgeSet_edgeSet]

private def SimpleGraph.circuitIndepMatroid : IndepMatroid (Sym2 V) where
  E := G.edgeSet
  Indep := G.Indep
  indep_empty := G.indep_empty
  indep_subset _ _ := G.indep_subset
  indep_aug _ _:= G.indep_aug
  indep_maximal := G.indep_maximal
  subset_ground _ hs := hs.subset_ground

def SimpleGraph.circuitMatroid := G.circuitIndepMatroid.matroid

@[simp]
theorem SimpleGraph.circuitMatroid_E : G.circuitMatroid.E = G.edgeSet := rfl

@[simp]
theorem SimpleGraph.circuitMatroid_indep_iff (s : Set <| Sym2 V) :
    G.circuitMatroid.Indep s ↔ G.Indep s := by
  simp [circuitMatroid, circuitIndepMatroid]

@[simp]
theorem SimpleGraph.isBase_iff (B : Set <| Sym2 V) :
    G.circuitMatroid.IsBase B ↔ G.Indep B ∧ (fromEdgeSet B).Reachable = G.Reachable := by
  simp [circuitMatroid, circuitIndepMatroid, maximal_indep_iff_indep_and_reachable_eq]

theorem SimpleGraph.circuitMatroid_dep_iff (s : Set <| Sym2 V) :
    G.circuitMatroid.Dep s ↔ ¬(fromEdgeSet s).IsAcyclic ∧ s ⊆ G.edgeSet := by
  simp [dep_iff, circuitMatroid_indep_iff, Indep, imp_or]

theorem SimpleGraph.circuitMatroid_restrict_eq_of_le {H : SimpleGraph V} (h : H ≤ G) :
    G.circuitMatroid ↾ H.edgeSet = H.circuitMatroid := by
  apply ext_indep
    <;> grind [restrict_ground_eq, edgeSet_subset_edgeSet, restrict_indep_iff,
      circuitMatroid_indep_iff, Indep]

theorem SimpleGraph.circuitMatroid_restrict_eq_of_subset (X : Set <| Sym2 V) (h : X ⊆ G.edgeSet) :
    G.circuitMatroid ↾ X = (fromEdgeSet X).circuitMatroid := by
  apply ext_indep
  <;> grind [restrict_indep_iff, circuitMatroid_indep_iff, Indep, edgeSet_inf,
      edgeSet_fromEdgeSet, Set.subset_inter_iff, restrict_ground_eq, circuitMatroid_E,
      sdiff_eq_self_iff_disjoint, edgeSet_disjoint_diagSet, Set.disjoint_iff]
