import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Combinatorics.Enumerative.Partition

variable {α β : Type*}
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

def equivPartitionSorted {n : Nat} :
    n.Partition ≃
    {l : {w : List Nat // List.Sorted (fun (x1 x2 : ℕ) => x1 ≥ x2) w ∧ ∀ x ∈ w, 0 < x } //
      l.val.sum = n} where
  toFun μ := ⟨⟨μ.parts.sort (· ≥ ·), μ.parts.sort_sorted _,
    by intro i; rw [Multiset.mem_sort]; exact μ.parts_pos⟩,
    by grind [Multiset.sort_eq, Multiset.sum_coe, Nat.Partition.parts_sum]⟩
  invFun l := ⟨l, by grind [Multiset.mem_coe], by grind [Multiset.sum_coe]⟩
  left_inv μ := by
    rw [Nat.Partition.ext_iff]
    exact μ.parts.sort_eq _
  right_inv l := by grind [Multiset.coe_sort, List.mergeSort_eq_self]

theorem YoungDiagram.cells_eq_union_rows (μ : YoungDiagram) :
    μ.cells = (Finset.range <| μ.colLen 0).biUnion μ.row := by
  ext ⟨i, j⟩
  simp only [mem_cells, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · intro h
    refine ⟨i, ?_, μ.mk_mem_row_iff.mpr h⟩
    suffices ⟨i, 0⟩ ∈ μ by exact μ.mem_iff_lt_colLen.mp this
    refine μ.isLowerSet (a := ⟨i, j⟩) ?_ h
    simp
  · intro ⟨i', hi⟩
    grind [YoungDiagram.mem_row_iff]

theorem YoungDiagram.card_eq_sum_rowLens (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  rw [YoungDiagram.rowLens, YoungDiagram.card, μ.cells_eq_union_rows, Finset.card_biUnion]
  · have : ∀ i ∈ Finset.range (μ.colLen 0), (μ.row i).card = μ.rowLen i := by
      grind [YoungDiagram.rowLen_eq_card]
    rw [Finset.sum_congr rfl this, Finset.sum_list_map_count, List.toFinset_range]
    apply Finset.sum_congr rfl
    intro i hi
    suffices List.count i (List.range (μ.colLen 0)) = 1 by rw [this]; simp
    simpa using hi
  · intro i hi i' hi' hneq
    rw [Function.onFun, Finset.disjoint_iff_inter_eq_empty, YoungDiagram.row_eq_prod,
      YoungDiagram.row_eq_prod]
    grind

theorem YoungDiagram.card_cellsOfRowLens (w : List Nat) :
    (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons w ws ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint, List.sum_cons]
    · congr
      · simp
      · simpa
    · simp only [Finset.disjoint_iff_ne, Finset.singleton_product, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk, Function.Embedding.coe_prodMap, Prod.exists, Prod.map_apply,
        Nat.succ_eq_add_one, Function.Embedding.refl_apply, ne_eq, forall_exists_index, and_imp,
        Prod.forall, Prod.mk.injEq, forall_apply_eq_imp_iff₂, not_and]
      grind

theorem YoungDiagram.card_ofRowLens (w : List Nat) (hw : w.Sorted (· ≥ ·)) :
    (YoungDiagram.ofRowLens w hw).card = w.sum := by
  rw [YoungDiagram.ofRowLens, YoungDiagram.card, YoungDiagram.card_cellsOfRowLens]

def equivPartitionYoung {n : Nat} : n.Partition ≃ {μ : YoungDiagram // μ.card = n} :=
  equivPartitionSorted.trans <| YoungDiagram.equivListRowLens.symm.subtypeEquiv (by
    intro ⟨w, _⟩
    rw [YoungDiagram.equivListRowLens_symm_apply, YoungDiagram.card_ofRowLens]
  )
