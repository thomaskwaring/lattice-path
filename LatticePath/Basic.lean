import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.Set.Card.Arithmetic

set_option linter.translateExisting false

@[to_additive existing]
def prodPathsTo {α} [Mul α] [One α] (gs : Set α) (a : α) : Set (List α) :=
  {l : List α | (∀ x ∈ l, x ∈ gs) ∧ l.prod = a}

section

variable {α} [Mul α] [One α] (gs : Set α)

@[to_additive existing]
theorem nil_mem_prodPathsTo (a : α) : [] ∈ prodPathsTo gs a ↔ a = 1 := by
  rw [eq_comm]
  simp [prodPathsTo]

@[to_additive existing]
theorem cons_mem_prodPathsTo (g a : α) (l : List α) :
    g :: l ∈ prodPathsTo gs a ↔ g ∈ gs ∧ (∀ x ∈ l, x ∈ gs) ∧ g * l.prod = a := by
  rw [←and_assoc]
  simp [prodPathsTo]

@[to_additive existing]
theorem prodPathsTo_disjoint (a b : α) (h : a ≠ b) :
    Disjoint (prodPathsTo gs a) (prodPathsTo gs b) := by
  rw [Set.disjoint_iff]
  grind [prodPathsTo]

@[to_additive existing]
theorem prodPathsTo_union (a : α) (ha : a ≠ 1) :
    prodPathsTo gs a = ⋃ (g : gs), ⋃ (a' : {a' : α // g * a' = a}),
      (fun l : List α => (g : α) :: l)'' (prodPathsTo gs a') := by
  ext l
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_image, Subtype.exists, exists_prop]
  constructor
  · intro ⟨hl_gs, hla⟩
    have : l ≠ [] := by grind [List.prod_nil]
    obtain ⟨g, l', hl'⟩ := List.exists_cons_of_ne_nil this
    have : g ∈ gs := by grind
    refine ⟨g, this, l'.prod, ?_, l', ?_, ?_⟩
    · rw [←hla, hl']
      simp
    all_goals grind [prodPathsTo]
  · intro h
    rcases h with ⟨g, hg, a', rfl, l', ⟨hl'_gs, rfl⟩, rfl⟩
    constructor
    · grind
    · exact List.prod_cons

@[to_additive existing]
noncomputable def numProdPathsTo (a : α) : ENat := (prodPathsTo gs a).encard

@[to_additive existing]
theorem numProdPathsTo_sum [Finite ↑gs] (a : α) (h_fin : ∀ g : gs, Finite {a' : α // g * a' = a})
    (ha : a ≠ 1) :
    numProdPathsTo gs a = ∑ᶠ (g : gs), ∑ᶠ (a' : {a' : α // g * a' = a}), numProdPathsTo gs a' := by
  rw [numProdPathsTo, prodPathsTo_union _ _ ha, Set.encard_iUnion_of_finite]
  · congr
    ext g
    rw [Set.encard_iUnion_of_finite]
    · congr
      ext a'
      rw [numProdPathsTo, Function.Injective.encard_image List.cons_injective]
    · intro a' b' hab
      have : (↑a' : α) ≠ ↑b' := by grind
      simpa using prodPathsTo_disjoint gs a' b' this
  · intro g g' hgs
    rw [Function.onFun, Set.disjoint_iff]
    intro l hl
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_image, Subtype.exists, exists_prop,
      Set.mem_empty_iff_false] at hl ⊢
    grind



end
