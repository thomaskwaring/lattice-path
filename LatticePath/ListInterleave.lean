import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.Fintype.Inv

open List

@[grind cases, grind]
inductive IsInterleaving {α : Type _} : List α → List α → List α → Prop where
  | nil : IsInterleaving [] [] []
  | left (a : α) (xs ys zs : List α) :
    IsInterleaving xs ys zs → IsInterleaving (a :: xs) ys (a :: zs)
  | right (a : α) (xs ys zs : List α) :
    IsInterleaving xs ys zs → IsInterleaving xs (a :: ys) (a :: zs)

@[grind .]
theorem isInterleaving_comm {α : Type _} (xs ys zs : List α) (h : IsInterleaving xs ys zs) :
  IsInterleaving ys xs zs := by
  induction h with
  | nil => exact .nil
  | left _ _ _ _ _ ih => exact .right _ _ _ _ ih
  | right _ _ _ _ _ ih => exact .left _ _ _ _ ih

@[grind .]
theorem isInterleaving_self_nil {α : Type _} (xs : List α) : IsInterleaving xs [] xs := by
  induction xs <;> grind

@[grind =]
theorem isInterleaving_nil_left {α : Type _} (xs zs : List α) :
    IsInterleaving xs [] zs ↔ xs = zs := by
  constructor
  · intro h
    cases h
    case nil => trivial
    case left a xs zs h => simp [(isInterleaving_nil_left xs zs).mp h]
  · grind

@[grind .]
theorem isInterleaving_nil_self {α : Type _} (xs : List α) : IsInterleaving [] xs xs := by grind

@[grind =]
theorem isInterleaving_nil_right {α : Type _} (xs zs : List α) :
    IsInterleaving [] xs zs ↔ xs = zs := by grind

theorem nil_isInterleaving {α : Type _} (xs ys : List α) :
    IsInterleaving xs ys [] ↔ xs = [] ∧ ys = [] := by grind

@[reducible]
def isInterleavingBool {α : Type _} [DecidableEq α] : List α → List α → List α → Bool
  | [], ys, zs => ys == zs
  | xs, [], zs => xs == zs
  | (_ :: _), (_ :: _), [] => false
  | (x :: xs), (y :: ys), (z :: zs) =>
    (x == z && isInterleavingBool xs (y :: ys) zs) || (y == z && isInterleavingBool (x :: xs) ys zs)

theorem isInterleaving_iff {α : Type _} [DecidableEq α] :
    (xs ys zs: List α) → isInterleavingBool xs ys zs ↔ IsInterleaving xs ys zs
  | xs, [], zs => by
    unfold isInterleavingBool
    grind
  | [], ys, zs => by
    unfold isInterleavingBool
    grind
  | (x :: xs), (y :: ys), [] => by
    unfold isInterleavingBool
    grind
  | (x :: xs), (y :: ys), (z :: zs) => by
    unfold isInterleavingBool
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    constructor <;> intro h
    · cases h
      case inl h =>
        rw [h.1]
        apply IsInterleaving.left
        exact isInterleaving_iff xs (y :: ys) zs |>.mp h.2
      case inr h =>
        rw [h.1]
        apply IsInterleaving.right
        exact isInterleaving_iff (x :: xs) ys zs |>.mp h.2
    · cases h
      case left h =>
        exact Or.inl ⟨rfl, isInterleaving_iff xs (y :: ys) zs |>.mpr h⟩
      case right h =>
        exact Or.inr ⟨rfl, isInterleaving_iff (x :: xs) ys zs |>.mpr h⟩

instance instDecidableIsInterleaving {α : Type _} [DecidableEq α] (xs ys zs : List α) :
    Decidable <| IsInterleaving xs ys zs :=
  decidable_of_bool (isInterleavingBool xs ys zs) (isInterleaving_iff xs ys zs)

@[grind →]
theorem length_isInterleaving {α : Type _} (xs ys zs : List α) (h : IsInterleaving xs ys zs) :
  zs.length = xs.length + ys.length := by induction h <;> grind

@[grind →]
theorem perm_append_of_isInterleaving {α : Type _} (xs ys zs : List α)
    (h : IsInterleaving xs ys zs) : zs ~ (xs ++ ys) := by
  induction h with
  | nil => simp
  | left a xs ys zs h ih =>
    rw [List.cons_append]
    exact List.Perm.cons a ih
  | right a xs ys zs h ih =>
    rw [List.append_cons]
    trans [a] ++ xs ++ ys
    · rw [List.append_assoc]
      simpa
    · apply List.Perm.append_right
      exact List.perm_append_comm

def interleavings {α : Type _} [DecidableEq α] (xs ys : List α) : Finset (List α) := by
  refine Finset.filter (IsInterleaving xs ys) <| List.toFinset (xs ++ ys).permutations

@[grind =, simp]
theorem mem_interleavings_iff {α : Type _} [DecidableEq α] (xs ys zs : List α) :
    zs ∈ interleavings xs ys ↔ IsInterleaving xs ys zs := by
  simpa [interleavings] using perm_append_of_isInterleaving xs ys zs

instance instFintypeSubtypeIsInterleaving {α : Type _} [DecidableEq α] (xs ys : List α) :
    Fintype {zs : List α // IsInterleaving xs ys zs} := by
  apply Fintype.subtype (s := interleavings xs ys)
  simp

@[simp]
theorem interleavings_nil {α : Type _} [DecidableEq α] (xs : List α) :
    interleavings xs [] = {xs} := by grind

@[simp]
theorem nil_interleavings {α : Type _} [DecidableEq α] (xs : List α) :
    interleavings [] xs = {xs} := by grind

theorem partition_interleavings {α : Type _} [DecidableEq α] (x y : α) (xs ys : List α) :
    interleavings (x :: xs) (y :: ys) =
      Finset.image (x :: ·) (interleavings xs (y :: ys)) ∪
      Finset.image (y :: ·) (interleavings (x :: xs) ys) := by
    ext l
    simp only [Finset.mem_union, Finset.mem_image, mem_interleavings_iff]
    constructor
    · grind
    · intro h
      rcases h with ⟨l, h, rfl⟩ | ⟨l, h, rfl⟩
      · exact IsInterleaving.left _ _ _ _ h
      · exact IsInterleaving.right _ _ _ _ h

theorem card_interleavings {α : Type _} [DecidableEq α] (xs ys : List α)
    (h_disj : xs.Disjoint ys) :
    (interleavings xs ys).card = (xs.length + ys.length).choose xs.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs xih =>
    induction ys with
    | nil => simp
    | cons y ys yih =>
      rw [partition_interleavings, Finset.card_union_of_disjoint,
        Finset.card_image_of_injective, Finset.card_image_of_injective, yih, xih]
      · simp only [List.length_cons]
        rw [←Nat.add_assoc, ←Nat.add_assoc, Nat.choose_succ_succ']
        grind
      all_goals grind [Finset.disjoint_right, List.disjoint_cons_left,
        List.disjoint_of_disjoint_cons_left, List.disjoint_of_disjoint_cons_right,
        List.cons_injective]

theorem eq_filter_of_isInterleaving {α : Type _} [DecidableEq α] (xs ys zs : List α)
    (h_inter : IsInterleaving xs ys zs) (h_disj : xs.Disjoint ys) :
    ys = zs.filter (fun a => ¬ List.elem a xs) := by
  induction h_inter with
  | nil => grind
  | left a xs ys zs =>
    calc ys
      _ = List.filter (fun a' => a' ≠ a) (List.filter (fun a' => ¬ List.elem a' xs) zs) := by
            grind [List.filter_eq_self, List.disjoint_cons_left]
      _ = _ := by simp
  | right _ _ _ _ _ ih =>
    rw [List.disjoint_cons_right] at h_disj
    simpa [h_disj.1] using ih h_disj.2

theorem isInterleaving_second_determined {α : Type _} (xs ys ys' zs : List α)
    (hys_inter : IsInterleaving xs ys zs) (hys'_inter : IsInterleaving xs ys' zs)
    (hys_disj : xs.Disjoint ys) (hys'_disj : xs.Disjoint ys') : ys = ys' := by
  induction zs generalizing xs ys ys'
  case nil => grind
  case cons z zs ih =>
    cases hys_inter
    case left xs hys_inter =>
      suffices IsInterleaving xs ys' zs by grind [List.disjoint_cons_left]
      cases hys'_inter
      case left => assumption
      case right => grind [List.disjoint_cons_left]
    case right ys hys_inter =>
      cases hys'_inter
      case left => grind [List.disjoint_cons_left]
      case right ys' hys'_inter => grind [List.disjoint_cons_right]

@[grind cases]
inductive IsListInterleaving {α : Type _} : List (List α) → List α → Prop where
  | nil : IsListInterleaving [] []
  | cons (xss : List (List α)) (xs ys zs : List α) :
    IsInterleaving xs ys zs → IsListInterleaving xss ys → IsListInterleaving (xs :: xss) zs

@[grind =]
theorem isListInterleaving_nil_iff {α : Type _} (zs : List α) :
    IsListInterleaving [] zs ↔ zs = [] := by
  grind [IsListInterleaving]

@[grind →]
theorem length_isListInterleaving {α : Type _} (xss : List (List α)) (zs : List α)
    (h : IsListInterleaving xss zs) : zs.length = (List.map List.length xss).sum := by
  induction h <;> grind

theorem perm_flatten_of_isListInterleaving {α : Type _} (xss : List (List α)) (zs : List α)
    (h : IsListInterleaving xss zs) : zs ~ xss.flatten := by
  induction h with
  | nil => simp
  | cons _ xs ys =>
    trans xs ++ ys <;> grind [List.perm_append_left_iff]

theorem List.disjoint_flatten {α : Type _} (xs : List α) (yss : List (List α)) :
    xs.Disjoint yss.flatten ↔ ∀ ys ∈ yss, xs.Disjoint ys := by
  induction yss with
  | nil => simp
  | cons => grind [flatten_cons, disjoint_append_right]

def forgetYs {α : Type _} (xss : List (List α)) (xs : List α) :
    ((ys : {ys : List α // IsListInterleaving xss ys}) × {zs : List α // IsInterleaving xs ys zs}) →
      {zs : List α // IsListInterleaving (xs :: xss) zs}
  | ⟨⟨ys, hys⟩, ⟨zs, hzs⟩⟩ => ⟨zs, IsListInterleaving.cons xss xs ys zs hzs hys⟩

theorem forgetYs_inj_of_disjoint {α : Type _} (xss : List (List α)) (xs : List α)
    (h_disj : List.Pairwise List.Disjoint (xs :: xss)) : Function.Injective (forgetYs xss xs) := by
  intro ⟨⟨ys, hys⟩, ⟨zs, hzs⟩⟩ ⟨⟨ys', hys'⟩, ⟨zs', hzs'⟩⟩ h
  simp only [forgetYs, Subtype.mk.injEq] at h
  rw [←h] at hzs'
  simp only [Sigma.mk.injEq, Subtype.mk.injEq]
  rw [List.pairwise_cons] at h_disj
  have : ys = ys' := by
    have : xs.Disjoint xss.flatten := (xs.disjoint_flatten xss).mpr h_disj.1
    apply isInterleaving_second_determined xs _ _ zs hzs hzs'
    all_goals grind [List.Perm.disjoint_right, perm_flatten_of_isListInterleaving]
  constructor
  · exact this
  · rw [Subtype.heq_iff_coe_eq]
    · assumption
    · intro _
      rw [this]

theorem forgetYs_surj {α : Type _} (xss : List (List α)) (xs : List α) :
    Function.Surjective (forgetYs xss xs) := by
  intro ⟨zs, h⟩
  cases h
  case cons ys hys hzs =>
    use ⟨⟨ys, hys⟩, ⟨zs, hzs⟩⟩
    simp [forgetYs]

theorem forgetYs_bij_of_disjoint {α : Type _} (xss : List (List α)) (xs : List α)
    (h_disj : List.Pairwise List.Disjoint (xs :: xss)) :
    Function.Bijective (forgetYs xss xs) :=
  ⟨forgetYs_inj_of_disjoint xss xs h_disj, forgetYs_surj xss xs⟩

@[reducible]
def isListInterleavingBool {α : Type _} [DecidableEq α] : List (List α) → List α → Bool
  | [], [] => true
  | [], (_ :: _) => false
  | (xs :: xss), zs =>
    xss.flatten.permutations.any
      (fun ys => isInterleavingBool xs ys zs && isListInterleavingBool xss ys)

theorem isListInterleaving_iff {α : Type _} [DecidableEq α] :
    (xss : List (List α)) → (zs : List α) →
       isListInterleavingBool xss zs ↔ IsListInterleaving xss zs
  | [], [] => by simpa [isListInterleavingBool] using IsListInterleaving.nil
  | [], (_ :: _) => by grind
  | (xs :: xss), zs => by
    unfold isListInterleavingBool
    simp only [List.any_eq_true, List.mem_permutations, Bool.and_eq_true]
    constructor
    · intro ⟨ys, _, hys, hzs⟩
      · apply IsListInterleaving.cons (ys := ys)
        · exact (isInterleaving_iff xs ys zs).mp hys
        · exact (isListInterleaving_iff _ _).mp hzs
    · intro h
      cases h
      case cons ys hys hzs =>
        use ys
        refine ⟨?_, ?_, ?_⟩
        · exact perm_flatten_of_isListInterleaving xss ys hys
        · exact (isInterleaving_iff xs ys zs).mpr hzs
        · exact (isListInterleaving_iff _ _).mpr hys

instance instDecidableIsListInterleaving {α : Type _} [DecidableEq α] (xss : List (List α))
    (zs : List α) : Decidable (IsListInterleaving xss zs) :=
  decidable_of_bool (isListInterleavingBool xss zs) (isListInterleaving_iff xss zs)

def listInterleavings {α : Type _} [DecidableEq α] (xss : List (List α)) : Finset (List α) :=
  Finset.filter (IsListInterleaving xss) <| List.toFinset xss.flatten.permutations

@[simp]
theorem mem_listInterleavings_iff {α : Type _} [DecidableEq α] (xss : List (List α)) (zs : List α) :
    zs ∈ listInterleavings xss ↔ IsListInterleaving xss zs := by
  simpa [listInterleavings] using fun h ↦ perm_flatten_of_isListInterleaving xss zs h

instance instFintypeSubtypeIsListInterleaving {α : Type _} [DecidableEq α] (xss : List (List α)) :
    Fintype {zs : List α // IsListInterleaving xss zs} := by
  apply Fintype.subtype (s := listInterleavings xss)
  simp

@[simp]
theorem listInterleavings_nil {α : Type _} [DecidableEq α] :
    listInterleavings (α := α) [] = {[]} := by
  ext l
  rw [mem_listInterleavings_iff, Finset.mem_singleton]
  exact isListInterleaving_nil_iff l

theorem card_listInterleavings {α : Type _} [DecidableEq α] (xss : List (List α))
    (h_disj : List.Pairwise List.Disjoint xss) :
    (listInterleavings xss).card =
      Nat.multinomial (Finset.univ : Finset (Fin (xss.length))) (fun i => (xss.get i).length) := by
  induction xss with
  | nil => simp
  | cons xs xss ih =>
    have finset_equiv_subtype : (listInterleavings (xs :: xss)).subtype (fun _ => True) ≃
      {zs : List α // IsListInterleaving (xs :: xss) zs} := by
      simp only [Finset.mem_subtype, mem_listInterleavings_iff]
      refine ⟨fun x => ⟨↑x.val, x.prop⟩, fun x => ⟨⟨x.val, by trivial⟩, x.prop⟩, ?_, ?_⟩
      all_goals grind
    have card_eq_card_subtype : (listInterleavings (xs :: xss)).card =
        ((listInterleavings (xs :: xss)).subtype (fun _ => True)).card := by
      rw [Finset.card_subtype]
      simp
    let β : {ys // IsListInterleaving xss ys} → Type _ := fun ys => {zs // IsInterleaving xs ys zs}
    have eq_sigma : ((ys : { ys // IsListInterleaving xss ys }) ×
      { zs // IsInterleaving xs (↑ys) zs}) = Sigma β := rfl
    rw [card_eq_card_subtype, Finset.card_eq_of_equiv_fintype (i := finset_equiv_subtype),
      ←Fintype.card_of_bijective (f := forgetYs xss xs) (forgetYs_bij_of_disjoint xss xs h_disj)]
    calc  Fintype.card ((ys : { ys // IsListInterleaving xss ys }) ×
        { zs // IsInterleaving xs (↑ys) zs })
      _ = Fintype.card (Sigma β) := by congr
      _ = ∑ (ys : { ys // IsListInterleaving xss ys }), Fintype.card (β ys) :=
            Fintype.card_sigma (α := β)
      _ = ∑ (ys : { ys // IsListInterleaving xss ys }),
        Fintype.card ({zs // IsInterleaving xs ys zs}) := by congr
      _ = ∑ (ys : { ys // IsListInterleaving xss ys }),
        Finset.card (interleavings xs ys) := by
          congr; ext ys
          exact Fintype.card_of_subtype (interleavings xs ↑ys) (by simp)
      _ = ∑ (ys : { ys // IsListInterleaving xss ys }),
        (xs.length + (↑ys : List α).length).choose (xs.length) := by
          congr; ext ys; apply card_interleavings
          suffices xs.Disjoint xss.flatten by
            rwa [List.Perm.disjoint_right (perm_flatten_of_isListInterleaving xss ys ys.prop)]
          grind [List.pairwise_cons, List.disjoint_flatten]
      _ = ∑ (ys : { ys // IsListInterleaving xss ys }),
        (xs.length + xss.flatten.length).choose (xs.length) := by
          congr; ext ys; congr 2
          apply List.Perm.length_eq
          exact perm_flatten_of_isListInterleaving _ _ ys.prop
      _ = (Fintype.card { ys // IsListInterleaving xss ys }) *
        (xs.length + xss.flatten.length).choose (xs.length) := by simp
      _ = (listInterleavings xss).card * (xs.length + xss.flatten.length).choose (xs.length) := by
        congr
        apply Fintype.card_of_subtype
        simp
      _ = (xs.length + xss.flatten.length).choose (xs.length) *
        (Nat.multinomial Finset.univ fun i ↦ (xss.get i).length) := by grind
    simp only [List.length_flatten, List.get_eq_getElem, List.length_cons]
    have : (Finset.univ : Finset (Fin (xss.length + 1))) =
        Finset.cons ⟨0, by grind⟩ (Finset.image Fin.succ Finset.univ) (by simp) := by
      simp
    rw [this, Nat.multinomial_cons]
    congr 1
    · congr 2
      rw [Finset.sum_image]
      · simp
      · exact Function.Injective.injOn <| Fin.succ_injective xss.length
    · rw [Nat.multinomial, Nat.multinomial]
      congr 1
      · rw [Finset.sum_image]
        · simp
        · exact Function.Injective.injOn <| Fin.succ_injective xss.length
      · rw [Finset.prod_image]
        · simp
        · exact Function.Injective.injOn <| Fin.succ_injective xss.length


theorem isInterleaving_swap {α : Type _} (xs₁ xs₂ ys zs ws : List α) (h₁ : IsInterleaving xs₁ ys ws)
    (h₂ : IsInterleaving xs₂ zs ys) :
    ∃ (ys' : List α), IsInterleaving xs₂ ys' ws ∧ IsInterleaving xs₁ zs ys' := by
  induction h₁ generalizing xs₂ zs with
  | nil => grind
  | left a xs₁ ys ws h₁ ih =>
    obtain ⟨ys', _⟩ := ih xs₂ zs h₂
    use a :: ys'
    grind
  | right a xs₁ ys ws h₁ ih =>
    cases h₂
    case left xs₂ h₂ =>
      obtain ⟨ys', _⟩ := ih xs₂ zs h₂
      use ys'
      grind
    case right xs₂ zs h₂ =>
      obtain ⟨ys', _⟩ := ih xs₂ zs h₂
      use a :: ys'
      grind

theorem isListInterleaving_perm {α : Type _} (xss xss' : List (List α)) (ws : List α)
    (h_perm : xss.Perm xss') (h_inter : IsListInterleaving xss ws) :
    IsListInterleaving xss' ws := by
  induction h_perm generalizing ws with
  | nil => assumption
  | cons => grind [IsListInterleaving]
  | swap xs₂ xs₁ xss =>
    cases h_inter
    case cons ys hys h₁ =>
      cases hys
      case cons zs hzs h₂ =>
        obtain ⟨ys', hys'⟩ := isInterleaving_swap xs₁ xs₂ ys zs ws h₁ h₂
        apply IsListInterleaving.cons (ys := ys')
        · exact hys'.1
        · apply IsListInterleaving.cons (ys := zs) <;> grind
  | trans => grind

theorem exists_interleaving_iff_sublist {α : Type _} (xs zs : List α) :
    xs <+ zs ↔ ∃ ys : List α, IsInterleaving xs ys zs := by
  constructor <;> intro h
  · induction h with
    | slnil => use []; grind
    | @cons xs zs a h ih =>
      obtain ⟨ys, hys⟩ := ih
      use (a :: ys)
      grind
    | @cons₂ xs zs a h ih =>
      obtain ⟨ys, hys⟩ := ih
      use ys
      grind
  · obtain ⟨ys, hys⟩ := h
    induction hys <;> grind
