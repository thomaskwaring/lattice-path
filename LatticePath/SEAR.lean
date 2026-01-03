import Mathlib.Logic.ExistsUnique
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Choose

structure SEAR where
  Sets : Type
  Elems : Sets → Type

namespace SEAR

variable {𝒮 : SEAR}

set_option quotPrecheck false
notation "|" S "|" => 𝒮.Elems S

abbrev Rel (A B : 𝒮.Sets) := |A| → |B| → Prop

notation A " ⇆ " B => 𝒮.Rel A B

class NonTriv where
  defaultSet : 𝒮.Sets
  defaultElem : |defaultSet|

def swapRel {A B : 𝒮.Sets} (φ : A ⇆ B) : B ⇆ A := fun y x => φ x y
notation:max φ "ᵒ" => swapRel φ

theorem swapRel_spec {A B : 𝒮.Sets} (φ : A ⇆ B) (x : |A|) (y : |B|) : φᵒ y x ↔ φ x y := by rfl

theorem swapRel_swapRel {A B : 𝒮.Sets} (φ : A ⇆ B) : φᵒᵒ = φ := by rfl

def swapRelEquiv {A B : 𝒮.Sets} : (A ⇆ B) ≃ (B ⇆ A) where
  toFun := swapRel
  invFun := swapRel

-- def Rel.IsTotal {A B : 𝒮.Sets} (φ : A ⇆ B) : Prop := ∀ x : |A|, ∃ y : |B|, φ x y

-- def Rel.IsFunctional {A B : 𝒮.Sets} (φ : A ⇆ B) : Prop :=
--   ∀ (x : |A|) (y y' : |B|), φ x y → φ x y' → y = y'

structure Func (A B : 𝒮.Sets) where
  rel : A ⇆ B
  hf : ∀ x : |A|, ∃! y : |B|, rel x y

notation A " ⟶ " B => 𝒮.Func A B

theorem Func.total {A B : 𝒮.Sets} (f : 𝒮.Func A B) : ∀ x : |A|, ∃ y : |B|, f.rel x y :=
  fun x => (f.hf x).exists

theorem Func.functional {A B : 𝒮.Sets} (f : 𝒮.Func A B) :
    ∀ (x : |A|) (y y' : |B|), f.rel x y → f.rel x y' → y = y' :=
  fun x => @(f.hf x).unique

theorem func_ext {A B : 𝒮.Sets} (f g : A ⟶ B) (h : f.rel = g.rel) : f = g := by
  grind [SEAR.Func]

instance Func.instCoeRels (A B : 𝒮.Sets) : Coe (A ⟶ B) (A ⇆ B) where
  coe := Func.rel

noncomputable def Func.apply {A B : 𝒮.Sets} (f : 𝒮.Func A B) (x : |A|) : |B| :=
  Classical.choose <| f.total x

noncomputable instance Func.instCoeFun {A B : 𝒮.Sets} :
    CoeFun (A ⟶ B) (fun _ => |A| → |B|) where
  coe f := f.apply

theorem Func.apply_spec {A B : 𝒮.Sets} (f : 𝒮.Func A B) (x : |A|) : f.rel x (f x) :=
  Classical.choose_spec _

theorem Func.apply_unique {A B : 𝒮.Sets} (f : 𝒮.Func A B) (x : |A|) (y : |B|) :
    f.rel x y ↔ y = f x :=
  ⟨fun hy => f.functional x y (f x) hy (f.apply_spec x), fun hy => hy ▸ f.apply_spec x⟩

theorem funext {A B : 𝒮.Sets} (f g : A ⟶ B) (h : ∀ x : |A|, f x = g x) :
    f = g := by
  apply 𝒮.func_ext
  grind [Func.apply_unique]

noncomputable instance Func.instFunLike {A B : 𝒮.Sets} :
    FunLike (A ⟶ B) |A| |B| where
  coe f := f.apply
  coe_injective' f f' h := funext f f' <| congr_fun h

theorem func_rep_fun {A B : 𝒮.Sets} (f : |A| → |B|) :
    ∃! f' : A ⟶ B, ∀ x : |A|, f x = f' x := by
  refine ⟨⟨fun x y => y = f x, fun x => ⟨f x, by simp⟩⟩, ?_, ?_⟩
  · intro x
    apply (Func.apply_unique _ x (f x)).mp
    rfl
  · intro g hg
    apply funext
    intro x
    apply (Func.apply_unique _ _ _).mp
    simpa using Eq.symm <| hg x

def Func.IsInjective {A B : 𝒮.Sets} (f : A ⟶ B) : Prop :=
  ∀ (x x' : |A|) (y : |B|), f.rel x y → f.rel x' y → x = x'

def Func.IsSurjective {A B : 𝒮.Sets} (f : A ⟶ B) : Prop :=
  ∀ y : |B|, ∃ x : |A|, f x = y

noncomputable def id (A : 𝒮.Sets) : A ⟶ A where
  rel := (· = ·)
  hf x := by use x; simp

theorem id_spec (A : 𝒮.Sets) (x x' : |A|) : (id A : A ⇆ A) x x' ↔ x = x' := by rfl

noncomputable def Rel.comp {A B C : 𝒮.Sets} (φ : A ⇆ B) (ψ : B ⇆ C) : A ⇆ C :=
  fun x z => ∃ y : |B|, φ x y ∧ ψ y z

theorem comp_spec {A B C : 𝒮.Sets} (φ : A ⇆ B) (ψ : B ⇆ C) (x : |A|) (z : |C|) :
  (φ.comp ψ) x z ↔ ∃ y : |B|, φ x y ∧ ψ y z := by grind [Rel.comp]

theorem id_comp {A B : 𝒮.Sets} (φ : A ⇆ B) : (id A : A ⇆ A).comp φ = φ := by
  grind [id_spec, comp_spec]

theorem comp_id {A B : 𝒮.Sets} (φ : A ⇆ B) : (φ.comp <| id B) = φ := by
  grind [id_spec, comp_spec]

theorem comp_assoc {A B C D : 𝒮.Sets} (φ : A ⇆ B) (ψ : B ⇆ C) (χ : C ⇆ D) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  grind [comp_spec]

theorem Func.id_apply {A : 𝒮.Sets} (x : |A|) : (id A) x = x := by
  symm; simp [←apply_unique, id]

def Func.comp {A B C : 𝒮.Sets} (f : A ⟶ B) (g : B ⟶ C) : A ⟶ C where
  rel := f.rel.comp g.rel
  hf x := by use g (f x); grind [apply_spec, comp_spec, apply_unique]

theorem Func.comp_apply {A B C : 𝒮.Sets} (f : A ⟶ B) (g : B ⟶ C) (x : |A|) :
    (f.comp g) x = g (f x) := by
  symm; rw [←(f.comp g).apply_unique]
  use f.apply x
  grind [apply_spec]

theorem Func.id_comp {A B : 𝒮.Sets} (f : A ⟶ B) : (id A).comp f = f := by
  apply func_ext
  grind [Func.comp, id_comp]

theorem Func.comp_id {A B : 𝒮.Sets} (f : A ⟶ B) : (f.comp <| id B) = f := by
  apply func_ext
  grind [Func.comp, comp_id]

theorem Func.comp_assoc {A B C D : 𝒮.Sets} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply func_ext
  grind [Func.comp, comp_assoc]

structure Tabulation {A B : 𝒮.Sets} (φ : A ⇆ B) where
  S : 𝒮.Sets
  p₁ : S ⟶ A
  p₂ : S ⟶ B
  represents (x : |A|) (y : |B|) : φ x y ↔ ∃ r : |S|, p₁ r = x ∧ p₂ r = y
  joint_mono (r s : |S|) : p₁ r = p₁ s → p₂ r = p₂ s → r = s

theorem tabulation_universal_property {A B C : 𝒮.Sets} (φ : A ⇆ B) (f : C ⟶ A)
    (g : C ⟶ B) (h : ∀ x : |C|, φ (f x) (g x)) (T : Tabulation φ) :
    ∃! fg : C ⟶ T.S, fg.comp T.p₁ = f ∧ fg.comp T.p₂ = g := by
  choose r hr₁ hr₂ using fun x => T.represents (f x) (g x) |>.mp (h x)
  choose fg hfg_spec hfg_uniq using func_rep_fun r
  use fg
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply funext
    simp [Func.comp_apply, ←hfg_spec, hr₁]
  · apply funext
    simp [Func.comp_apply, ←hfg_spec, hr₂]
  · intro fg' hfg'
    apply hfg_uniq
    grind [Tabulation.joint_mono, Func.comp_apply]

class HasTabulation where
  tab {A B : 𝒮.Sets} (φ : A ⇆ B) : Tabulation φ

def Rel.tabulate [htab : 𝒮.HasTabulation] {A B : 𝒮.Sets} (φ : A ⇆ B) : Tabulation φ :=
  htab.tab φ

instance tabulateCoe {A B : 𝒮.Sets} (φ : A ⇆ B) : CoeOut (Tabulation φ) (𝒮.Sets) where
  coe := Tabulation.S

-- section

variable [hntr : 𝒮.NonTriv] [htab : 𝒮.HasTabulation]

instance : Inhabited 𝒮.Sets := ⟨hntr.defaultSet⟩
instance : Inhabited |default| := ⟨hntr.defaultElem⟩

private def zeroTab := @Rel.tabulate 𝒮 _ default default (fun _ _ => False)

noncomputable instance instZeroSets : Zero 𝒮.Sets where
  zero := zeroTab.S

theorem isEmptyZero : IsEmpty |0| := by
  constructor
  intro x
  apply zeroTab.represents (zeroTab.p₁ x) (zeroTab.p₂ x) |>.mpr
  exact ⟨x, rfl, rfl⟩

theorem initial_zero {A : 𝒮.Sets} : Nonempty <| Unique (0 ⇆ A) := by
  rw [unique_iff_existsUnique]
  refine ⟨default, by trivial, ?_⟩
  intro y _
  ext x
  exact IsEmpty.elim' isEmptyZero x

theorem terminal_zero {A : 𝒮.Sets} : Nonempty <| Unique (A ⇆ 0) := by
  let ⟨_⟩ := initial_zero (A := A)
  exact ⟨swapRelEquiv.unique⟩

private noncomputable def oneTab :=
  @Rel.tabulate 𝒮 _ default default (fun x y => default = x ∧ default = y)

noncomputable instance instOneSets : One 𝒮.Sets where
  one := oneTab.S

theorem nonempty_unique_one : Nonempty <| Unique |1| := by
  rw [unique_iff_existsUnique]
  have : _ := oneTab.represents (𝒮 := 𝒮) default default
  simp only [and_self, true_iff] at this
  refine ⟨Classical.choose this, by simp, ?_⟩
  intro y
  have : _ := oneTab.represents (oneTab.p₁ y) (oneTab.p₂ y)
  have : _ := 𝒮.oneTab.joint_mono
  grind [Classical.choose_spec]

noncomputable instance instUniqueOne : Unique |1| := nonempty_unique_one.some

@[reducible]
def Sets.Subset (A : 𝒮.Sets) := |A| → Prop

@[reducible]
instance instMembershipSubset {A : 𝒮.Sets} : Membership |A| A.Subset where
  mem φ x := φ x

def Sets.Subset.toRel {A : 𝒮.Sets} (σ : A.Subset) : 1 ⇆ A := fun _ x => x ∈ σ

theorem Sets.Subset.toRel_spec {A : 𝒮.Sets} (σ : A.Subset) (x : |A|) : x ∈ σ ↔ σ.toRel default x :=
  Iff.rfl

omit hntr htab in
theorem subset_ext {A : 𝒮.Sets} (σ τ : A.Subset) (h : ∀ x : |A|, x ∈ σ ↔ x ∈ τ) : σ = τ := by
  ext x
  exact h x

theorem exists_injection_of_subset {A : 𝒮.Sets} (σ : A.Subset) :
    ∃ (S : 𝒮.Sets) (i : S ⟶ A), (∀ x : |A|, x ∈ σ ↔ ∃ x' : |S|, i x' = x) ∧ i.IsInjective := by
  let ⟨S, p₁, p₂, hrep, hmono⟩ := σ.toRel.tabulate
  use S, p₂
  constructor
  · intro x
    simp_rw [σ.toRel_spec, hrep default x, instUniqueOne.uniq, true_and]
  · intro x x' y hx hx'
    apply hmono
    · trans default <;> simp_rw [instUniqueOne.uniq]
    · grind [Func.apply_unique]

def Rel.image {A B : 𝒮.Sets} (φ : A ⇆ B) : B.Subset := fun y => ∃ x : |A|, φ x y

omit hntr htab in
theorem Rel.image_spec {A B : 𝒮.Sets} (φ : A ⇆ B) (y : |B|) : y ∈ φ.image ↔ ∃ x : |A|, φ x y :=
  Iff.rfl

omit hntr htab in
theorem apply_mem_image {A B : 𝒮.Sets} (f : A ⟶ B) (x : |A|) : f x ∈ f.rel.image := by
  simp [f.rel.image_spec]
  exact ⟨x, f.apply_spec x⟩

omit hntr htab in
theorem factors_through_iff {A B C : 𝒮.Sets} (f : A ⟶ B) (g : C ⟶ B) :
    (∃ f' : A ⟶ C, f = f'.comp g) ↔ (∀ x : |A|, f x ∈ g.rel.image) := by
  constructor
  · intro ⟨f', h⟩ x
    simp_rw [h, Func.comp_apply, Rel.image_spec]
    use f' x
    exact g.apply_spec _
  · intro h
    simp_rw [Rel.image_spec] at h
    choose z hz using h
    choose f' hf' using func_rep_fun z
    use f'
    apply funext
    grind [Func.comp_apply, Func.apply_unique]

theorem epi_mono {A B : 𝒮.Sets} (f : A ⟶ B) :
    ∃ (S : 𝒮.Sets) (e : A ⟶ S) (m : S ⟶ B), f = e.comp m ∧ e.IsSurjective ∧ m.IsInjective := by
  obtain ⟨S, i, hS, hi⟩ := exists_injection_of_subset f.rel.image
  obtain ⟨e, he⟩ : ∃ f' : A ⟶ S, f = f'.comp i := by
    simp_rw [factors_through_iff, Rel.image_spec]
    intro x
    specialize hS (f x)
    simp_rw [apply_mem_image, true_iff] at hS
    obtain ⟨x', hx'⟩ := hS
    exact ⟨x', i.apply_unique x' (f x) |>.mpr hx'.symm⟩
  refine ⟨S, e, i, he, ?_, hi⟩
  intro y
  have : i y ∈ f.rel.image := hS (i y) |>.mpr ⟨y, rfl⟩
  simp_rw [Rel.image_spec] at this
  obtain ⟨x, hx⟩ := this
  use x
  suffices i (e x) = i y by
    apply hi (y := i y)
    · rw [←this]
      apply i.apply_spec
    · exact Func.apply_spec i y
  rw [f.apply_unique, he] at hx
  rw [hx, Func.comp_apply]

def Rel.IsBijection {A B : 𝒮.Sets} (φ : A ⇆ B) :=
    (∀ x : |A|, ∃! y : |B|, φ x y) ∧  ∀ y : |B|, ∃! x : |A|, φ x y

def Rel.IsBijection.toFun {A B : 𝒮.Sets} {φ : A ⇆ B} (h : φ.IsBijection) : A ⟶ B where
  rel := φ
  hf := h.1

def Rels.IsBijection.invFun {A B : 𝒮.Sets} {φ : A ⇆ B} (h : φ.IsBijection) :
    B ⟶ A where
  rel := φᵒ
  hf := by
    intro y
    obtain ⟨x, hx⟩ := h.2 y
    use x
    grind [swapRel_spec]

omit hntr htab in
theorem exists_isBijection_of_tabulation {A B : 𝒮.Sets} {φ : A ⇆ B} (T T' : Tabulation φ) :
    ∃ ψ : T ⇆ T', ψ.IsBijection := by
  use fun x y => T.p₁ x = T'.p₁ y ∧ T.p₂ x = T'.p₂ y
  constructor
  · intro r
    have hr := T.represents (T.p₁ r) (T.p₂ r) |>.mpr ⟨r, rfl, rfl⟩
    let ⟨s, hs⟩ := T'.represents (T.p₁ r) (T.p₂ r) |>.mp hr
    use s
    grind [Tabulation.joint_mono]
  · intro r
    have hr := T'.represents (T'.p₁ r) (T'.p₂ r) |>.mpr ⟨r, rfl, rfl⟩
    let ⟨s, hs⟩ := T.represents (T'.p₁ r) (T'.p₂ r) |>.mp hr
    use s
    grind [Tabulation.joint_mono]

private def prodTab (A B : 𝒮.Sets) := Rel.tabulate (A := A) (B := B) <| fun _ _ => True

noncomputable instance instMulSEAR : Mul 𝒮.Sets where
  mul A B := (prodTab A B).S

omit hntr in
theorem mul_spec {A B : 𝒮.Sets} (x : |A|) (y : |B|) :
    ∃! xy : |A * B|, (prodTab A B).p₁ xy = x ∧ (prodTab A B).p₂ xy = y := by
  obtain ⟨xy, hxy⟩ : ∃ r : |A * B|, (prodTab A B).p₁ r = x ∧ (prodTab A B).p₂ r = y := by
    simpa using (prodTab A B).represents x y
  refine ⟨xy, hxy, ?_⟩
  intro xy' hxy'
  apply (prodTab A B).joint_mono <;> grind

noncomputable def pair {A B : 𝒮.Sets} (x : |A|) (y : |B|) : |A * B| :=
  Classical.choose <| mul_spec x y

omit hntr in
theorem pair_spec {A B : 𝒮.Sets} (x : |A|) (y : |B|) :
    (prodTab A B).p₁ (pair x y) = x ∧ (prodTab A B).p₂ (pair x y) = y :=
  (Classical.choose_spec <| mul_spec x y).1

omit hntr in
theorem pair_of_proj {A B : 𝒮.Sets} (xy : |A * B|) :
    xy = pair ((prodTab A B).p₁ xy) ((prodTab A B).p₂ xy) := by
  have := Classical.choose_spec <| mul_spec ((prodTab A B).p₁ xy) ((prodTab A B).p₂ xy)
  apply this.2
  exact ⟨rfl, rfl⟩

omit hntr in
theorem mul_cartesian {A B T : 𝒮.Sets} (f : T ⟶ A) (g : T ⟶ B) :
    ∃! fg : T ⟶ A * B, fg.comp (prodTab A B).p₁ = f ∧ fg.comp (prodTab A B).p₂ = g := by
  apply tabulation_universal_property
  grind

class HasPower where
  pset : 𝒮.Sets → 𝒮.Sets
  mem_rel (A : 𝒮.Sets) : A ⇆ (pset A)
  subset_rep {A : 𝒮.Sets} (S : A.Subset) : ∃! s : |pset A|, ∀ x : |A|, x ∈ S ↔ (mem_rel A) x s

variable [hpow : 𝒮.HasPower]

prefix:max "𝒫" => hpow.pset
prefix:max "ε" => hpow.mem_rel

-- theorem pset_rep_prop {A : 𝒮.Sets} (P : |A| → Prop) :
--     ∃! s : |𝒫 A|, ∀ x : |A|, P x ↔ (ε A)(x,s) := by
--   choose S hS using subset_comp P
--   choose s hs using h₃.subset_rep S
--   use s
--   simp only at hS hs ⊢
--   constructor
--   · grind
--   · intro _ _
--     apply hs.2
--     grind

omit hntr htab in
theorem rel_as_func {A B : 𝒮.Sets} (φ : A ⇆ B) :
    ∃! f : A ⟶ 𝒫 B, ∀ (x : |A|) (y : |B|), φ x y ↔ (ε B) y (f x) := by
  choose s hs_spec hs_uniq using fun x => hpow.subset_rep (φ x ·)
  choose f hf using func_rep_fun s
  refine ⟨f, ?_, ?_⟩
  · grind
  · intro _ _
    apply hf.2
    intro _
    symm
    apply hs_uniq
    grind

theorem exists_exp (A B : 𝒮.Sets) :
    ∃ (E : 𝒮.Sets) (ev : (E * A) ⟶ B), ∀ f : A ⟶ B,
      ∃! s : |E|, ∀ a : |A|, ev (pair s a) = f a := by
  obtain ⟨E, i, hE, hi⟩ := exists_injection_of_subset <|
    fun s => ∀ x : |A|, ∃! y : |B|, (HasPower.mem_rel (A * B)) (pair x y) s
  let ev_rel : (E * A) ⇆ B :=
    fun s y => (HasPower.mem_rel (A * B)) (pair ((prodTab E A).p₂ s) y) (i ((prodTab E A).p₁ s))
  have ev_functional : ∀ s : |E * A|, ∃! y : |B|, ev_rel s y := by
    intro s
    specialize hE (i ((prodTab E A).p₁ s))
    simp only [exists_apply_eq_apply, iff_true] at hE
    simpa [ev_rel] using hE <| (prodTab E A).p₂ s
  let ev : (E * A) ⟶ B := ⟨ev_rel, ev_functional⟩
  use E, ev
  intro f
  obtain ⟨graph, hg, hg_uniq⟩ :=
    hpow.subset_rep <| fun xy => f ((prodTab A B).p₁ xy) = (prodTab A B).p₂ xy
  obtain ⟨s, si⟩ : ∃ s : |E|, i s = graph := by
    apply (hE graph).mp
    intro x
    use f x
    simp only at hg ⊢
    constructor
    · simpa [Membership.mem, pair_spec] using hg (pair x (f x))
    · intro y hy
      have := (hg (pair x y)).mpr hy
      grind [pair_spec]
  refine ⟨s, ?_, ?_⟩
  · intro x
    have := ev.apply_spec (pair s x)
    simp only [show ev.rel = ev_rel by rfl, pair_spec, ev_rel, si] at this
    symm
    simpa [Membership.mem, pair_spec] using (hg (pair x (ev.apply (pair s x)))).mpr this
  · intro s' hs'
    apply hi (y := graph)
    · suffices i s' = graph by rw [←this]; exact i.apply_spec _
      apply hg_uniq
      intro xy
      have := hE (i s') |>.mpr ⟨s', rfl⟩
      simp_rw [←hs']
      constructor <;> intro h
      · simp_rw [Eq.comm, ←ev.apply_unique, ev, ev_rel, pair_spec] at h
        rwa [pair_of_proj xy]
      · simp_rw [Membership.mem, Eq.comm, ←ev.apply_unique, ev, ev_rel, pair_spec]
        rwa [←pair_of_proj xy]
    · rw [←si]
      exact i.apply_spec _

class HasInfinity where
  N : 𝒮.Sets
  o : |N|
  sc : N ⟶ N
  ho : ∀ n : |N|, o ≠ sc n
  hsc : sc.IsInjective

omit hpow in
noncomputable def fibre {A Y : 𝒮.Sets} (φ : A ⇆ Y) (x : |A|) : 𝒮.Sets :=
  Classical.choose <| exists_injection_of_subset (φ x · : Y.Subset)

class HasCollection where
  coll : (A : 𝒮.Sets) → (|A| → 𝒮.Sets → Prop) → 𝒮.Sets
  pA : (A : 𝒮.Sets) → (p : |A| → 𝒮.Sets → Prop) → (coll A p ⟶ A)
  pUFam : (A : 𝒮.Sets) → (p : |A| → 𝒮.Sets → Prop) → 𝒮.Sets
  pURel : (A : 𝒮.Sets) → (p : |A| → 𝒮.Sets → Prop) → (coll A p ⇆ pUFam A p)
  hrep : (A : 𝒮.Sets) → (p : |A| → 𝒮.Sets → Prop) → (b : |coll A p|) →
    p (pA A p b) (fibre (pURel A p) b)
  him : (A : 𝒮.Sets) → (p : |A| → 𝒮.Sets → Prop) → (a : |A|) → (∃ X : 𝒮.Sets, p a X) →
    a ∈ (pA A p).rel.image

end SEAR
