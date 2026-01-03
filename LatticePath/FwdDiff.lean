import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.NthRewrite

open Polynomial fwdDiff

variable {R : Type*} [CommRing R]

noncomputable def polyFwdDiff (h : R) (p : R[X]) : R[X] := p.comp (X + C h) - p

notation "Δₚ_[" h "]" => polyFwdDiff h

theorem polyFwdDiff_eval (h : R) (p : R[X]) : (Δₚ_[h] p).eval = Δ_[h] p.eval := by
  ext a
  simp [fwdDiff, polyFwdDiff]

theorem polyFwdDiff_add (h : R) (p q : R[X]) : Δₚ_[h] (p + q) = Δₚ_[h] p + Δₚ_[h] q := by
  simp only [polyFwdDiff, add_comp]
  ring

theorem polyFwdDiff_mul_const (h a : R) (p : R[X]) : Δₚ_[h] (C a * p) = C a * Δₚ_[h] p := by
  simp [polyFwdDiff, mul_sub]

theorem polyFwdDiff_smul (h a : R) (p : R[X]) : Δₚ_[h] (a • p) = a • Δₚ_[h] p := by
  simp [polyFwdDiff, Polynomial.smul_eq_C_mul, mul_sub]

noncomputable def polyFwdDiffLin (h : R) : R[X] →ₗ[R] R[X] where
  toFun := Δₚ_[h]
  map_add' := polyFwdDiff_add h
  map_smul' := polyFwdDiff_smul h

theorem polyFwdDiff_const (h a : R) : Δₚ_[h] (C a) = 0 := by simp [polyFwdDiff]

theorem polyFwdDiff_X (h : R) : Δₚ_[h] X = C h := by simp [polyFwdDiff]

theorem polyFwdDiff_degree_lt [Nontrivial R] [NoZeroDivisors R] (h : R) (p : R[X]) (hp0 : p ≠ 0) :
    (Δₚ_[h] p).degree < p.degree := by
  rw [polyFwdDiff, ←degree_neg, neg_sub]
  apply degree_sub_lt (hp0 := hp0)
  · rw [degree_eq_natDegree hp0, degree_eq_natDegree (comp_X_add_C_ne_zero_iff.mpr hp0),
      natDegree_comp_eq_of_mul_ne_zero (by simpa)]
    simp
  · rw [leadingCoeff_comp] <;> simp

theorem polyFwdDiff_iter_natDegree_add_one [Nontrivial R] [NoZeroDivisors R] (h : R) (p : R[X])
    (m : ℕ) (hm : p.natDegree ≤ m) : (Δₚ_[h])^[m + 1] p = 0 := by
  induction m generalizing p with
  | zero =>
    rw [nonpos_iff_eq_zero, natDegree_eq_zero] at hm
    obtain ⟨a, hp⟩ := hm
    rw [←hp]
    simp [polyFwdDiff_const]
  | succ n ih =>
    apply ih
    by_cases p = 0
    case pos hp => simp [hp, polyFwdDiff]
    case neg hp =>
      by_cases Δₚ_[h] p = 0
      case pos hdp => simp [hdp]
      case neg hdp =>
        have : _ := polyFwdDiff_degree_lt h p hp
        rw [degree_eq_natDegree hdp, degree_eq_natDegree hp, Nat.cast_lt] at this
        grind

noncomputable def polyShift (h : R) (p : R[X]) : R[X] := p.comp (X + C h)

notation "T_[" h "]" => polyShift h

theorem polyShift_add (h : R) (p q : R[X]) : T_[h] (p + q) = T_[h] p + T_[h] q := by
  simp [polyShift]

theorem polyShift_const (h a : R) : T_[h] (C a) = C a := by simp [polyShift]

theorem polyShift_mul (h : R) (p q : R[X]) : T_[h] (p * q) = T_[h] p * T_[h] q := by
  simp [polyShift]

theorem polyShift_sub (h : R) (p q : R[X]) : T_[h] (p - q) = T_[h] p - T_[h] q := by
  simp [polyShift]

noncomputable def polyShiftAlgHom (h : R) : R[X] →ₐ[R] R[X] where
  toFun := T_[h]
  map_one' := polyShift_const h 1
  map_mul' := polyShift_mul h
  map_zero' := by simp [polyShift]
  map_add' := polyShift_add h
  commutes' r := by simp [polyShift]

theorem polyShift_comm (h k : R) (p : R[X]) : T_[h] (T_[k] p) = T_[k] (T_[h] p) := by
  let hk : R[X] →ₐ[R] R[X] := (polyShiftAlgHom h).comp (polyShiftAlgHom k)
  let kh : R[X] →ₐ[R] R[X] := (polyShiftAlgHom k).comp (polyShiftAlgHom h)
  suffices hk = kh by
    simpa [hk, kh, polyShiftAlgHom] using AlgHom.congr_fun this p
  apply algHom_ext
  simp [polyShiftAlgHom, hk, kh, polyShift, add_right_comm]

theorem polyFwdDiff_eq_shift_sub_id (h : R) : Δₚ_[h] = T_[h] - id := by
  ext p : 1
  simp [polyFwdDiff, polyShift]

theorem polyFwdDiff_shift (h k : R) : Δₚ_[h] ∘ T_[k] = T_[k] ∘ Δₚ_[h] := by
  ext p : 1
  simpa [polyFwdDiff, polyShift] using polyShift_comm h k p

theorem polyShift_comp_eq_add (h k : R) : T_[h] ∘ T_[k] = T_[h + k] := by
  let hk : R[X] →ₐ[R] R[X] := (polyShiftAlgHom h).comp (polyShiftAlgHom k)
  let hk_add : R[X] →ₐ[R] R[X] := polyShiftAlgHom (h + k)
  ext p : 1
  suffices hk = hk_add by
    simpa [hk, hk_add, polyShiftAlgHom] using AlgHom.congr_fun this p
  apply algHom_ext
  simp [hk, hk_add, polyShiftAlgHom, polyShift, ←add_assoc]

theorem polyShift_zero : T_[0] = (id : R[X] → R[X]) := by
  ext p : 1
  simp [polyShift]

@[simp]
theorem polyFwdDiff_zero : (Δₚ_[0] : R[X] → R[X]) = 0 := by
  ext p : 1
  simp [polyFwdDiff]

theorem polyFwdDiff_descPochhammer (n : ℕ) :
    Δₚ_[1] (descPochhammer R (n + 1)) = (n + 1) * descPochhammer R n := by
  rw [polyFwdDiff]
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right, mul_comp, map_one, X_comp]
  have : ((descPochhammer R n).comp (X - 1)).comp (X + 1) =
    (T_[1] ∘ T_[-1]) (descPochhammer R n) := by
    rw [Function.comp_apply, polyShift, polyShift, map_neg, map_one]
    congr
  rw [this, polyShift_comp_eq_add, add_neg_cancel, polyShift_zero, id_eq]
  ring

theorem polyFwdDiff_ascPochhammer (n : ℕ) :
    Δₚ_[-1] (ascPochhammer R (n + 1)) = - (n + 1) * ascPochhammer R n := by
  rw [polyFwdDiff]
  nth_rw 2 [ascPochhammer_succ_right]
  simp only [ascPochhammer, mul_comp, X_comp, map_neg, map_one]
  have : ((ascPochhammer R n).comp (X + 1)).comp (X + -1) =
    (T_[-1] ∘ T_[1]) (ascPochhammer R n) := by
    rw [Function.comp_apply, polyShift, polyShift, map_neg, map_one]
  rw [this, polyShift_comp_eq_add, neg_add_cancel, polyShift_zero, id_eq]
  ring

theorem sum_polyFwdDiff {h : R} (p : R[X]) (n : ℕ) :
    ∑ k ∈ Finset.range n, T_[k * h] (Δₚ_[h] p) = Δₚ_[n * h] p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.range_add_one, Finset.mem_range, lt_self_iff_false, not_false_eq_true,
      Finset.sum_insert, ih, Nat.cast_add, Nat.cast_one]
    simp [polyFwdDiff_eq_shift_sub_id, polyShift_sub, add_mul, ←polyShift_comp_eq_add]
