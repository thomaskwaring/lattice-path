import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Pochhammer

#check ascPochhammer_succ_right
#check Nat.stirlingFirst_succ_succ

open Polynomial

variable {R : Type*} [CommRing R]

theorem coeff_ascPochhammer_eq_stirlingFirst (n k : ℕ) :
    (ascPochhammer R n).coeff k = n.stirlingFirst k := by
  induction n generalizing k with
  | zero => cases k <;> simp [coeff_one]
  | succ n ih =>
    cases k
    case zero => simp [ascPochhammer_succ_left]
    case succ k =>
      rw [ascPochhammer_succ_right, Nat.stirlingFirst_succ_succ, mul_add, coeff_add, coeff_mul_X,
        coeff_mul_natCast, ih k, ih (k + 1), add_comm, mul_comm]
      simp
