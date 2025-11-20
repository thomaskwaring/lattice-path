import Mathlib.Data.List.Sym

namespace List

variable {α β : Type*}

protected theorem Perm.sym2' {xs ys : List α} (h : xs ~ ys) :
    xs.sym2 ~ ys.sym2 := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    conv => enter [1, 2, 1]; rw [Sym2.eq_swap]
    -- -- Explicit permutation to speed up simps that follow.
    refine Perm.trans (Perm.swap ..) (Perm.trans (Perm.cons _ ?_) (Perm.swap ..))
    calc
      s(y, y) :: (List.map (fun y_1 ↦ s(y, y_1)) xs ++
        s(x, x) :: (List.map (fun y ↦ s(x, y)) xs ++ xs.sym2)) ~
        s(y, y) :: (s(x, x) :: (List.map (fun y ↦ s(x, y)) xs ++ xs.sym2) ++
        List.map (fun y_1 ↦ s(y, y_1)) xs) := by
          apply List.Perm.cons; exact List.perm_append_comm ..
      _ = s(y, y) :: s(x, x) :: ((List.map (fun y ↦ s(x, y)) xs ++ xs.sym2) ++
        List.map (fun y_1 ↦ s(y, y_1)) xs) := by simp
      _ ~ s(x, x) :: s(y, y) :: ((List.map (fun y ↦ s(x, y)) xs ++ xs.sym2) ++
        List.map (fun y_1 ↦ s(y, y_1)) xs) := List.Perm.swap ..
    apply List.Perm.cons
    calc
      s(y, y) :: ((List.map (fun y ↦ s(x, y)) xs ++ xs.sym2) ++
        List.map (fun y_1 ↦ s(y, y_1)) xs) ~
        s(y, y) :: (List.map (fun y_1 ↦ s(y, y_1)) xs ++
        (List.map (fun y ↦ s(x, y)) xs ++ xs.sym2)) := by apply List.Perm.cons; exact
          perm_append_comm
      _ = s(y, y) :: List.map (fun y_1 ↦ s(y, y_1)) xs ++
        (List.map (fun y ↦ s(x, y)) xs ++ xs.sym2) := by simp
      _ ~ List.map (fun y ↦ s(x, y)) xs ++
        (s(y, y) :: List.map (fun y_1 ↦ s(y, y_1)) xs ++ xs.sym2) := List.perm_append_comm_assoc ..
  | trans _ _ ih1 ih2 => exact ih1.trans ih2




end List
