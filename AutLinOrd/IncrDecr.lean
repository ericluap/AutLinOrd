import AutLinOrd.Pow
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Order

/-!
  This file proves basic facts about what it means for an order automorphism
  to be increasing or decreasing at a given point.
-/

variable {α : Type*} [LinearOrder α]

/--
  `f` is increasing at `x` if
  `x < f x`.
-/
abbrev isIncreasingAt (f : α ≃o α) (x : α) := x < f x
abbrev isDecreasingAt (f : α ≃o α) (x : α) := f x < x

/--
  If `f` is increasing at `x`, then for any integer `z`,
  `(f ^ z) x < (f ^ (z+1)) x`.
-/
theorem incr_plus_one_pow {f : α ≃o α} {x : α} (incr : isIncreasingAt f x)
    (z : ℤ) : (f ^ z) x < (f ^ (z + 1)) x := by
  simp [←add_pows, incr]

/--
  If `f` is decreasing at `x`, then for any integer `z`,
  `(f ^ (z+1)) x < (f ^ z) x`.
-/
theorem decr_plus_one_pow {f : α ≃o α} {x : α} (decr : isDecreasingAt f x)
    (z : ℤ) : (f ^ (z + 1)) x < (f ^ z) x := by
  simp [←add_pows, decr]

/--
  If `f` is increasing at `x`, then for any integer `z`,
  `(f ^ (z-1)) x < (f ^ z) x`.
-/
theorem incr_minus_one_pow {f : α ≃o α} {x : α} (incr : isIncreasingAt f x)
    (z : ℤ) : (f ^ (z - 1)) x < (f ^ z) x := by
  apply_fun f
  simp [add_pows_one, show 1 + z = z + 1 by omega, incr_plus_one_pow incr z]

/--
  If `f` is decreasing at `x`, then for any integer `z`,
  `(f ^ z) x < (f ^ (z-1)) x`.
-/
theorem decr_minus_one_pow {f : α ≃o α} {x : α} (decr : isDecreasingAt f x)
    (z : ℤ) : (f ^ z) x < (f ^ (z - 1)) x := by
  apply_fun f
  simp [add_pows_one, show 1 + z = z + 1 by omega, decr_plus_one_pow decr z]

/--
  If `f` is increasing at `x`, then for any
  positive integer `z`, `x < (f ^ z) x`.
-/
theorem incr_pos_gt {f : α ≃o α} {x : α} {z : ℤ}
    (incr : isIncreasingAt f x) (pos : 0 < z) : x < (f ^ z) x  := by
  induction z with
  | zero => simp at pos
  | succ i ih =>
    by_cases is_zero : i = 0
    · simp [is_zero, incr]
    · calc x
      _ < (f ^ (i : ℕ)) x := ih (by omega)
      _ < (f ^ ((i : ℕ) + 1)) x := by simp [←add_pows_n, incr]
  | pred i _ => omega

/--
  If `f` is increasing at `x`, then for any
  negative integer `z`, `(f ^ z) x < x`.
-/
theorem incr_neg_lt {f : α ≃o α} {x : α} {z : ℤ}
    (incr : isIncreasingAt f x) (neg : z < 0) : (f ^ z) x < x  := by
  induction z with
  | zero => simp at neg
  | succ i _ => omega
  | pred i ih =>
    by_cases is_zero : i = 0
    · rw [is_zero]
      apply_fun f
      simp [incr]
    · calc (f ^ (-(i : ℤ) - 1)) x
      _ < (f ^ (-(i : ℤ))) x := incr_minus_one_pow incr (-(i : ℤ))
      _ < x := ih (by omega)

/--
  If `f` is decreasing at `x`, then for any
  negative integer `z`, `x < (f ^ z) x`.
-/
theorem decr_neg_gt {f : α ≃o α} {x : α} {z : ℤ}
    (decr : isDecreasingAt f x) (neg : z < 0) : x < (f ^ z) x  := by
  induction z with
  | zero => simp at neg
  | succ i _ => omega
  | pred i ih =>
    by_cases is_zero : i = 0
    · rw [is_zero]
      apply_fun f
      simp [decr]
    · calc x
      _ < (f ^ (-(i : ℤ))) x := ih (by omega)
      _ < (f ^ (-(i : ℤ) - 1)) x := decr_minus_one_pow decr (-(i : ℤ))

/--
  If `f` is increasing at `x` and `x < (f ^ z) x`,
  then `0 < z`.
-/
theorem incr_up_pos {f : α ≃o α} {x : α} {z : ℤ}
    (incr : isIncreasingAt f x) (up : x < (f ^ z) x) : 0 < z := by
  obtain z_lt_zero | z_eq_zero | zero_lt_z := Int.lt_trichotomy z 0
  · have := incr_neg_lt incr z_lt_zero
    order
  · simp [z_eq_zero] at up
  · trivial

/--
  If `f` is decreasing at `x` and `(f ^ z) x < x`,
  then `0 < z`.
-/
theorem decr_down_pos {f : α ≃o α} {x : α} {z : ℤ}
    (decr : isDecreasingAt f x) (down : (f ^ z) x < x) : 0 < z := by
  obtain z_lt_zero | z_eq_zero | zero_lt_z := Int.lt_trichotomy z 0
  · have := decr_neg_gt decr z_lt_zero
    order
  · simp [z_eq_zero] at down
  · trivial

/--
  If `f` is increasing at `x` and `(f ^ z) x < (f ^ w) x`,
  then `z < w`.
-/
theorem incr_gt_pow_gt {f : α ≃o α} {x : α} {z w : ℤ}
    (incr : isIncreasingAt f x) (gt : (f^z) x < (f^w) x) : z < w := by
  have : (f ^ (-z)) ((f^z) x) < (f ^ (-z)) ((f^w) x) :=
    OrderIso.GCongr.orderIso_apply_lt_apply (f ^ (-z)) gt
  simp only [zpow_neg, RelIso.inv_apply_self] at this
  simp  only[←zpow_neg, add_pows] at this
  have := incr_up_pos incr this
  omega

/--
  If `f` is decreasing at `x` and `(f ^ z) x < (f ^ w) x`,
  then `w < z`.
-/
theorem decr_gt_pow_lt {f : α ≃o α} {x : α} {z w : ℤ}
    (incr : isDecreasingAt f x) (gt : (f^z) x < (f^w) x) : w < z := by
  have : (f ^ (-w)) ((f^z) x) < (f ^ (-w)) ((f^w) x) :=
    OrderIso.GCongr.orderIso_apply_lt_apply (f ^ (-w)) gt
  simp only [zpow_neg, RelIso.inv_apply_self] at this
  simp  only[←zpow_neg, add_pows] at this
  have := decr_down_pos incr this
  omega

/--
  If `f` is increasing at `x` and `z < w`,
  then `(f ^ z) x < (f ^ w) x`.
-/
theorem incr_pow_gt_gt {f : α ≃o α} {x : α} {z w : ℤ}
    (incr : isIncreasingAt f x) (pow_gt : z < w) : (f^z) x < (f^w) x := by
  apply_fun (f^(-z))
  simp only [zpow_neg, RelIso.inv_apply_self]
  simp only [←zpow_neg, add_pows]
  apply incr_pos_gt incr
  omega

/--
  If `f` is decreasing at `x` and `z < w`,
  then `(f ^ w) x < (f ^ z) x`.
-/
theorem decr_pow_gt_gt {f : α ≃o α} {x : α} {z w : ℤ}
    (decr : isDecreasingAt f x) (pow_gt : z < w) : (f^w) x < (f^z) x := by
  apply_fun (f^(-w))
  simp only [zpow_neg, RelIso.inv_apply_self]
  simp only [←zpow_neg, add_pows]
  apply decr_neg_gt decr
  omega

/--
  If `f` is increasing at `x` and `(f ^ z) x = (f ^ w) x`,
  then `z = w`.
-/
theorem incr_eq_pow_eq {f : α ≃o α} {x : α} {z w : ℤ}
    (incr : isIncreasingAt f x) (eq : (f ^ z) x = (f ^ w) x) :
    z = w := by
  obtain z_lt_w | z_eq_w | w_lt_z := Int.lt_trichotomy z w
  · have := incr_pow_gt_gt incr z_lt_w
    order
  · trivial
  · have := incr_pow_gt_gt incr w_lt_z
    order

/--
  If `f` is decreasing at `x` and `(f ^ z) x = (f ^ w) x`,
  then `z = w`.
-/
theorem decr_eq_pow_eq {f : α ≃o α} {x : α} {z w : ℤ}
    (decr : isDecreasingAt f x) (eq : (f ^ z) x = (f ^ w) x) :
    z = w := by
  obtain z_lt_w | z_eq_w | w_lt_z := Int.lt_trichotomy z w
  · have := decr_pow_gt_gt decr z_lt_w
    order
  · trivial
  · have := decr_pow_gt_gt decr w_lt_z
    order

/--
  If `f` is increasing at `x` and `(f ^ z) x ≤ (f ^ w) x`,
  then `z ≤ w`.
-/
theorem incr_ge_pow_ge {f : α ≃o α} {x : α} {z w : ℤ}
    (incr : isIncreasingAt f x) (ge : (f^z) x ≤ (f^w) x) : z ≤ w := by
  obtain eq | gt := ge.eq_or_gt
  · exact (incr_eq_pow_eq incr eq).symm.le
  · exact (incr_gt_pow_gt incr gt).le

/--
  If `f` is decreasing at `x` and `(f ^ z) x ≤ (f ^ w) x`,
  then `w ≤ z`.
-/
theorem decr_ge_pow_ge {f : α ≃o α} {x : α} {z w : ℤ}
    (decr : isDecreasingAt f x) (ge : (f^z) x ≤ (f^w) x) : w ≤ z := by
  obtain eq | gt := ge.eq_or_gt
  · exact (decr_eq_pow_eq decr eq).le
  · exact (decr_gt_pow_lt decr gt).le

/--
  If `f x = x`, then for any integer `z`,
  `(f ^ z) x = x`.
-/
theorem fixed_all_pow_eq {f : α ≃o α} {x : α}
    (fixed : f x = x) (z : ℤ) : (f ^ z) x = x := by
  induction z with
  | zero => simp
  | succ i ih => rw [add_comm, ←add_pows, ih, zpow_one, fixed]
  | pred i ih =>
    rw [neg_sub_comm, ←sub_pows, ih]
    apply_fun f
    simp [fixed]
