import Mathlib
import AutLinOrd.Pow

variable {α : Type*} [LinearOrder α]

/--
  `f` is increasing at `x` if
  `x < f x`.
-/
abbrev isIncreasingAt (f : α ≃o α) (x : α) := x < f x
abbrev isDecreasingAt (f : α ≃o α) (x : α) := f x < x

theorem incr_plus_one_pow {f : α ≃o α} {x : α} (incr : isIncreasingAt f x)
    (z : ℤ) : (f ^ z) x < (f ^ (z + 1)) x := by
  simp [←add_pows, incr]

theorem decr_plus_one_pow {f : α ≃o α} {x : α} (decr : isDecreasingAt f x)
    (z : ℤ) : (f ^ (z + 1)) x < (f ^ z) x := by
  simp [←add_pows, decr]

theorem incr_minus_one_pow {f : α ≃o α} {x : α} (incr : isIncreasingAt f x)
    (z : ℤ) : (f ^ (z - 1)) x < (f ^ z) x := by
  apply_fun f
  simp [add_pows_one, incr_plus_one_pow,
    show 1 + z = z + 1 by omega, incr_plus_one_pow incr z]

theorem decr_minus_one_pow {f : α ≃o α} {x : α} (decr : isDecreasingAt f x)
    (z : ℤ) : (f ^ z) x < (f ^ (z - 1)) x := by
  apply_fun f
  simp [add_pows_one, decr_plus_one_pow,
    show 1 + z = z + 1 by omega, decr_plus_one_pow decr z]

/--
  If `f` is increasing at `x`, then for any
  positive integer `z`, `x < (f ^ z) x`.
-/
theorem incr_pos_gt {f : α ≃o α} {x : α} {z : ℤ}
    (incr : isIncreasingAt f x) (pos : 0 < z) : x < (f ^ z) x  := by
  induction z with
  | hz => simp at pos
  | hp i ih =>
    by_cases is_zero : i = 0
    · simp [is_zero, incr]
    · calc x
      _ < (f ^ (i : ℕ)) x := ih (by omega)
      _ < (f ^ ((i : ℕ) + 1)) x := by simp [←add_pows_n, incr]
  | hn i _ => omega

/--
  If `f` is increasing at `x`, then for any
  negative integer `z`, `(f ^ z) x < x`.
-/
theorem incr_neg_lt {f : α ≃o α} {x : α} {z : ℤ}
    (incr : isIncreasingAt f x) (neg : z < 0) : (f ^ z) x < x  := by
  induction z with
  | hz => simp at neg
  | hp i _ => omega
  | hn i ih =>
    by_cases is_zero : i = 0
    · rw [is_zero]
      apply_fun f
      simp [incr]
    · calc (f ^ (-(i : ℤ) - 1)) x
      _ < (f ^ (-(i : ℤ))) x := incr_minus_one_pow incr (-(i : ℤ))
      _ < x := ih (by omega)

theorem decr_neg_gt {f : α ≃o α} {x : α} {z : ℤ}
    (decr : isDecreasingAt f x) (neg : z < 0) : x < (f ^ z) x  := by
  induction z with
  | hz => simp at neg
  | hp i _ => omega
  | hn i ih =>
    by_cases is_zero : i = 0
    · rw [is_zero]
      apply_fun f
      simp [decr]
    · calc x
      _ < (f ^ (-(i : ℤ))) x := ih (by omega)
      _ < (f ^ (-(i : ℤ) - 1)) x := decr_minus_one_pow decr (-(i : ℤ))

theorem incr_up_pos {f : α ≃o α} {x : α} {z : ℤ}
    (incr : isIncreasingAt f x) (up : x < (f ^ z) x) : 0 < z := by
  obtain z_lt_zero | z_eq_zero | zero_lt_z := Int.lt_trichotomy z 0
  · have := incr_neg_lt incr z_lt_zero
    order
  · simp [z_eq_zero] at up
  · trivial

theorem decr_down_pos {f : α ≃o α} {x : α} {z : ℤ}
    (decr : isDecreasingAt f x) (down : (f ^ z) x < x) : 0 < z := by
  obtain z_lt_zero | z_eq_zero | zero_lt_z := Int.lt_trichotomy z 0
  · have := decr_neg_gt decr z_lt_zero
    order
  · simp [z_eq_zero] at down
  · trivial

theorem incr_gt_pow_gt {f : α ≃o α} {x : α} {z w : ℤ}
    (incr : isIncreasingAt f x) (gt : (f^z) x < (f^w) x) : z < w := by
  have : (f ^ (-z)) ((f^z) x) < (f ^ (-z)) ((f^w) x) :=
    OrderIso.GCongr.orderIso_apply_lt_apply (f ^ (-z)) gt
  simp only [zpow_neg, RelIso.inv_apply_self] at this
  simp  only[←zpow_neg, add_pows] at this
  have := incr_up_pos incr this
  omega

theorem decr_gt_pow_lt {f : α ≃o α} {x : α} {z w : ℤ}
    (incr : isDecreasingAt f x) (gt : (f^z) x < (f^w) x) : w < z := by
  have : (f ^ (-w)) ((f^z) x) < (f ^ (-w)) ((f^w) x) :=
    OrderIso.GCongr.orderIso_apply_lt_apply (f ^ (-w)) gt
  simp only [zpow_neg, RelIso.inv_apply_self] at this
  simp  only[←zpow_neg, add_pows] at this
  have := decr_down_pos incr this
  omega
