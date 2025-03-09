import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Order.Hom.Basic
import Mathlib.Order.RelIso.Group

variable {α : Type*} [LinearOrder α]

theorem add_pows (f : α ≃o α) (z y : ℤ) (x : α) :
    (f ^ z) ((f ^ y) x) = (f ^ (z + y)) x := by
  rw [←Function.comp_apply (f := f^z)]
  simp only [←RelIso.coe_mul, ←zpow_add]

theorem sub_pows (f : α ≃o α) (z y : ℤ) (x : α) :
    (f ^ z) ((f ^ (-y)) x) = (f ^ (z - y)) x := by
  rw [show z - y = z + (-y) by omega, ←add_pows]

theorem add_pows_one (f : α ≃o α) (y : ℤ) (x : α) :
    f ((f ^ y) x) = (f ^ (1 + y)) x := by
  conv =>
    enter [1, 1]
    rw [show f = f^(1 : ℤ) by simp]
  rw [←Function.comp_apply (f := f^(1 : ℤ))]
  simp only [←RelIso.coe_mul, ←zpow_add]

theorem add_pows_n (f : α ≃o α) (z y : ℕ) (x : α) :
    (f ^ z) ((f ^ y) x) = (f ^ (z + y)) x := by
  rw [←Function.comp_apply (f := f^z)]
  simp only [←RelIso.coe_mul, ←npow_add]

theorem below_pow_any_below {f : α ≃o α} {x y : α}
    {x_exp y_exp : ℤ} (x_below_y : (f^x_exp) x ≤ (f^y_exp) y) :
    ∀z : ℤ, ∃t : ℤ, (f^z) x ≤ (f^t) y := by
  intro z
  use (z - x_exp + y_exp)
  calc (f ^ z) x
  _ = (f ^ (z - x_exp)) ((f ^ x_exp) x) := by simp [add_pows]
  _ ≤ (f ^ (z - x_exp)) ((f ^ y_exp) y) := by simpa
  _ = (f ^ (z - x_exp + y_exp)) y := by simp [add_pows]

theorem above_pow_any_above {f : α ≃o α} {x y : α}
    {x_exp y_exp : ℤ} (x_above_y : (f^y_exp) y ≤ (f^x_exp) x) :
    ∀z : ℤ, ∃t : ℤ, (f^t) y ≤ (f^z) x := by
  intro z
  use (z - x_exp + y_exp)
  have := calc (f ^ z) x
    _ = (f ^ (z - x_exp)) ((f ^ x_exp) x) := by simp [add_pows]
    _ ≥ (f ^ (z - x_exp)) ((f ^ y_exp) y) := by simpa
    _ = (f ^ (z - x_exp + y_exp)) y := by simp [add_pows]
  exact this
