import AutLinOrd.NonDecrAt
import AutLinOrd.OrbitalAt

variable {α : Type*} [LinearOrder α]

/--
  For an automorphism `f` and element `x`,
  `orbital_at_non_decr f x` is an automorphism which
  is the same as `f` on its orbital at `x` except increasing,
  and is the identity everywhere else.
-/
noncomputable def orbital_at_non_decr (f : α ≃o α) (x : α) : α ≃o α :=
  orbital_at (non_decr_at f x) x

/--
  The orbital of `x` under `f` is the equal to the
  orbital of `x` under `orbital_at_non_decr f x`.
-/
theorem orbital_at_non_decr_orbital_eq (f : α ≃o α) (x : α) :
    elem_orbital f x = elem_orbital (orbital_at_non_decr f x) x := by
  rw [orbital_at_non_decr, orbital_at_eq_orbital, non_decr_eq_elem_orbital]

/--
  For all `y`, `y ≤ (orbital_at_non_decr f x) y `.
-/
theorem non_decr_orbital_at_non_decr {f : α ≃o α} {x y : α} :
    y ≤ (orbital_at_non_decr f x) y := by
  by_cases h : y ∈ elem_orbital (non_decr_at f x) x
  <;> simp [orbital_at_non_decr, orbital_at, h, mem_elem_orbital_non_decr]

/--
  For any `y` and natural number `n`,
  `y ≤ (orbital_at_non_decr f x)^n y`.
-/
theorem pow_non_decr_orbital_at_non_decr {f : α ≃o α} {x y : α} {n : ℕ} :
    y ≤ ((orbital_at_non_decr f x)^n) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [add_comm n, ← add_pows_n, pow_one]
    transitivity (orbital_at_non_decr f x ^ n) y
    · exact ih
    · exact non_decr_orbital_at_non_decr

/--
  For all `y`, `(orbital_at_non_decr f x)⁻¹ y ≤ y  `.
-/
theorem inv_non_decr_orbital_at_non_decr {f : α ≃o α} {x y : α} :
    (orbital_at_non_decr f x)⁻¹ y ≤ y := by
  refine (OrderIso.symm_apply_le (orbital_at_non_decr f x)).mpr ?_
  exact non_decr_orbital_at_non_decr

/--
  For all `y` and natural number `n`,
  `(orbital_at_non_decr f x ^ n)⁻¹ y ≤ y  `.
-/
theorem pow_inv_non_decr_orbital_at_non_decr {f : α ≃o α} {x y : α} {n : ℕ} :
    (orbital_at_non_decr f x ^ n)⁻¹ y ≤ y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [←zpow_natCast _ (n+1), ←zpow_neg _ (n+1 : ℤ), ←add_pows]
    transitivity (orbital_at_non_decr f x ^ n)⁻¹ y
    · exact inv_non_decr_orbital_at_non_decr
    · exact ih

/--
  If `y` is in the orbital of `x` under `f`,
  then `(orbital_at_non_decr f x) y = (non_decr f x) y`.
-/
theorem mem_orbital_at_non_decr_eq {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) :
    orbital_at_non_decr f x y = (non_decr_at f x) y := by
  simp only [orbital_at_non_decr, orbital_at, RelIso.coe_fn_mk,
    Equiv.coe_fn_mk, ite_eq_left_iff]
  intro h
  rw [←non_decr_eq_elem_orbital] at h
  contradiction

/--
  If `y` is not in the orbital of `x` under `f`,
  then `(orbital_at_non_decr f x) y = y`.
-/
theorem not_mem_orbital_at_non_decr_eq {f : α ≃o α} {x y : α}
    (y_not_mem : y ∉ elem_orbital f x) : orbital_at_non_decr f x y = y := by
  simp only [orbital_at_non_decr, orbital_at, RelIso.coe_fn_mk,
    Equiv.coe_fn_mk, ite_eq_right_iff]
  intro h
  rw [←non_decr_eq_elem_orbital] at h
  contradiction

/--
  If `(orbital_at_non_decr f x) x = x`,
  then `f x = x`.
-/
theorem fix_orig_fix {f : α ≃o α} {x : α}
    (fix : orbital_at_non_decr f x x = x) : f x = x := by
  rw [mem_orbital_at_non_decr_eq] at fix
  · exact non_decr_at_fix_iff_orig_fix.mp fix
  · exact mem_elem_orbital_reflexive f x
