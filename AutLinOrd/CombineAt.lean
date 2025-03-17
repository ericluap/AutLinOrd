import AutLinOrd.OrbitalAtNonDecr

variable {α : Type*} [LinearOrder α]

/--
  Given automorphisms `f` and `g` and an element `x`,
  `combine_at f g x` is an automorphism whose orbital at
  `x` is the union of that of `f` and `g`.
-/
noncomputable def combine_at (f g : α ≃o α) (x : α) : α ≃o α :=
  (orbital_at_non_decr f x).trans (orbital_at_non_decr g x)

/--
  For any `y`, we have that `y ≤ (combine_at f g x) y`.
-/
theorem not_decr_combine_at (f g : α ≃o α) (x y : α) :
    y ≤ (combine_at f g x) y := by
  rw [combine_at]
  transitivity (orbital_at_non_decr f x) y
  <;> exact non_decr_orbital_at_non_decr

/--
  For any `y` in the orbital of `x` under `f`,
  `(orbital_at_non_decr f x) y ≤ (combine_at f g x) y`.
-/
theorem f_le_combine_at {f : α ≃o α} (g : α ≃o α) {x y : α} :
    orbital_at_non_decr f x y ≤ (combine_at f g x) y := by
  rw [combine_at]
  exact non_decr_orbital_at_non_decr

/--
  For any `y` in the orbital of `x` under `f`,
  `(orbital_at_non_decr f x) y ≤ (combine_at f g x) y`.
-/
theorem inv_f_ge_combine_at {f : α ≃o α} (g : α ≃o α) {x y : α} :
    (combine_at f g x).symm y ≤ (orbital_at_non_decr f x).symm y := by
  rw [combine_at]
  simp only [OrderIso.symm_trans_apply, map_le_map_iff]
  exact inv_non_decr_orbital_at_non_decr

/--
  For any `y` in the orbital of `x` under `f`,
  `(orbital_at_non_decr g x) y ≤ (combine_at f g x) y`.
-/
theorem g_le_combine_at {g : α ≃o α} (f : α ≃o α) {x y : α} :
    orbital_at_non_decr g x y ≤ (combine_at f g x) y := by
  simp only [combine_at, OrderIso.trans_apply, map_le_map_iff]
  exact non_decr_orbital_at_non_decr

/--
  For any `y` and natural number `n`,
  `(orbital_at_non_decr f x)^n y ≤ (combine_at f g x)^n y`.
-/
theorem pow_f_le_combine_at {f g : α ≃o α} {x y : α} (n : ℕ) :
    ((orbital_at_non_decr f x)^n) y ≤ ((combine_at f g x)^n) y := by
  induction n with
  | zero => simp
  | succ i ih =>
    norm_cast at ih ⊢
    simp only [add_comm i, ← add_pows_n, pow_one, combine_at, OrderIso.trans_apply]
    transitivity (orbital_at_non_decr f x) ((combine_at f g x ^ i) y)
    · simp only [map_le_map_iff, ih]
    · exact non_decr_orbital_at_non_decr

/--
  For any `y` and natural number `n`,
  `(combine_at f g x)^(-n) y ≤ (orbital_at_non_decr f x)^(-n) y`.
-/
theorem pow_f_inv_ge_combine_at {f g : α ≃o α} {x y : α} (n : ℕ) :
    ((combine_at f g x)^(-n : ℤ)) y ≤ ((orbital_at_non_decr f x)^(-n : ℤ)) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [zpow_neg, zpow_natCast, Nat.cast_add, Nat.cast_one,
      neg_add_rev, Int.reduceNeg, ←add_pows, zpow_one] at ih ⊢
    calc (combine_at f g x).symm ((combine_at f g x ^ n)⁻¹ y)
    _ ≤ (orbital_at_non_decr f x).symm ((combine_at f g x ^ n)⁻¹ y) :=
      inv_f_ge_combine_at g
    _ ≤ (orbital_at_non_decr f x).symm ((orbital_at_non_decr f x ^ n)⁻¹ y) := by
      simp only [map_le_map_iff, ih]

/--
  If there exists an integer `z` such that
  `(orbital_at_non_decr f x)^z x ≤ y`, then
  there exists an integer `l` such that
  `(combine_at f g x)^l x ≤ y`.
-/
theorem pow_f_le_pow_combine_le {f g : α ≃o α} {x y : α} {z : ℤ}
    (pow_f_le : ((orbital_at_non_decr f x)^z) x ≤ y) :
    ∃l : ℤ, ((combine_at f g x)^l) x ≤ y := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_natCast] at pow_f_le
    use 0
    simp only [zpow_zero, RelIso.coe_one, id_eq]
    transitivity (orbital_at_non_decr f x ^ n) x
    · exact pow_non_decr_orbital_at_non_decr
    · exact pow_f_le
  | negSucc n =>
    simp only [zpow_negSucc] at pow_f_le
    use Int.negSucc n
    simp only [zpow_negSucc]
    transitivity (orbital_at_non_decr f x ^ (n + 1))⁻¹ x
    · exact pow_f_inv_ge_combine_at (n+1)
    · exact pow_f_le

/--
  If there exists an integer `z` such that
  `y ≤ (orbital_at_non_decr f x)^z x`, then
  there exists an integer `u` such that
  `y ≤ (combine_at f g x)^u x`.
-/
theorem pow_f_ge_combine_ge {f g : α ≃o α} {x y : α} {z : ℤ}
    (pow_f_ge : y ≤ ((orbital_at_non_decr f x)^z) x) :
    ∃u : ℤ, y ≤ ((combine_at f g x)^u) x := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_natCast] at pow_f_ge
    use n
    transitivity (orbital_at_non_decr f x ^ n) x
    · exact pow_f_ge
    · simp only [zpow_natCast]
      exact pow_f_le_combine_at n
  | negSucc n =>
    simp at pow_f_ge
    use 0
    simp only [zpow_zero, RelIso.coe_one, id_eq]
    transitivity (orbital_at_non_decr f x ^ (n + 1))⁻¹ x
    · exact pow_f_ge
    · exact pow_inv_non_decr_orbital_at_non_decr

/--
  If there exists a `y` such that
  `(orbital_at_non_decr f x) x = y`,
  then there exists an integer `l` such that
  `(combine_at f g x)^l x ≤ y`.
-/
theorem f_fix_combine_le {f g : α ≃o α} {x y : α}
    (fix : (orbital_at_non_decr f x) x = y) :
    ∃l : ℤ, ((combine_at f g x)^l) x ≤ y := by
  use 0
  simp only [zpow_zero, RelIso.coe_one, id_eq]
  transitivity (orbital_at_non_decr f x) x
  · exact non_decr_orbital_at_non_decr
  · exact fix.le

/--
  If there exists a `y` such that
  `(orbital_at_non_decr f x) x = y`,
  then there exists an integer `u` such that
  `y ≤ (combine_at f g x)^u x`.
-/
theorem f_fix_combine_ge {f g : α ≃o α} {x y : α}
    (fix : (orbital_at_non_decr f x) x = y) :
    ∃u : ℤ, y ≤ ((combine_at f g x)^u) x := by
  use 1
  simp
  transitivity (orbital_at_non_decr f x) x
  · exact fix.symm.le
  · exact non_decr_orbital_at_non_decr

/--
  If `y` is in the orbital of `x` under `f`,
  then `y` is in the orbital of `x` under `combine_at f g x`.
-/
theorem f_in_combine_map {f : α ≃o α} (g : α ≃o α) {x y : α}
    (y_mem : y ∈ elem_orbital f x) : y ∈ elem_orbital (combine_at f g x) x := by
  rw [orbital_at_non_decr_orbital_eq, mem_elem_orbital_strong_iff] at y_mem
  obtain fix | ⟨z, z_le, lt_z⟩ | ⟨z, le_z, z_lt⟩ := y_mem
  · simp only [combine_at, mem_elem_orbital_iff]
    constructor
    · exact f_fix_combine_le fix
    · exact f_fix_combine_ge fix
  · simp only [mem_elem_orbital_iff]
    constructor
    · exact pow_f_le_pow_combine_le z_le
    · exact pow_f_ge_combine_ge lt_z.le
  · simp [mem_elem_orbital_iff]
    constructor
    · exact pow_f_le_pow_combine_le le_z
    · exact pow_f_ge_combine_ge z_lt.le
