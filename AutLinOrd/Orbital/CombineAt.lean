import AutLinOrd.Orbital.OrbitalAtNonDecr

/-!
  This files defines `combine_at f g x` which is an automorphism whose orbital
  at `x` is the union of that of `f` and `g`.
-/

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
  `(combine_at f g x).symm y ≤ (orbital_at_non_decr f x) y`.
-/
theorem inv_f_ge_combine_at {f : α ≃o α} (g : α ≃o α) {x y : α} :
    (combine_at f g x).symm y ≤ (orbital_at_non_decr f x).symm y := by
  rw [combine_at]
  simp only [OrderIso.symm_trans_apply, map_le_map_iff]
  exact inv_non_decr_orbital_at_non_decr

/--
  For any `y` in the orbital of `x` under `f`,
  `(combine_at f g x).symm y ≤ (orbital_at_non_decr g x) y`.
-/
theorem inv_g_ge_combine_at {g : α ≃o α} (f : α ≃o α) {x y : α} :
    (combine_at f g x).symm y ≤ (orbital_at_non_decr g x).symm y := by
  rw [combine_at]
  simp only [OrderIso.symm_trans_apply]
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
  `(orbital_at_non_decr g x)^n y ≤ (combine_at f g x)^n y`.
-/
theorem pow_g_le_combine_at {f g : α ≃o α} {x y : α} (n : ℕ) :
    ((orbital_at_non_decr g x)^n) y ≤ ((combine_at f g x)^n) y := by
  induction n with
  | zero => simp
  | succ i ih =>
    norm_cast at ih ⊢
    simp only [add_comm i, ← add_pows_n, pow_one, combine_at, OrderIso.trans_apply]
    transitivity (orbital_at_non_decr g x) ((combine_at f g x ^ i) y)
    · simp only [map_le_map_iff, ih]
    · simp only [map_le_map_iff]
      exact non_decr_orbital_at_non_decr

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
  For any `y` and natural number `n`,
  `(combine_at f g x)^(-n) y ≤ (orbital_at_non_decr g x)^(-n) y`.
-/
theorem pow_g_inv_ge_combine_at {f g : α ≃o α} {x y : α} (n : ℕ) :
    ((combine_at f g x)^(-n : ℤ)) y ≤ ((orbital_at_non_decr g x)^(-n : ℤ)) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [zpow_neg, zpow_natCast, Nat.cast_add, Nat.cast_one,
      neg_add_rev, Int.reduceNeg, ←add_pows, zpow_one] at ih ⊢
    calc (combine_at f g x).symm ((combine_at f g x ^ n)⁻¹ y)
    _ ≤ (orbital_at_non_decr g x).symm ((combine_at f g x ^ n)⁻¹ y) :=
      inv_g_ge_combine_at f
    _ ≤ (orbital_at_non_decr g x).symm ((orbital_at_non_decr g x ^ n)⁻¹ y) := by
      simp [ih]

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
    simp only [Int.ofNat_eq_natCast, zpow_natCast] at pow_f_le
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
  `(orbital_at_non_decr g x)^z x ≤ y`, then
  there exists an integer `l` such that
  `(combine_at f g x)^l x ≤ y`.
-/
theorem pow_g_le_pow_combine_le {f g : α ≃o α} {x y : α} {z : ℤ}
    (pow_g_le : ((orbital_at_non_decr g x)^z) x ≤ y) :
    ∃l : ℤ, ((combine_at f g x)^l) x ≤ y := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast] at pow_g_le
    use 0
    simp only [zpow_zero, RelIso.coe_one, id_eq]
    transitivity (orbital_at_non_decr g x ^ n) x
    · exact pow_non_decr_orbital_at_non_decr
    · exact pow_g_le
  | negSucc n =>
    simp only [zpow_negSucc] at pow_g_le
    use Int.negSucc n
    simp only [zpow_negSucc]
    transitivity (orbital_at_non_decr g x ^ (n + 1))⁻¹ x
    · exact pow_g_inv_ge_combine_at (n+1)
    · exact pow_g_le

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
    simp only [Int.ofNat_eq_natCast, zpow_natCast] at pow_f_ge
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
  If there exists an integer `z` such that
  `y ≤ (orbital_at_non_decr g x)^z x`, then
  there exists an integer `u` such that
  `y ≤ (combine_at f g x)^u x`.
-/
theorem pow_g_ge_combine_ge {f g : α ≃o α} {x y : α} {z : ℤ}
    (pow_g_ge : y ≤ ((orbital_at_non_decr g x)^z) x) :
    ∃u : ℤ, y ≤ ((combine_at f g x)^u) x := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast] at pow_g_ge
    use n
    transitivity (orbital_at_non_decr g x ^ n) x
    · exact pow_g_ge
    · simp only [zpow_natCast]
      exact pow_g_le_combine_at n
  | negSucc n =>
    simp at pow_g_ge
    use 0
    simp only [zpow_zero, RelIso.coe_one, id_eq]
    transitivity (orbital_at_non_decr g x ^ (n + 1))⁻¹ x
    · exact pow_g_ge
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
  `(orbital_at_non_decr g x) x = y`,
  then there exists an integer `l` such that
  `(combine_at f g x)^l x ≤ y`.
-/
theorem g_fix_combine_le {f g : α ≃o α} {x y : α}
    (fix : (orbital_at_non_decr g x) x = y) :
    ∃l : ℤ, ((combine_at f g x)^l) x ≤ y := by
  use 0
  simp only [zpow_zero, RelIso.coe_one, id_eq]
  transitivity (orbital_at_non_decr g x) x
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
  If there exists a `y` such that
  `(orbital_at_non_decr g x) x = y`,
  then there exists an integer `u` such that
  `y ≤ (combine_at f g x)^u x`.
-/
theorem g_fix_combine_ge {f g : α ≃o α} {x y : α}
    (fix : (orbital_at_non_decr g x) x = y) :
    ∃u : ℤ, y ≤ ((combine_at f g x)^u) x := by
  use 1
  simp
  transitivity (orbital_at_non_decr g x) x
  · exact fix.symm.le
  · simp only [combine_at, OrderIso.trans_apply, map_le_map_iff]
    exact non_decr_orbital_at_non_decr

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

/--
  If `y` is in the orbital of `x` under `g`,
  then `y` is in the orbital of `x` under `combine_at f g x`.
-/
theorem g_in_combine_map {g : α ≃o α} (f : α ≃o α) {x y : α}
    (y_mem : y ∈ elem_orbital g x) : y ∈ elem_orbital (combine_at f g x) x := by
  rw [orbital_at_non_decr_orbital_eq, mem_elem_orbital_strong_iff] at y_mem
  obtain fix | ⟨z, z_le, lt_z⟩ | ⟨z, le_z, z_lt⟩ := y_mem
  · simp only [combine_at, mem_elem_orbital_iff]
    constructor
    · exact g_fix_combine_le fix
    · exact g_fix_combine_ge fix
  · simp only [mem_elem_orbital_iff]
    constructor
    · exact pow_g_le_pow_combine_le z_le
    · exact pow_g_ge_combine_ge lt_z.le
  · simp [mem_elem_orbital_iff]
    constructor
    · exact pow_g_le_pow_combine_le le_z
    · exact pow_g_ge_combine_ge z_lt.le

/--
  The union of the orbital of `x` under `f`
  and the orbital of `x` under `g` is a subset
  of the orbital of `x` under `combine_at f g x`.
-/
theorem f_g_orbital_subset_combine_orbital (f g : α ≃o α) (x : α) :
    elem_orbital f x ∪ elem_orbital g x
      ⊆ elem_orbital (combine_at f g x) x := by
  simp only [Set.union_subset_iff]
  constructor
  · intro z hz
    exact f_in_combine_map g hz
  · intro z hz
    exact g_in_combine_map f hz

theorem combine_orbital_subset_f_g_orbital (f g : α ≃o α) (x : α) :
    elem_orbital (combine_at f g x) x ⊆
      elem_orbital f x ∪ elem_orbital g x := by
  intro z hz
  -- assume that `z` is in neither orbital of `x`
  by_contra!
  simp only [Set.mem_union, not_or] at this
  obtain ⟨z_not_mem_f, z_not_mem_g⟩ := this
  rw [non_decr_eq_elem_orbital] at z_not_mem_f z_not_mem_g
  -- then `z` must be fixed by `combine_at f g x`
  have : combine_at f g x z = z := by
    simp [combine_at, orbital_at_non_decr, orbital_at,
      z_not_mem_f, z_not_mem_g]
  -- since `z` is fixed and in the orbital of `combine_at f g x`, `x = z`
  have : x = z := fix_mem_orbital_eq hz this
  -- and so `z` is not in the orbital of `z` under `f`
  simp [this, ←non_decr_eq_elem_orbital] at z_not_mem_f
  -- but this is a contradiction
  exact z_not_mem_f (mem_elem_orbital_reflexive f z)

/--
  The orbital of `x` under `combine_at f g x` is equal to
  the union of the orbital of `x` under `f` and the
  orbital of `x` under `g`.
-/
theorem combine_orbital_eq_union (f g : α ≃o α) (x : α) :
    elem_orbital (combine_at f g x) x =
      elem_orbital f x ∪ elem_orbital g x := by
  apply Set.eq_of_subset_of_subset
  · exact combine_orbital_subset_f_g_orbital f g x
  · exact f_g_orbital_subset_combine_orbital f g x

/--
  If `y` is not in the orbital of `x` under `combine_at f g x`,
  then `(combine_at f g x) y = y`.
-/
theorem not_mem_orbital_at_combine_at_eq {f g : α ≃o α} {x y : α}
    (y_not_mem : y ∉ elem_orbital (combine_at f g x) x) :
    (combine_at f g x) y = y := by
  simp only [combine_orbital_eq_union, Set.mem_union, not_or] at y_not_mem
  obtain ⟨y_not_mem_f, y_not_mem_g⟩ := y_not_mem
  rw [combine_at, OrderIso.trans_apply,
    not_mem_orbital_at_non_decr_eq y_not_mem_f,
    not_mem_orbital_at_non_decr_eq y_not_mem_g]

/--
  If `y` is not in the orbital of `x` under `(combine_at f g x)`,
  then the orbital of `y` under `(combine_at f g x)` is `{y}`.
-/
theorem not_mem_orbital_singleton {f g : α ≃o α} {x y : α}
    (y_not_mem : y ∉ elem_orbital (combine_at f g x) x) :
    elem_orbital (combine_at f g x) y = {y} :=
  fix_iff_singleton_orbital.mp (not_mem_orbital_at_combine_at_eq y_not_mem)

/--
  If `combine_at f g x` fixes `x`,
  then it fixes everything.
-/
theorem fix_at_fix_all {f g : α ≃o α} {x : α} (fix : (combine_at f g x) x = x)
    (y : α) : (combine_at f g x) y = y := by
  by_cases h : y ∈ elem_orbital (combine_at f g x) x
  · simp only [mem_elem_orbital_iff, fix_pow_fix fix, exists_const] at h
    have : x = y := by
      -- order [h.1, h.2]
      have := h.1
      have := h.2
      order
    simp [←this, fix]
  · exact not_mem_orbital_at_combine_at_eq h

/--
  If the orbital of `y` under `combine_at f g x`
  is not `{y}`, then the
  orbital of `x` under `combine_at f g x`
  is not `{x}`.
-/
theorem not_singleton_at_not_singleton {f g : α ≃o α} {x y : α}
    (not_single : ¬elem_orbital (combine_at f g x) y = {y}) :
    ¬elem_orbital (combine_at f g x) x = {x} := by
  simp only [← fix_iff_singleton_orbital] at not_single
  have := (fix_at_fix_all (y := y)).mt not_single
  rw [fix_iff_singleton_orbital] at this
  exact this
