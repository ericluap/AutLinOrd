import AutLinOrd.ElemOrbital

/-!
  This file defines `non_decr_at f x` which is equal to either `f` or `f⁻¹`
  such that it is nondecreasing at `x`.
-/

variable {α : Type*} [LinearOrder α]

/--
  If `f` is increasing at `x` and `y` is in the orbital of `x` under `f`,
  then `f` is increasing at `y`.
-/
theorem incr_at_incr_all {f : α ≃o α} {x y : α}
    (incr : isIncreasingAt f x) (y_mem : y ∈ elem_orbital f x) :
    isIncreasingAt f y := by
  rw [mem_elem_orbital_strong_iff] at y_mem
  obtain fix | incr | decr := y_mem
  · rw [isIncreasingAt] at incr ⊢
    subst_vars
    exact OrderIso.GCongr.orderIso_apply_lt_apply f incr
  · obtain ⟨z, hz, hz1⟩ := incr
    rw [isIncreasingAt]
    have : (f ^ (z + 1)) x ≤ f y := by simp [add_comm z, ←add_pows, hz]
    order
  · obtain ⟨z, hz1, hz⟩ := decr
    rw [isIncreasingAt] at incr
    have : (f ^ (z + 1)) x < (f ^ z) x := by order
    simp [←add_pows] at this
    order

/--
  If `f` is not decreasing at `x` and `y` is in the orbital of `x` under `f`,
  then `f` is not decreasing at `y`.
-/
theorem non_decr_at_non_decr_all {f : α ≃o α} {x y : α}
    (non_decr : x ≤ f x) (y_mem : y ∈ elem_orbital f x) :
    y ≤ f y := by
  rw [mem_elem_orbital_strong_iff] at y_mem
  obtain fix | incr | decr := y_mem
  · subst_vars
    exact OrderIso.GCongr.orderIso_apply_le_apply f non_decr
  · obtain ⟨z, hz, hz1⟩ := incr
    have : (f ^ (z + 1)) x ≤ f y := by simp [add_comm z, ←add_pows, hz]
    order
  · obtain ⟨z, hz1, hz⟩ := decr
    have : (f ^ (z + 1)) x < (f ^ z) x := by order
    simp [←add_pows] at this
    order

/--
  If `f` is decreasing at `x` and `y` is in the orbital of `x` under `f`,
  then `f` is decreasing at `y`.
-/
theorem decr_at_decr_all {f : α ≃o α} {x y : α}
    (decr : f x < x) (y_mem : y ∈ elem_orbital f x) :
    f y < y := by
  rw [mem_elem_orbital_strong_iff] at y_mem
  obtain fix | incr | decr := y_mem
  · subst_vars
    exact OrderIso.GCongr.orderIso_apply_lt_apply f decr
  · obtain ⟨z, hz, hz1⟩ := incr
    have : (f ^ (z + 1)) x < (f ^ z) x := decr_plus_one_pow decr z
    order
  · obtain ⟨z, hz1, hz⟩ := decr
    have : (f ^ (z + 1)) x > f y := by simp [add_comm z, ←add_pows, hz]
    order

/--
  `non_decr_at f x` is either `f` or `f⁻¹`
  in order to make `x ≤ (non_decr_at f x) x`.
-/
def non_decr_at (f : α ≃o α) (x : α) : α ≃o α :=
  if x ≤ f x then
    f
  else
    f⁻¹

/--
  Either `x ≤ f x` and `non_decr_at f x = f` or
  `f x < x` and `non_decr_at f x = f⁻¹`.
-/
theorem non_decr_at_def (f : α ≃o α) (x : α) :
    (x ≤ f x ∧ non_decr_at f x = f) ∨ (f x < x ∧ non_decr_at f x = f⁻¹) := by
  by_cases h : x ≤ f x
  · left
    constructor
    · trivial
    · simp only [non_decr_at, ite_eq_left_iff, not_le]
      order
  · right
    constructor
    · order
    · simp [non_decr_at, h]

/--
  We have that `non_decr_at f x` is not decreasing at `x`.
-/
theorem non_decr_at_non_decr (f : α ≃o α) (x : α) :
    x ≤ (non_decr_at f x) x := by
  obtain eq | inv := non_decr_at_def f x
  · simp [eq]
  · simp only [inv, gt_iff_lt, not_lt]
    exact ((map_inv_lt_iff f⁻¹).mp inv.1).le

theorem mem_elem_orbital_non_decr {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital (non_decr_at f x) x) : y ≤ (non_decr_at f x) y :=
  non_decr_at_non_decr_all (non_decr_at_non_decr f x) y_mem

/--
  The orbital of `x` under `f⁻¹` is a subset
  of the orbital of `x` under `f`.
-/
theorem inv_subset_elem_orbital (f : α ≃o α) (x : α) :
    elem_orbital f⁻¹ x ⊆ elem_orbital f x := by
  intro y y_mem
  rw [mem_elem_orbital_iff] at y_mem ⊢
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use -l
    simpa using hl
  · use -u
    simpa using hu

/--
  The orbital of `x` under `f` is equal to the orbital
  of `x` under `f⁻¹`.
-/
theorem finv_elem_orbital_eq (f : α ≃o α) (x : α) :
    elem_orbital f x = elem_orbital f⁻¹ x := by
  apply Set.eq_of_subset_of_subset
  · exact inv_subset_elem_orbital f⁻¹ x
  · exact inv_subset_elem_orbital f x

/--
  The orbital of `x` under `f` is equal to the orbital
  of `x` under `non_decr_at f x`.
-/
theorem non_decr_eq_elem_orbital (f : α ≃o α) (x : α) :
    elem_orbital f x = elem_orbital (non_decr_at f x) x := by
  obtain eq | inv := non_decr_at_def f x
  · simp [eq]
  · simp [inv, ←finv_elem_orbital_eq]

/--
  If `y` is in the orbital of `x` under `f`,
  then `y ≤ (non_decr_at f x) y`.
-/
  theorem mem_orig_elem_orbital_non_decr {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) : y ≤ (non_decr_at f x) y :=
  non_decr_at_non_decr_all (non_decr_at_non_decr f x)
    ((non_decr_eq_elem_orbital f x) ▸ y_mem)

/--
  If `y` is in the oribtal of `x` under `non_decr_at f x`,
  then `f y ≤ (non_decr_at f x) y`.
-/
theorem mem_elem_orbital_image_non_decr {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital (non_decr_at f x) x) :
    f y ≤ (non_decr_at f x) y := by
  obtain eq | ⟨inv, f_eq⟩ := non_decr_at_def f x
  · simp [eq]
  · have : f y < y := decr_at_decr_all inv
      ((non_decr_eq_elem_orbital f x) ▸ y_mem)
    have : y ≤ (non_decr_at f x) y := mem_elem_orbital_non_decr y_mem
    order

/--
  If `y` is in the orbital of `f` under `x`,
  then `f y ≤ (non_decr_at f x) y`.
-/
theorem mem_orig_elem_orbital_image_non_decr {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) :
    f y ≤ (non_decr_at f x) y := by
  obtain eq | ⟨inv, f_eq⟩ := non_decr_at_def f x
  · simp [eq]
  · have : f y < y := decr_at_decr_all inv y_mem
    have : y ≤ (non_decr_at f x) y := mem_elem_orbital_non_decr
      ((non_decr_eq_elem_orbital f x) ▸ y_mem)
    order

/--
  If `y` is in the orbital of `x` under `non_decr_at f x`,
  then for any integer `z`,
  `(f ^ z) y` is in the orbital of `x` under `non_decr_at f x`.
-/
theorem pow_orig_mem_non_decr_elem_orbital {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital (non_decr_at f x) x) (z : ℤ) :
    (f ^ z) y ∈ elem_orbital (non_decr_at f x) x := by
  rw [←non_decr_eq_elem_orbital] at y_mem
  have : (f^z) y ∈ elem_orbital f x := pow_mem_elem_orbital z y_mem
  rw [non_decr_eq_elem_orbital] at this
  exact this

/--
  If `y` is in the orbital of `x` under `non_decr_at f x`,
  then `f y` is in the orbital of `x` under `non_decr_at f x`.
-/
theorem pow_orig_mem_non_decr_elem_orbital_one {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital (non_decr_at f x) x) :
    f y ∈ elem_orbital (non_decr_at f x) x :=
  pow_orig_mem_non_decr_elem_orbital y_mem 1

/--
  If `y` is in the orbital of `x` under `f`,
  then `non_decr_at f x ^ z` is in the orbital of `x` under `f`.
-/
theorem orig_mem_orbital_pow_mem_orbital {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) (z : ℤ) :
    (non_decr_at f x ^ z) y ∈ elem_orbital f x := by
  rw [non_decr_eq_elem_orbital] at y_mem ⊢
  exact pow_mem_elem_orbital z y_mem

/--
  `(non_decr_at f x) x = x` if and only if `f x = x`.
-/
theorem non_decr_at_fix_iff_orig_fix {f : α ≃o α} {x : α} :
   (non_decr_at f x) x = x ↔ f x = x := by
  obtain ⟨b, eq⟩ | ⟨a, eq⟩ := non_decr_at_def f x
  · simp [eq]
  · have : x < f⁻¹ x := (map_inv_lt_iff f⁻¹).mp a
    rw [←eq] at this
    constructor
    <;> order

/--
  If `(non_decr_at f x) x ≠ x`, then
  `y` is an element of the orbital of `x` under `f`
  if and only if
  there exists a `z` such that
  `(non_decr_at f x)^z x ≤ y < (non_decr_at f x)^(z+1) x`.
-/
theorem not_fix_non_decr_mem_orbital_strong_iff {f : α ≃o α} {x y : α}
    (not_fix : (non_decr_at f x) x ≠ x) : y ∈ elem_orbital f x ↔
    (∃z : ℤ, ((non_decr_at f x) ^ z) x ≤ y ∧
    y < ((non_decr_at f x) ^ (z + 1)) x) := by
  constructor
  · intro x_mem_f
    rw [non_decr_eq_elem_orbital] at x_mem_f
    obtain fix | incr | decr :=
      (mem_elem_orbital_strong_iff (non_decr_at f x) x y).mp x_mem_f
    · use 1
      simp only [zpow_one, fix, le_refl, Int.reduceAdd, true_and]
      simp only [←fix, show (2 : ℤ) = 1+1 by simp,
        ←add_pows, zpow_one, OrderIso.lt_iff_lt]
      obtain lt | eq := (non_decr_at_non_decr f x).lt_or_eq
      · trivial
      · order
    · trivial
    · obtain ⟨z, hlz, huz⟩ := decr
      simp [←add_pows] at hlz
      have : (non_decr_at f x ^ z) ((non_decr_at f x) x) <
          (non_decr_at f x ^ z) x := by order
      simp only [OrderIso.lt_iff_lt] at this
      have : x ≤ (non_decr_at f x) x := non_decr_at_non_decr f x
      order
  · intro incr
    rw [non_decr_eq_elem_orbital, mem_elem_orbital_strong_iff]
    right
    left
    trivial

/--
  If `z < w`,
  then `(non_decr_at f x ^ z) x ≤ (non_decr_at f x ^ w) x`.
-/
theorem non_decr_at_pow_gt_ge {f : α ≃o α} {x : α} {z w : ℤ}
    (pow_gt : z < w) : (non_decr_at f x ^ z) x ≤ (non_decr_at f x ^ w) x := by
  obtain eq | lt := non_decr_at_non_decr f x |>.eq_or_lt
  · simp [fix_pow_fix eq.symm z, fix_pow_fix eq.symm w]
  · exact (incr_pow_gt_gt lt pow_gt).le

/--
  If `z ≤ w`,
  then `(non_decr_at f x ^ z) x ≤ (non_decr_at f x ^ w) x`.
-/
theorem non_decr_at_pow_ge_ge {f : α ≃o α} {x : α} {z w : ℤ}
    (pow_ge : z ≤ w) : (non_decr_at f x ^ z) x ≤ (non_decr_at f x ^ w) x := by
  obtain eq_pow | lt_pow := pow_ge.eq_or_lt
  · simp [eq_pow]
  · exact non_decr_at_pow_gt_ge lt_pow
