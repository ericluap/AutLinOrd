import AutLinOrd.ElemOrbital

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

theorem mem_elem_orbital_image_non_decr {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital (non_decr_at f x) x) :
    f y ≤ (non_decr_at f x) y := by
  obtain eq | ⟨inv, f_eq⟩ := non_decr_at_def f x
  · simp [eq]
  · have : f y < y := decr_at_decr_all inv
      ((non_decr_eq_elem_orbital f x) ▸ y_mem)
    have : y ≤ (non_decr_at f x) y := mem_elem_orbital_non_decr y_mem
    order

theorem pow_orig_mem_non_decr_elem_orbital {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital (non_decr_at f x) x) (z : ℤ) :
    (f ^ z) y ∈ elem_orbital (non_decr_at f x) x := by
  rw [←non_decr_eq_elem_orbital] at y_mem
  have : (f^z) y ∈ elem_orbital f x := pow_mem_elem_orbital z y_mem
  rw [non_decr_eq_elem_orbital] at this
  exact this

theorem pow_orig_mem_non_decr_elem_orbital_one {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital (non_decr_at f x) x) :
    f y ∈ elem_orbital (non_decr_at f x) x :=
  pow_orig_mem_non_decr_elem_orbital y_mem 1
