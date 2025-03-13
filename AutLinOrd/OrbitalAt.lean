import AutLinOrd.ElemOrbital

variable {α : Type*} [LinearOrder α]

/--
  Let `y` be in the orbital of `x` under `f`
  and `z` not be. Then if `y < z` and `t` is any integer,
  `(f ^ t) y < z`.
-/
theorem in_not_orbital_lt {f : α ≃o α} {x y z : α}
    (y_mem : y ∈ elem_orbital f x) (z_not_mem : z ∉ elem_orbital f x)
    (lt : y < z) (t : ℤ) : (f ^ t) y < z := by
  by_contra!
  absurd z_not_mem
  apply (mem_elem_orbital_iff f x z).mpr
  simp only [mem_elem_orbital_iff, not_and, not_exists, not_le,
    forall_exists_index] at z_not_mem y_mem
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use t+u
    exact (z_not_mem l (by order) (t+u)).le
  · use t+u
    have fty_le_ftux : (f^t) y ≤ (f^t) ((f^u) x) :=
      OrderIso.GCongr.orderIso_apply_le_apply (f ^ t) hu
    rw [add_pows] at fty_le_ftux
    order

/--
  Let `y` be in the orbital of `x` under `f`
  and `z` not be. Then if `y ≤ z` and `t` is any integer,
  `(f ^ t) y ≤ z`.
-/
theorem in_not_orbital_le {f : α ≃o α} {x y z : α}
    (y_mem : y ∈ elem_orbital f x) (z_not_mem : z ∉ elem_orbital f x)
    (le : y ≤ z) (t : ℤ) : (f ^ t) y ≤ z := by
  by_contra!
  absurd z_not_mem
  apply (mem_elem_orbital_iff f x z).mpr
  simp only [mem_elem_orbital_iff, not_and, not_exists, not_le,
    forall_exists_index] at z_not_mem y_mem
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use t+u
    exact (z_not_mem l (by order) (t+u)).le
  · use t+u
    have fty_le_ftux : (f^t) y ≤ (f^t) ((f^u) x) :=
      OrderIso.GCongr.orderIso_apply_le_apply (f ^ t) hu
    rw [add_pows] at fty_le_ftux
    order

/--
  Let `y` be in the orbital of `x` under `f`
  and `z` not be. Then if `y > z` and `t` is any integer,
  `(f ^ t) y > z`.
-/
theorem in_not_orbital_gt {f : α ≃o α} {x y z : α}
    (y_mem : y ∈ elem_orbital f x) (z_not_mem : z ∉ elem_orbital f x)
    (gt : z < y) (t : ℤ) : z < (f ^ t) y := by
  by_contra!
  absurd z_not_mem
  apply (mem_elem_orbital_iff f x z).mpr
  simp only [mem_elem_orbital_iff, not_and, not_exists, not_le,
    forall_exists_index] at z_not_mem y_mem
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use t+l
    have : (f ^ t) ((f^l) x) ≤ (f ^ t) y :=
      OrderIso.GCongr.orderIso_apply_le_apply (f ^ t) hl
    rw [add_pows] at this
    order
  · use u
    order

/--
  Let `y` be in the orbital of `x` under `f`
  and `z` not be. Then if `y ≥ z` and `t` is any integer,
  `(f ^ t) y ≥ z`.
-/
theorem in_not_orbital_ge {f : α ≃o α} {x y z : α}
    (y_mem : y ∈ elem_orbital f x) (z_not_mem : z ∉ elem_orbital f x)
    (gt : z ≤ y) (t : ℤ) : z ≤ (f ^ t) y := by
  by_contra!
  absurd z_not_mem
  apply (mem_elem_orbital_iff f x z).mpr
  simp only [mem_elem_orbital_iff, not_and, not_exists, not_le,
    forall_exists_index] at z_not_mem y_mem
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use t+l
    have : (f ^ t) ((f^l) x) ≤ (f ^ t) y :=
      OrderIso.GCongr.orderIso_apply_le_apply (f ^ t) hl
    rw [add_pows] at this
    order
  · use u
    order

open Classical in
/--
  For a given automorphism `f` and element `x`,
  `orbital_at f x` keeps only the orbital of `f` containing `x`.
-/
noncomputable def orbital_at (f : α ≃o α) (x : α) : α ≃o α where
  toFun y := if y ∈ elem_orbital f x then f y else y
  invFun y := if y ∈ elem_orbital f x then f⁻¹ y else y
  left_inv := by
    rw [Function.LeftInverse]
    intro y
    by_cases h : y ∈ elem_orbital f x
    · simp only [h, ↓reduceIte, RelIso.inv_apply_self, ite_eq_left_iff]
      intro not_elem
      exact (not_elem (pow_mem_elem_orbital_one h)).elim
    · simp [h]
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro y
    by_cases h : y ∈ elem_orbital f x
    · simp only [h, ↓reduceIte, RelIso.apply_inv_self, ite_eq_left_iff]
      intro not_elem
      have := (pow_mem_elem_orbital (-1) h)
      simp only [Int.reduceNeg, zpow_neg, zpow_one] at this
      exact (not_elem this).elim
    · simp [h]
  map_rel_iff' := by
    intro a b
    by_cases h : a ∈ elem_orbital f x
    <;> by_cases h2 : b ∈ elem_orbital f x
    <;> simp only [Equiv.coe_fn_mk, h, ↓reduceIte, h2, map_le_map_iff]
    · constructor
      · intro fa_le_b
        have : f a ∈ elem_orbital f x := pow_mem_elem_orbital_one h
        have := in_not_orbital_le this h2 fa_le_b (-1)
        simpa
      · intro a_le_b
        exact in_not_orbital_le h h2 a_le_b 1
    · constructor
      · intro a_le_fb
        have : f b ∈ elem_orbital f x := pow_mem_elem_orbital_one h2
        have := in_not_orbital_ge this h a_le_fb (-1)
        simpa
      · intro a_le_b
        exact in_not_orbital_ge h2 h a_le_b 1

/--
  If `y` is in the orbital of `x` under `f`,
  then `(orbital_at f x) y = f y`.
-/
theorem orbital_at_mem_orbital (f : α ≃o α) (x : α) {y : α}
    (y_mem : y ∈ elem_orbital f x) : (orbital_at f x) y = f y := by
  simp only [orbital_at, RelIso.coe_fn_mk, Equiv.coe_fn_mk, ite_eq_left_iff]
  intro h
  contradiction

/--
  If `y` is in the orbital of `x` under `f`,
  then `(orbital_at f x)⁻¹ y = f⁻¹ y`.
-/
theorem neg_orbital_at_mem_orbital (f : α ≃o α) (x : α) {y : α}
    (y_mem : y ∈ elem_orbital f x) :
    ((orbital_at f x)^(-1 : ℤ)) y = (f^(-1 : ℤ)) y := by
  apply_fun (orbital_at f x)
  simp only [Int.reduceNeg, zpow_neg, zpow_one, RelIso.apply_inv_self]
  have := orbital_at_mem_orbital f x (pow_mem_elem_orbital (-1) y_mem)
  simpa using this.symm

/--
  If `y` is not in the orbital of `x` under `f`,
  then `(orbital_at f x) y = y`.
-/
theorem orbital_at_not_mem_orbital (f : α ≃o α) (x y : α)
    (y_not_mem : y ∉ elem_orbital f x) : (orbital_at f x) y = y := by
  simp only [orbital_at, RelIso.coe_fn_mk, Equiv.coe_fn_mk, ite_eq_right_iff]
  intro h
  contradiction

/--
  For any integer `z`, `((orbital_at f x)^z) x = (f^z) x`.
-/
theorem pow_orbital_at_eq (f : α ≃o α) (x : α) (z : ℤ) :
    ((orbital_at f x)^z) x = (f^z) x := by
  induction z with
  | hz => simp
  | hp i ih =>
    norm_cast at ih ⊢
    simp [add_comm i, ←add_pows_n, ih]
    exact orbital_at_mem_orbital f x
      (pow_mem_elem_orbital (↑i) (mem_elem_orbital_reflexive f x))
  | hn i ih =>
    rw [neg_sub_comm, ←sub_pows, ih, ←sub_pows]
    exact neg_orbital_at_mem_orbital f x
      (pow_mem_elem_orbital (-↑i) (mem_elem_orbital_reflexive f x))

/--
  The orbital of `x` under `(orbital_at f x)`
  is equal to the orbital of `x` under `f`.
-/
theorem orbital_at_eq_orbital (f : α ≃o α) (x : α) :
    elem_orbital (orbital_at f x) x = elem_orbital f x := by
  ext y
  constructor
  <;> simp [mem_elem_orbital_iff, pow_orbital_at_eq]
