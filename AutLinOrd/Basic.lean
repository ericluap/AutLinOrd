import Mathlib
import AutLinOrd.NonDecrAt
import AutLinOrd.OrbitalAt
import AutLinOrd.CombineAt

variable {α : Type*} [LinearOrder α]

/--
  The set of all non-singleton orbitals of `f`.
-/
def orbitals (f : α ≃o α) :=
  {z : Set α | ∃x : α, elem_orbital f x = z ∧ ¬∃z : α, elem_orbital f x = {z}}

/--
  An automorphism `f` is a bump if it only has
  a single orbital (that is not a singleton).
-/
def isBump (f : α ≃o α) := (orbitals f).ncard = 1

/--
  If `f` is a bump, then it has an orbital.
-/
theorem exists_orbital {f : α ≃o α} (is_bump : isBump f) :
    ∃x : Set α, x ∈ orbitals f := by
  rw [isBump, Set.ncard_eq_one] at is_bump
  obtain ⟨x, hx⟩ := is_bump
  use x
  simp [hx]

open Classical in
/--
  If `f` is a bump, then
  `orbital f` is its unique orbital.
  Otherwise, `orbital f` is the empty set.
-/
def orbital (f : α ≃o α) :=
  if h : isBump f then
    (exists_orbital h).choose
  else
    ∅

/--
  Either there exists an `x` such that
  the orbital of `f` is equal to the orbital of `x` under `f`,
  the orbital of `x` under `f` is not a singleton,
  and `f` is a bump,
  or
  the orbital of `f` is the empty set.
-/
theorem orbital_def (f : α ≃o α) :
    (∃x : α, orbital f = elem_orbital f x ∧ ¬∃z : α, elem_orbital f x = {z}
      ∧ isBump f) ∨
    (orbital f = ∅) := by
  by_cases h : isBump f
  · simp only [orbital, h, ↓reduceDIte]
    have := (exists_orbital h).choose_spec.out
    left
    grind
  · simp [orbital, h]

/--
  If `x` is an element of the orbital of `f`, then
  `f` is a bump.
-/
theorem mem_orbital_iff_bump {f : α ≃o α} {x : α}
    (mem : x ∈ orbital f) : isBump f := by
  by_contra!
  simp [orbital, this] at mem

/--
  An element `x` is in the orbital of `f`
  if and only if
  the orbital of `f` is equal to
  the orbital of `x` under `f`,
  `f` is a bump,
  and `f x ≠ x`.
-/
theorem mem_orbital_iff {f : α ≃o α} {x : α} :
    x ∈ orbital f ↔ orbital f = elem_orbital f x ∧ isBump f ∧ f x ≠ x := by
  constructor
  · intro x_mem
    by_cases h : isBump f
    · simp only [orbital, h, ↓reduceDIte] at x_mem ⊢
      have := (exists_orbital h).choose_spec
      simp only [orbitals, not_exists, Set.mem_setOf_eq] at this x_mem ⊢
      obtain ⟨z, eq_elem_orbital, not_singleton⟩ := this
      simp [←eq_elem_orbital] at x_mem ⊢
      constructor
      · exact (mem_elem_orbital_eq x_mem).symm
      · rw [fix_iff_singleton_orbital]
        have := (mem_elem_orbital_eq x_mem)
        rw [←this] at not_singleton
        specialize not_singleton x
        exact not_singleton
    · simp [orbital, h] at x_mem
  · intro eq_orbital
    rw [eq_orbital.1]
    exact mem_elem_orbital_reflexive f x

/--
  If `x` is in the orbital of `f`,
  then `(combine_at f g x) x ≠ x`.
-/
theorem mem_f_orbital_not_fixed {f g : α ≃o α} {x : α}
    (x_mem : x ∈ orbital f) : (combine_at f g x) x ≠ x := by
  intro combine_at_fix
  have := f_le_combine_at (f := f) g (x := x) (y := x)
  have : x ≤ orbital_at_non_decr f x x := non_decr_orbital_at_non_decr
  have : orbital_at_non_decr f x x = x := by order
  have : f x = x := fix_orig_fix this
  rw [mem_orbital_iff] at x_mem
  tauto

/--
  `orbital f` is `OrdConnected`.
-/
theorem isOrdConnected_orbital (f : α ≃o α) : (orbital f).OrdConnected := by
  obtain ⟨x, hx, _⟩ | y := orbital_def f
  · rw [hx]
    exact elem_orbital_ordConnected f x
  · rw [y]
    exact Set.ordConnected_empty

/--
  If `s` is an orbital of `combine_at f g x`,
  then `s` is equal to the orbital of `x` under `combine_at f g x`.
-/
theorem mem_combine_orbitals_eq_elem_orbital {f g : α ≃o α} {x : α} {s : Set α}
    (mem : s ∈ orbitals (combine_at f g x)) :
    s = elem_orbital (combine_at f g x) x := by
  simp only [orbitals, not_exists,
    Set.mem_setOf_eq, Set.mem_singleton_iff] at mem ⊢
  obtain ⟨z, hzs, not_single⟩ := mem
  rw [← hzs]
  specialize not_single z
  have := not_mem_orbital_singleton.mt not_single
  simp only [not_not] at this
  exact mem_elem_orbital_eq this

/--
  If `(combine_at f g x) ≠ x`, then
  the orbital of `x` under `combine_at f g x`
  is an orbital of `combine_at f g x`
-/
theorem elem_orbital_combine_mem_orbitals {f g : α ≃o α} {x : α}
    (not_fix : (combine_at f g x) x ≠ x) :
    elem_orbital (combine_at f g x) x ∈ orbitals (combine_at f g x) := by
  use x
  simp only [not_exists, true_and]
  intro y singleton_orbital
  have := singleton_orbital_swap singleton_orbital
  have := fix_iff_singleton_orbital.mpr.mt not_fix
  contradiction

/--
  If `x` is in the orbital of `f`, then
  `combine_at f g x` is a bump.
-/
theorem mem_orbital_combine_isBump {f g : α ≃o α} {x : α}
    (x_mem_f : x ∈ orbital f) : isBump (combine_at f g x) := by
  simp only [isBump, Set.ncard_eq_one]
  use (elem_orbital (combine_at f g x) x)
  ext s
  constructor
  · exact mem_combine_orbitals_eq_elem_orbital
  · intro h
    simp only [Set.mem_singleton_iff] at h
    subst_vars
    apply elem_orbital_combine_mem_orbitals
    exact mem_f_orbital_not_fixed x_mem_f

/--
  If `x` is in the orbital of `f` and `g`,
  then
  `combine_at f g x` is a bump and
  the orbital of `combine_at f g x` is
  equal to the union of the orbitals of `f` and `g`.
-/
theorem intersect_orbital_combine_at {f g : α ≃o α} {x : α}
    (x_mem_f : x ∈ orbital f) (x_mem_g : x ∈ orbital g) :
    isBump (combine_at f g x) ∧
    orbital (combine_at f g x) = orbital f ∪ orbital g := by
  have isBump_combine : isBump (combine_at f g x) :=
    mem_orbital_combine_isBump x_mem_f
  rw [mem_orbital_iff] at x_mem_f x_mem_g
  rw [x_mem_f.1, x_mem_g.1]
  simp only [isBump_combine, orbital, ↓reduceDIte, true_and]
  have := mem_combine_orbitals_eq_elem_orbital
    (exists_orbital isBump_combine).choose_spec
  rw [this]
  exact combine_orbital_eq_union f g x

abbrev leftBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, x < y
abbrev rightBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, y < x

/--
  A bounded bump is a bump whose
  only orbital is bounded to the left or right.
-/
def isBoundedBump (f : α ≃o α) :=
  isBump f ∧ (leftBoundedOrbital f ∨ rightBoundedOrbital f)

/--
  If `f` and `g` are bounded on the right
  and `x` is in the orbital of `f` and `g`,
  then `combine_at f g x` is a bounded bump.
-/
theorem left_combine_bounded {f g : α ≃o α} {x : α}
    (f_left : leftBoundedOrbital f) (g_left : leftBoundedOrbital g)
    (x_mem_f : x ∈ orbital f) (x_mem_g : x ∈ orbital g) :
    isBoundedBump (combine_at f g x) := by
  have := intersect_orbital_combine_at x_mem_f x_mem_g
  simp only [leftBoundedOrbital, isBoundedBump, this,
    Set.mem_union, true_and] at f_left g_left ⊢
  obtain ⟨f_min, hfmin⟩ := f_left
  obtain ⟨g_min, hgmin⟩ := g_left
  left
  use (min f_min g_min)
  rintro y (y_mem_f | y_mem_g)
  · exact inf_lt_of_left_lt (hfmin y y_mem_f)
  · exact inf_lt_of_right_lt (hgmin y y_mem_g)

/--
  If `f` and `g` are bounded on the right
  and `x` is in the orbital of `f` and `g`,
  then `combine_at f g x` is a bounded bump.
-/
theorem right_combine_bounded {f g : α ≃o α} {x : α}
    (f_right : rightBoundedOrbital f) (g_right : rightBoundedOrbital g)
    (x_mem_f : x ∈ orbital f) (x_mem_g : x ∈ orbital g) :
    isBoundedBump (combine_at f g x) := by
  have := intersect_orbital_combine_at x_mem_f x_mem_g
  simp only [rightBoundedOrbital, isBoundedBump, this,
    Set.mem_union, true_and] at f_right g_right ⊢
  obtain ⟨f_max, hfmin⟩ := f_right
  obtain ⟨g_max, hgmin⟩ := g_right
  right
  use (max f_max g_max)
  rintro y (y_mem_f | y_mem_g)
  · exact lt_sup_of_lt_left (hfmin y y_mem_f)
  · exact lt_sup_of_lt_right (hgmin y y_mem_g)

/--
  Two points are related by `bubbleR` if they
  are both in the orbital of a bounded bump.
-/
abbrev bubbleR (x y : α) :=
  (∃f : α ≃o α, isBoundedBump f ∧ x ∈ orbital f ∧ y ∈ orbital f) ∨ x = y

/--
  The `bubbleR` relation is reflexive.
-/
theorem reflexive_bubbleR (x : α) : bubbleR x x := by
  simp [bubbleR]

/--
  The `bubbleR` relation is symmetric.
-/
theorem symmetric_bubbleR {x y : α} : bubbleR x y → bubbleR y x := by
  simp [bubbleR, And.comm, eq_comm]

/--
  Let `x < y` and `y < z`.
  If `x` is bubble related to `z`,
  then `x` is bubble related to `y`.
-/
theorem left_convex_bubbleR {x y z : α} (x_lt_y : x < y) (y_lt_z : y < z)
    (x_R_z : bubbleR x z) : bubbleR x y := by
  obtain ⟨f, isBoundedBump_f, ⟨x_mem_f_orbital, z_mem_f_orbital⟩⟩ | eq :=
    x_R_z
  · rw [bubbleR]
    left
    use f
    simp only [isBoundedBump_f, x_mem_f_orbital, true_and]
    have y_mem : y ∈ Set.Icc x z := ⟨x_lt_y.le, y_lt_z.le⟩
    have := isOrdConnected_orbital f
    exact Set.OrdConnected.out' x_mem_f_orbital z_mem_f_orbital y_mem
  · order

/--
  Let `x < y` and `y < z`.
  If `x` is bubble related to `z`,
  then `y` is bubble related to `z`.
-/
theorem right_convex_bubbleR {x y z : α} (x_lt_y : x < y) (y_lt_z : y < z)
    (x_R_z : bubbleR x z) : bubbleR y z := by
  obtain ⟨f, isBoundedBump_f, ⟨x_mem_f_orbital, z_mem_f_orbital⟩⟩ | eq :=
    x_R_z
  · rw [bubbleR]
    left
    use f
    simp only [isBoundedBump_f, z_mem_f_orbital, and_true, true_and]
    have y_mem : y ∈ Set.Icc x z := ⟨x_lt_y.le, y_lt_z.le⟩
    have := isOrdConnected_orbital f
    exact Set.OrdConnected.out' x_mem_f_orbital z_mem_f_orbital y_mem
  · order

/--
  Let `x` and `y` be in the orbital of `f`,
  and `y` and `z` be in the orbital of `g`.
  If the orbitals of `f` and `g` are left bounded,
  then `x` and `z` are bubble related.
-/
theorem intersect_leftBounded_bubbleR {f g : α ≃o α} {x y z : α}
    (x_mem_f : x ∈ orbital f) (y_mem_f : y ∈ orbital f)
    (y_mem_g : y ∈ orbital g) (z_mem_g : z ∈ orbital g)
    (f_leftBounded : leftBoundedOrbital f)
    (g_leftBounded : leftBoundedOrbital g) : bubbleR x z := by
  rw [bubbleR]
  left
  use combine_at f g y
  constructor
  · exact left_combine_bounded f_leftBounded g_leftBounded
      y_mem_f y_mem_g
  · have eq_union := (intersect_orbital_combine_at y_mem_f y_mem_g).2
    simp [eq_union]
    tauto

/--
  Let `x` and `y` be in the orbital of `f`,
  and `y` and `z` be in the orbital of `g`.
  If the orbitals of `f` and `g` are right bounded,
  then `x` and `z` are bubble related.
-/
theorem intersect_rightBounded_bubbleR {f g : α ≃o α} {x y z : α}
    (x_mem_f : x ∈ orbital f) (y_mem_f : y ∈ orbital f)
    (y_mem_g : y ∈ orbital g) (z_mem_g : z ∈ orbital g)
    (f_rightBounded : rightBoundedOrbital f)
    (g_rightBounded : rightBoundedOrbital g) : bubbleR x z := by
  rw [bubbleR]
  left
  use combine_at f g y
  constructor
  · exact right_combine_bounded f_rightBounded g_rightBounded
      y_mem_f y_mem_g
  · have eq_union := (intersect_orbital_combine_at y_mem_f y_mem_g).2
    simp [eq_union]
    tauto

/--
  Let `x` be bubble related to `y`
  and `y` be bubble related to `z`.
  Let `f` and `g` be bounded bumps such that
  `x` and `y` are in the orbital of `f`,
  and `y` and `z` are in the orbital of `g`.
  If `x < y` and `y < z`, then `x` and `z` are bubble related.
-/
theorem ordered_intersect_bounbded_bumps_bubbleR_transitive {f g : α ≃o α} {x y z : α}
    (hxy' : bubbleR x y) (hyz' : bubbleR y z) (f_boundedBump : isBoundedBump f)
    (g_boundedBump : isBoundedBump g) (x_mem_f : x ∈ orbital f)
    (y_mem_f : y ∈ orbital f) (y_mem_g : y ∈ orbital g) (z_mem_g : z ∈ orbital g)
    (x_lt_y : x < y) (y_lt_z : y < z) : bubbleR x z := by
  simp only [isBoundedBump] at f_boundedBump g_boundedBump
  obtain ⟨f_bump, f_leftbounded | f_rightbounded⟩ := f_boundedBump
  <;> obtain ⟨g_bump, g_leftbounded | g_rightbounded⟩ := g_boundedBump
  · exact intersect_leftBounded_bubbleR x_mem_f y_mem_f y_mem_g z_mem_g
      f_leftbounded g_leftbounded
  · sorry
  · sorry
  · exact intersect_rightBounded_bubbleR x_mem_f y_mem_f y_mem_g z_mem_g
      f_rightbounded g_rightbounded

/--
  Let `x` be bubble related to `y`
  and `y` be bubble related to `z`.
  Let `f` and `g` be bounded bumps such that
  `x` and `y` are in the orbital of `f`,
  and `y` and `z` are in the orbital of `g`.
  Then `x` and `z` are bubble related.
-/
theorem intersect_bounded_bumps_bubbleR_transitive {f g : α ≃o α} {x y z : α}
    (hxy' : bubbleR x y) (hyz' : bubbleR y z) (f_boundedbump : isBoundedBump f)
    (g_boundedbump : isBoundedBump g) (x_in_f_orbital : x ∈ orbital f)
    (y_in_f_orbital : y ∈ orbital f) (y_in_g_orbital : y ∈ orbital g)
    (z_in_g_orbital : z ∈ orbital g) : bubbleR x z := by
  obtain x_lt_y | x_eq_y | y_lt_x := lt_trichotomy x y
  <;> obtain y_lt_z | y_eq_z | z_lt_y := lt_trichotomy y z
  <;> obtain x_lt_z | x_eq_z | z_lt_x := lt_trichotomy x z
  <;> try grind
  all_goals try (apply left_convex_bubbleR <;> first | order | trivial)
  · exact ordered_intersect_bounbded_bumps_bubbleR_transitive hxy' hyz'
      f_boundedbump g_boundedbump x_in_f_orbital y_in_f_orbital
      y_in_g_orbital z_in_g_orbital x_lt_y y_lt_z
  · apply symmetric_bubbleR
    apply left_convex_bubbleR (z := y)
    · order
    · order
    · exact symmetric_bubbleR hyz'
  · apply right_convex_bubbleR (x := y)
    · order
    · order
    · exact hyz'
  · apply symmetric_bubbleR
    apply right_convex_bubbleR (x := y)
    · order
    · order
    · exact symmetric_bubbleR hxy'
  · apply symmetric_bubbleR
    apply symmetric_bubbleR at hxy'
    apply symmetric_bubbleR at hyz'
    exact ordered_intersect_bounbded_bumps_bubbleR_transitive hyz' hxy'
      g_boundedbump f_boundedbump z_in_g_orbital y_in_g_orbital
      y_in_f_orbital x_in_f_orbital z_lt_y y_lt_x
/--
  The `bubbleR` relation is transitive.
-/
theorem transitive_bubbleR {x y z : α} :
    bubbleR x y → bubbleR y z → bubbleR x z := by
  intro hxy hyz
  have hxy' := hxy
  have hyz' := hyz
  obtain ⟨f, f_boundedbump, x_in_f_orbital, y_in_f_orbital⟩ | rfl := hxy
  <;> obtain ⟨g, g_boundedbump, y_in_g_orbital, z_in_g_orbital⟩ | rfl := hyz
  · exact intersect_bounded_bumps_bubbleR_transitive hxy' hyz' f_boundedbump
      g_boundedbump x_in_f_orbital y_in_f_orbital y_in_g_orbital z_in_g_orbital
  · exact hxy'
  · exact hyz'
  · exact hxy'
