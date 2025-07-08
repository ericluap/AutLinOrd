import Mathlib
import AutLinOrd.Orbital.Orbital

/-!
  This file defines the bubble relation and proves it is a
  convex equivalence relation.
-/

variable {α : Type*} [LinearOrder α]

/--
  The orbital of `f` is a left bounded orbital
  if there exists an element smaller than
  everything in the orbital of `f`.
-/
abbrev leftBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, x < y
/--
  The orbital of `f` is a right bounded orbital
  if there exists an element smaller than
  everything in the orbital of `f`.
-/
abbrev rightBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, y < x

/--
  A bounded bump is a bump whose
  only orbital is either bounded to the left or to the right.
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
  are both in the orbital of a bounded bump
  (or are equal).
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
  Let `x ≤ y` and `y ≤ z`.
  If `x` is bubble related to `z`,
  then `x` is bubble related to `y`.
-/
theorem left_convex_bubbleR_le {x y z : α} (x_le_y : x ≤ y) (y_le_z : y ≤ z)
    (x_R_z : bubbleR x z) : bubbleR x y := by
  obtain y_lt_z | y_eq_z := y_le_z.lt_or_eq
  <;> obtain x_lt_y | x_eq_y := x_le_y.lt_or_eq
  · exact left_convex_bubbleR x_lt_y y_lt_z x_R_z
  · exact Or.inr x_eq_y
  · simp [y_eq_z, x_R_z]
  · exact Or.inr x_eq_y

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
  Let `x ≤ y` and `y ≤ z`.
  If `x` is bubble related to `z`,
  then `y` is bubble related to `z`.
-/
theorem right_convex_bubbleR_le {x y z : α} (x_le_y : x ≤ y) (y_le_z : y ≤ z)
    (x_R_z : bubbleR x z) : bubbleR y z := by
  obtain y_lt_z | y_eq_z := y_le_z.lt_or_eq
  <;> obtain x_lt_y | x_eq_y := x_le_y.lt_or_eq
  · exact right_convex_bubbleR x_lt_y y_lt_z x_R_z
  · simp [←x_eq_y, x_R_z]
  · exact Or.inr y_eq_z
  · exact Or.inr y_eq_z

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
    simp only [eq_union, Set.mem_union]
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
    simp only [eq_union, Set.mem_union]
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
  · by_cases g_leftbounded : leftBoundedOrbital g
    · exact intersect_leftBounded_bubbleR x_mem_f y_mem_f y_mem_g z_mem_g
        f_leftbounded g_leftbounded
    · simp only [leftBoundedOrbital, not_exists, not_forall, not_lt] at g_leftbounded
      obtain ⟨t, ht, t_le_z⟩ := g_leftbounded x
      have : bubbleR t z := by
        left
        use g
        simp [isBoundedBump, g_bump, g_rightbounded, ht, z_mem_g]
      exact right_convex_bubbleR_le t_le_z (show x ≤ z by order) this
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
