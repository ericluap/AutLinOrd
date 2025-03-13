import Mathlib
import AutLinOrd.NonDecrAt
import AutLinOrd.OrbitalAt

variable {α : Type*} [LinearOrder α]

/--
  Given automorphisms `f` and `g` and an element `x`,
  `combine_at f g x` is an automorphism who orbital at
  `x` is the union of that of `f` and `g`.
-/
noncomputable def combine_at (f g : α ≃o α) (x : α) : α ≃o α :=
  (orbital_at (non_decr_at f x) x).trans (orbital_at (non_decr_at g x) x)

/--
  For any `y`, we have that `y ≤ (combine_at f g x) y`.
-/
theorem not_decr_combine_at (f g : α ≃o α) (x y : α) :
    y ≤ (combine_at f g x) y := by
  by_cases h : y ∈ elem_orbital (non_decr_at f x) x
  · by_cases h2 : (non_decr_at f x) y ∈ elem_orbital (non_decr_at g x) x
    <;> simp [combine_at, orbital_at, h, h2]
    · have : y ≤ non_decr_at f x y := mem_elem_orbital_non_decr h
      have : (non_decr_at f x) y ≤ non_decr_at g x ((non_decr_at f x) y) :=
        mem_elem_orbital_non_decr h2
      order
    · exact mem_elem_orbital_non_decr h
  · by_cases h2 : y ∈ elem_orbital (non_decr_at g x) x
    <;> simp [combine_at, orbital_at, h, h2]
    · exact mem_elem_orbital_non_decr h2

theorem f_le_combine_at {f g : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) : f y ≤ (combine_at f g x) y := by
  rw [non_decr_eq_elem_orbital] at y_mem
  by_cases h2 : (non_decr_at f x) y ∈ elem_orbital (non_decr_at g x) x
  <;> simp [combine_at, orbital_at, y_mem, h2]
  · have : f y ≤ (non_decr_at f x) y := mem_elem_orbital_image_non_decr y_mem
    have : (non_decr_at f x) y ≤ (non_decr_at g x) ((non_decr_at f x) y) :=
      mem_elem_orbital_non_decr h2
    order
  · exact mem_elem_orbital_image_non_decr y_mem

theorem first_in_combine_maps (f g : α ≃o α) (x y : α)
    (y_mem : y ∈ elem_orbital f x) : y ∈ elem_orbital (combine_at f g x) x := by
  rw [←orbital_at_eq_orbital, non_decr_eq_elem_orbital,
    mem_elem_orbital_strong_iff] at y_mem
  obtain fix | incr | decr := y_mem
  simp only [mem_elem_orbital_iff, combine_at]
  all_goals sorry-/

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
  The orbital of a bump `f`.
  (If `f` is not a bump, then it returns junk)
-/
def orbital (f : α ≃o α) :=
  if h : ∃x, x ∈ orbitals f then
    h.choose
  else
    ∅

/--
  `x` is an element of the orbital of `f`
  if and only if the orbital of `f` is equal to
  the orbital of `x` under `f`.
-/
theorem mem_orbital_iff {f : α ≃o α} {x : α} :
    x ∈ orbital f ↔ orbital f = elem_orbital f x := by
  constructor
  · intro x_mem
    by_cases h : ∃x, x ∈ orbitals f
    · simp only [orbital, h, ↓reduceDIte] at x_mem ⊢
      have := h.choose_spec
      simp only [orbitals, not_exists, Set.mem_setOf_eq] at this x_mem ⊢
      obtain ⟨z, eq_elem_orbital, not_singleton⟩ := this
      simp [←eq_elem_orbital] at x_mem ⊢
      exact (mem_elem_orbital_eq x_mem).symm
    · simp [orbital, h] at x_mem
  · intro eq_orbital
    rw [eq_orbital]
    exact mem_elem_orbital_reflexive f x

theorem pow_mem_orbital {f : α ≃o α} {x : α} (x_mem : x ∈ orbital f) (z : ℤ) :
    (f ^ z) x ∈ orbital f := by
  rw [mem_orbital_iff] at x_mem
  rw [x_mem]
  exact pow_mem_elem_orbital z (mem_elem_orbital_reflexive f x)

theorem pow_mem_orbital_one {f : α ≃o α} {x : α} (x_mem : x ∈ orbital f) :
    f x ∈ orbital f := pow_mem_orbital x_mem 1

abbrev leftBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, x < y
abbrev rightBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, y < x

/--
  A bounded bump is a bump whose
  only orbital is bounded to the left or right.
-/
def isBoundedBump (f : α ≃o α) :=
  isBump f ∧ (leftBoundedOrbital f ∨ rightBoundedOrbital f)

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

def isIncreasingOnOrbital (f : α ≃o α) := ∀x ∈ orbital f, x < f x
def isDecreasingOnOrbitl (f : α ≃o α) := ∀x ∈ orbital f, f x < x

def isNotDecreasingOnOrbital (f : α ≃o α) := ∀x ∈ orbital f, x ≤ f x
def isNotIncreasingOnOrbital (f : α ≃o α) := ∀x ∈ orbital f, f x ≤ x

theorem combine_bumps {f g : α ≃o α}
    (hf : isBump f) (hg : isBump g) (inter : ∃x, x ∈ orbital f ∩ orbital g) :
    ∃h : α ≃o α, isBump h ∧ orbital h = orbital f ∪ orbital g := by
  sorry

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
  · sorry
  · exact hxy'
  · exact hyz'
  · exact hxy'
