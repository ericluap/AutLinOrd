import Mathlib
import AutLinOrd.OrdClosure
import AutLinOrd.MulAction

variable {α : Type*} [LinearOrder α]

/--
  The orbit of `x` under an automorphism `f`.
-/
abbrev elem_orbit (f : α ≃o α) (x : α) :=
  MulAction.orbit (Subgroup.zpowers f) x

/--
  The orbital of `x` under an automorphism `f`.
-/
abbrev elem_orbital (f : α ≃o α) (x : α) := (elem_orbit f x).ordClosure

/--
  The set of all non-singleton orbitals of `f`.
-/
abbrev orbitals (f : α ≃o α) :=
  {z : Set α | ∃x : α, elem_orbital f x = z ∧ ¬∃z : α, elem_orbital f x = {z}}

/--
  An automorphism `f` is a bump if it only has
  a single orbital (that is not a singleton).
-/
abbrev isBump (f : α ≃o α) := (orbitals f).ncard = 1

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
  A bounded bump is a bump whose
  only orbital is bounded above or below.
-/
def isBoundedBump (f : α ≃o α) :=
  isBump f ∧
  (∃x : α,
    (∀y ∈ orbital f, x < y) ∨ (∀y ∈ orbital f, y < x))

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
  simp only [bubbleR]
  conv_lhs =>
    lhs; rhs
    intro f
    rhs
    rw [And.comm]
  conv_lhs =>
    rhs;
    rw [eq_comm]
  exact fun a ↦ a

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
