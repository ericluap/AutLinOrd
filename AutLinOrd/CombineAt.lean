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
  all_goals sorry
