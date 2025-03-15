import AutLinOrd.NonDecrAt
import AutLinOrd.OrbitalAt

variable {α : Type*} [LinearOrder α]

/--
  Given automorphisms `f` and `g` and an element `x`,
  `combine_at f g x` is an automorphism whose orbital at
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

/--
  For any `y` in the orbital of `x` under `f`,
  `f y ≤ (combine_at f g x) y`.
-/
theorem f_le_combine_at {f : α ≃o α} (g : α ≃o α) {x y : α}
    (y_mem : y ∈ elem_orbital f x) : f y ≤ (combine_at f g x) y := by
  rw [non_decr_eq_elem_orbital] at y_mem
  by_cases h2 : (non_decr_at f x) y ∈ elem_orbital (non_decr_at g x) x
  <;> simp [combine_at, orbital_at, y_mem, h2]
  · have : f y ≤ (non_decr_at f x) y := mem_elem_orbital_image_non_decr y_mem
    have : (non_decr_at f x) y ≤ (non_decr_at g x) ((non_decr_at f x) y) :=
      mem_elem_orbital_non_decr h2
    order
  · exact mem_elem_orbital_image_non_decr y_mem

theorem in_or_above_orbital {f g : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) (z : ℤ) :
    (((combine_at f g x ^ z) y) ∈ elem_orbital f x) ∨
    (∀t ∈ elem_orbital f x, t < (combine_at f g x ^ z) y) := by
  by_cases h : (((combine_at f g x ^ z) y) ∈ elem_orbital f x)
  · left
    trivial
  · right
    intro t ht
    by_contra!
    absurd h
    simp only [mem_elem_orbital_iff]
    constructor
    · have : y ≤ (combine_at f g x) y := not_decr_combine_at f g x y
      rw [mem_elem_orbital_iff] at y_mem
      obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
      use l
      have : (combine_at f g x) y ≤  (combine_at f g x ^ z) y := by exact?



theorem pow_f_le_combine_at {f g : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) (z : ℤ) :
    (f^z) y ≤ ((combine_at f g x)^z) y := by
  induction z with
  | hz => simp
  | hp i ih =>
    norm_cast at ih ⊢
    simp [add_comm i, ←add_pows_n]
    have : f ((f^i) y) ≤ f ((combine_at f g x ^ i) y) :=
      OrderIso.GCongr.orderIso_apply_le_apply f ih
    by_cases h : (combine_at f g x ^ i) y ∈ elem_orbital f x
    · have := f_le_combine_at g h
      order
    · conv =>
        enter [2, 1]
        simp [combine_at]
      simp
      rw [non_decr_eq_elem_orbital] at h
      have := orbital_at_not_mem_orbital h
      simp [this]
  | hn i _ =>

theorem f_in_combine_maps (f g : α ≃o α) (x y : α)
    (y_mem : y ∈ elem_orbital f x) : y ∈ elem_orbital (combine_at f g x) x := by
  rw [non_decr_eq_elem_orbital, ←orbital_at_eq_orbital,
    mem_elem_orbital_strong_iff] at y_mem
  obtain fix | incr | decr := y_mem
  · simp only [mem_elem_orbital_iff, combine_at, fix]
