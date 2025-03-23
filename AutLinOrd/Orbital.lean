import AutLinOrd.CombineAt
import Mathlib.Data.Set.Card

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
