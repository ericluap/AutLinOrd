import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.Order

section OrdClosure
variable {α : Type*} [Preorder α]

/--
  The `ordClosure` of a set `s` is the
  intersection of its upper and lower closure.
  This is the smallest `OrdConnected` set containing `s`.
-/
def Set.ordClosure (s : Set α) :=
    (upperClosure s : Set α) ∩ (lowerClosure s : Set α)

/--
  `z` is an element of the `ordClosure` of `s`
  if and only if it is bounded above and below
  by elements of `s`.
-/
theorem mem_ordClosure {s : Set α} {z : α} :
    z ∈ s.ordClosure ↔ ∃x ∈ s, ∃y ∈ s, z ∈ Set.Icc x y := by
  simp only [Set.ordClosure, Set.mem_inter_iff, SetLike.mem_coe,
    mem_upperClosure, mem_lowerClosure, Set.mem_Icc]
  tauto

/--
  A set `s` is a subset of its `ordClosure`.
-/
theorem subset_ordClosure (s : Set α) : s ⊆ s.ordClosure := by
  intro x hx
  simp only [mem_ordClosure, Set.mem_Icc]
  have s_subset_upper : s ⊆ upperClosure s := subset_upperClosure
  have s_subset_lower : s ⊆ lowerClosure s := subset_lowerClosure
  tauto

/--
  The `ordClosure` of a set is `OrdConnected`.
-/
theorem ordConnected_ordClosure (s : Set α) :
    s.ordClosure.OrdConnected :=
  Set.OrdConnected.inter
    (IsUpperSet.ordConnected (upperClosure s).upper)
    (IsLowerSet.ordConnected (lowerClosure s).lower)

/--
  If `s` is a subset of `t` and `t` is `OrdConnected`,
  then `s.ordClosure` is a subset of `t`.
-/
theorem ordClosure_subset_ordConnected {s t : Set α}
    (s_sub_t : s ⊆ t) (ht : t.OrdConnected) : s.ordClosure ⊆ t := by
  intro z hz
  obtain ⟨x, hx, y, hy , hxy⟩ := mem_ordClosure.mp hz
  exact ht.out' (s_sub_t hx) (s_sub_t hy) hxy

/--
  The intersection of all `OrdConnected` sets
  containing a set `s` is equal to `s.ordClosure`.
-/
theorem inter_eq_closure (s : Set α) :
    ⋂₀ {S : Set α | s ⊆ S ∧ S.OrdConnected} = s.ordClosure := by
  apply Set.eq_of_subset_of_subset
  · apply Set.sInter_subset_of_mem
    simp only [Set.mem_setOf_eq]
    exact ⟨subset_ordClosure s, ordConnected_ordClosure s⟩
  · simp only [Set.subset_sInter_iff, Set.mem_setOf_eq, and_imp]
    intro t s_subset_t t_ordConnected
    exact ordClosure_subset_ordConnected s_subset_t t_ordConnected

/--
  If every element of a set `t` is upper and lower bounded
  by elements of a set `s`, then `t.ordClosure` is a subset
  of `s.ordClosure`.
-/
theorem ordClosure_subset_ordClosure {s t : Set α}
    (t_between_s : ∀x ∈ t, (∃l ∈ s, l ≤ x) ∧ (∃u ∈ s, x ≤ u)) :
    t.ordClosure ⊆ s.ordClosure := by
  intro x hx
  simp only [mem_ordClosure, Set.mem_Icc] at hx ⊢
  obtain ⟨lx, hlx, ux, hux, ⟨lx_le_x, x_le_ux⟩⟩ := hx
  rcases t_between_s lx hlx with ⟨⟨l, ⟨l_mem, l_le⟩⟩, _⟩
  rcases t_between_s ux hux with ⟨_, ⟨u, ⟨u_mem, le_u⟩⟩⟩
  use l, l_mem, u, u_mem
  constructor
  <;> order

/--
  If every element of `t` is between elements of `s`
  and vice versa, then the `ordClosure` of `s` and `t`
  are equal.
-/
theorem ordClosure_eq_ordClosure {s t : Set α}
    (t_between_s : ∀x ∈ t, (∃l ∈ s, l ≤ x) ∧ (∃u ∈ s, x ≤ u))
    (s_between_t : ∀x ∈ s, (∃l ∈ t, l ≤ x) ∧ (∃u ∈ t, x ≤ u)) :
    s.ordClosure = t.ordClosure := by
  apply Set.eq_of_subset_of_subset
  · exact ordClosure_subset_ordClosure s_between_t
  · exact ordClosure_subset_ordClosure t_between_s

/--
  If `s` is `OrdConnected`, then
  `s.ordClosure = s`.
-/
theorem ordClosure_of_ordConnected {s : Set α} (ord : s.OrdConnected) :
    s.ordClosure = s := by
  have s_sub_closure := subset_ordClosure s
  have closure_sub_s : s.ordClosure ⊆ s :=
    ordClosure_subset_ordConnected (by simp) ord
  exact Set.Subset.antisymm closure_sub_s s_sub_closure

end OrdClosure
