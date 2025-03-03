import Mathlib.Order.UpperLower.Basic

section OrdClosure
variable {α : Type*} [Preorder α]

def Set.ordClosure (s : Set α) :=
    (upperClosure s : Set α) ∩ (lowerClosure s : Set α)

theorem mem_ordClosure {s : Set α} {z : α} :
    z ∈ s.ordClosure ↔ ∃x ∈ s, ∃y ∈ s, z ∈ Set.Icc x y := by
  simp only [Set.ordClosure, Set.mem_inter_iff, SetLike.mem_coe,
    mem_upperClosure, mem_lowerClosure, Set.mem_Icc]
  tauto

theorem subset_ordClosure (s : Set α) : s ⊆ s.ordClosure := by
  intro x hx
  simp only [mem_ordClosure, Set.mem_Icc]
  have s_subset_upper : s ⊆ upperClosure s := subset_upperClosure
  have s_subset_lower : s ⊆ lowerClosure s := subset_lowerClosure
  tauto

theorem ordConnected_ordClosure (s : Set α) :
    s.ordClosure.OrdConnected :=
  Set.OrdConnected.inter
    (IsUpperSet.ordConnected (upperClosure s).upper)
    (IsLowerSet.ordConnected (lowerClosure s).lower)

theorem ordClosure_subset_ordConnected (s : Set α) {t : Set α}
    (s_sub_t : s ⊆ t) (ht : t.OrdConnected) : s.ordClosure ⊆ t := by
  intro z hz
  obtain ⟨x, hx, y, hy , hxy⟩ := mem_ordClosure.mp hz
  exact ht.out' (s_sub_t hx) (s_sub_t hy) hxy

theorem inter_eq_closure (s : Set α) :
    ⋂₀ {S : Set α | s ⊆ S ∧ S.OrdConnected} = s.ordClosure := by
  apply Set.eq_of_subset_of_subset
  · apply Set.sInter_subset_of_mem
    simp only [Set.mem_setOf_eq]
    exact ⟨subset_ordClosure s, ordConnected_ordClosure s⟩
  · simp only [Set.subset_sInter_iff, Set.mem_setOf_eq, and_imp]
    intro t s_subset_t t_ordConnected
    exact ordClosure_subset_ordConnected s s_subset_t t_ordConnected

end OrdClosure
