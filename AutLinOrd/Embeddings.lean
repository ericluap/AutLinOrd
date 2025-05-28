import Mathlib.Order.InitialSeg
import Mathlib.Tactic.ApplyFun

variable [LinearOrder α] [LinearOrder β]

/--
  If `f : α ↪o β`, then `α ≃o Set.range f`
-/
noncomputable def ordEmbedding_iso_range [Nonempty α] (f : α ↪o β) :
    α ≃o Set.range f where
  toFun x := ⟨f x, by simp⟩
  invFun x := (Function.invFun f) x
  left_inv := by simp [Function.LeftInverse, Function.invFun]
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Function.invFun,
      Subtype.forall, Set.image_univ, Set.mem_range, Subtype.mk.injEq,
      forall_exists_index]
    intro b x h
    have : ∃x, f x = b := by use x
    simp only [this, ↓reduceDIte]
    generalize_proofs
    simp [this.choose_spec]
  map_rel_iff' := by simp

/-- An order embedding between dual order is also an order embedding orders. -/
def OrderEmbedding.undual [LinearOrder α] [LinearOrder β]
  (f : αᵒᵈ ↪o βᵒᵈ) : α ↪o β := ⟨f.toEmbedding, f.map_rel_iff⟩

/--
  If `α` is initial in `β` and `β ≃o γ`, then
  `α` is initial in `γ`.
-/
def iso_initial [LinearOrder γ] (initial : α ≤i β) (iso : β ≃o γ) :
    α ≤i γ where
  toFun x := (iso ∘ initial) x
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Subtype.range_coe_subtype, Set.mem_range, Function.comp_apply,
      Set.mem_setOf_eq, Subtype.forall, forall_exists_index,
      forall_apply_eq_imp_iff]
    intro a b b_lt_map
    have symm_b_lt : iso.symm b < initial a := by
      apply_fun iso
      simp [b_lt_map]
    have b_symm_mem := initial.mem_range_of_rel' a (iso.symm b) symm_b_lt
    simp only [InitialSeg.coe_coe_fn, Set.mem_range] at b_symm_mem
    obtain ⟨c, hc⟩ := b_symm_mem
    use c
    simp [hc]

/--
  If `α` is initial in `β` and `β ≃o γ`, then the image of `α`
  under `γ` is initial in `γ`.
-/
def iso_image_initial [LinearOrder γ] (initial : α ≤i β) (iso : β ≃o γ) :
    Set.range (iso ∘ initial) ≤i γ where
  toFun x := x.val
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Subtype.range_coe_subtype, Set.mem_range, Function.comp_apply,
      Set.mem_setOf_eq, Subtype.forall, forall_exists_index,
      forall_apply_eq_imp_iff]
    intro a b b_lt_map
    have symm_b_lt : iso.symm b < initial a := by
      apply_fun iso
      simp [b_lt_map]
    have b_symm_mem := initial.mem_range_of_rel' a (iso.symm b) symm_b_lt
    simp only [InitialSeg.coe_coe_fn, Set.mem_range] at b_symm_mem
    obtain ⟨c, hc⟩ := b_symm_mem
    use c
    simp [hc]
