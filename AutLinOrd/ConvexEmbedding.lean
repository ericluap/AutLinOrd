import Mathlib.Order.InitialSeg
import Mathlib.Order.Interval.Set.OrdConnected

/--
  A `ConvexEmbedding` is an `OrderEmbedding` whose image is `OrdConnected`.
  In other words, it is a convex order embedding.
-/
structure ConvexEmbedding (α β : Type*) [Preorder α] [Preorder β] extends α ↪o β
    where
  imageOrdConnected : (Set.range toFun).OrdConnected

@[inherit_doc]
infixl:24 " ≤c " => ConvexEmbedding

namespace ConvexEmbedding

variable [Preorder α] [Preorder β] [Preorder γ] (f : α ≤c β)

@[coe]
def toOrdEmbedding (f : ConvexEmbedding α β) : α ↪o β where
  toFun := f.toFun
  inj' := f.inj'
  map_rel_iff' := f.map_rel_iff'

instance : Coe (ConvexEmbedding α β) (α ↪o β) where
  coe f := f.toOrdEmbedding

instance : FunLike (ConvexEmbedding α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      DFunLike.coe_fn_eq] at h
    cases f; cases g; congr

@[simp]
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b :=
  f.map_rel_iff

@[simp]
theorem lt_iff_lt {a b} : f a < f b ↔ a < b := by
  constructor
  · intro h
    exact (OrderEmbedding.lt_iff_lt f.toRelEmbedding).mp h
  · intro h
    simp [lt_iff_le_not_le]
    exact lt_iff_le_not_le.mp h

theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff

/--
  The image of an `OrdConnected` set under a `ConvexEmbedding`
  is `OrdConnected`.
-/
theorem interval_convexEmbedding_interval {s : Set α}
    (interval_s : s.OrdConnected) : (f '' s).OrdConnected := by
  simp [Set.ordConnected_iff, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro x hx z hz x_le_z y hy
  have y_mem_range : y ∈ Set.range f := by
    have imageOrdConnected := f.imageOrdConnected
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      Set.ordConnected_iff, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, OrderEmbedding.le_iff_le] at imageOrdConnected
    exact imageOrdConnected x z x_le_z hy
  simp only [Set.mem_range] at y_mem_range
  obtain ⟨t, ht⟩ := y_mem_range
  use t
  constructor
  · simp only [← ht, Set.mem_Icc, le_iff_le] at hy
    obtain ⟨x_le_t, t_lt_z⟩ := hy
    simp only [Set.ordConnected_iff] at interval_s
    exact interval_s x hx z hz x_le_z ⟨x_le_t, t_lt_z⟩
  · exact ht

def comp (g : β ≤c γ) (f : α ≤c β) : α ≤c γ where
  toFun := g ∘ f
  inj' := Function.Injective.comp g.inj' f.inj'
  map_rel_iff' := Iff.trans g.map_rel_iff' f.map_rel_iff'
  imageOrdConnected := by
    rw [Set.range_comp]
    exact interval_convexEmbedding_interval g f.imageOrdConnected

end ConvexEmbedding

/--
  The image of an `InitialSeg` is `OrdConnected`.
-/
theorem image_initialSeg_ordConnected [PartialOrder α] [PartialOrder β]
    (f : α ≤i β) : (Set.range f).OrdConnected := by
  have := f.mem_range_of_rel'
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
  InitialSeg.coe_toOrderEmbedding, Set.ordConnected_iff, Set.mem_range,
  forall_exists_index, forall_apply_eq_imp_iff, InitialSeg.le_iff_le]
  intro x z x_le_z y y_mem
  obtain y_lt_initz | y_eq_initz := y_mem.2.lt_or_eq
  · exact this z y y_lt_initz
  · simp [y_eq_initz]

/--
  Every `InitialSeg` is a `ConvexEmbedding`.
-/
def initial_emb_convex_emb [PartialOrder α] [PartialOrder β]
    (initial : α ≤i β) : α ≤c β where
  toFun := initial
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  imageOrdConnected := image_initialSeg_ordConnected initial
