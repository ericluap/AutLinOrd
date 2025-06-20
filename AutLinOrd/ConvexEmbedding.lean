import Mathlib.Order.InitialSeg
import Mathlib.Order.Interval.Set.OrdConnected

seal OrderDual

/-!
  This file defines a convex embedding between two linear orders
  and introduces the notation `A ≤c B` for it.
-/

/--
  A `ConvexEmbedding` is an `OrderEmbedding` whose image is `OrdConnected`.
-/
structure ConvexEmbedding (α β : Type*) [Preorder α] [Preorder β] extends α ↪o β
    where
  imageOrdConnected : (Set.range toFun).OrdConnected

@[inherit_doc]
infixl:24 " ≤c " => ConvexEmbedding

def OrderEmbedding.dual' [Preorder α] [Preorder β] (f : α ↪o β) :
    (αᵒᵈ ↪o βᵒᵈ) where
  toFun := OrderDual.toDual ∘ f ∘ OrderDual.ofDual
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp

def OrderEmbedding.undual' [Preorder α] [Preorder β] (f : αᵒᵈ ↪o βᵒᵈ) :
    (α ↪o β) where
  toFun := OrderDual.ofDual ∘ f ∘ OrderDual.toDual
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp

namespace ConvexEmbedding

variable [Preorder α] [Preorder β] [Preorder γ] (f : α ≤c β)

/--
  Every `ConvexEmbedding` is an `OrderEmbedding`.
-/
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

/--
  If `z` is in between `f x` and `f y`, then `z` is in the range of `f`.
-/
theorem mem_icc_mem_range
    (x_le_y : x ≤ y) (z_mem_range : z ∈ Set.Icc (f x) (f y)) :
    z ∈ Set.range f := by
  have := f.imageOrdConnected
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Set.ordConnected_iff,
    Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, OrderEmbedding.le_iff_le] at this
  exact this x y x_le_y z_mem_range

def dual (f : α ≤c β) : αᵒᵈ ≤c βᵒᵈ :=
  ⟨f.toOrdEmbedding.dual', by
    simp [OrderEmbedding.dual', Set.ordConnected_iff]
    intro x y y_le_x z z_mem_icc
    simp only [Set.mem_range, Function.comp_apply, OrderDual.exists, OrderDual.ofDual_toDual]
    simp only [Set.mem_preimage] at z_mem_icc
    have := mem_icc_mem_range f y_le_x z_mem_icc
    simp only [Set.mem_range] at this
    obtain ⟨y, hy⟩ := this
    use y
    exact (Equiv.apply_eq_iff_eq_symm_apply OrderDual.toDual).mpr hy
    ⟩

def undual (f : αᵒᵈ ≤c βᵒᵈ) : α ≤c β :=
  ⟨f.toOrdEmbedding.undual', by
    simp [OrderEmbedding.undual', Set.ordConnected_iff]
    intro x y y_le_x z z_mem_icc
    simp only [Set.mem_range, Function.comp_apply, OrderDual.exists, OrderDual.ofDual_toDual]
    simp only [Set.mem_preimage] at z_mem_icc
    have := mem_icc_mem_range f y_le_x z_mem_icc
    simp only [Set.mem_range] at this
    obtain ⟨y, hy⟩ := this
    use OrderDual.ofDual y
    exact (Equiv.apply_eq_iff_eq_symm_apply OrderDual.ofDual).mpr hy
    ⟩

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
@[coe]
def InitialSeg.toConvexEmbedding [PartialOrder α] [PartialOrder β]
    (initial : α ≤i β) : α ≤c β where
  toFun := initial
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  imageOrdConnected := image_initialSeg_ordConnected initial

instance [PartialOrder α] [PartialOrder β] : Coe (α ≤i β) (α ≤c β) where
  coe f := f.toConvexEmbedding

def InitialSeg.toUndualConvexEmbedding [PartialOrder α] [PartialOrder β]
    (final : αᵒᵈ ≤i βᵒᵈ) : α ≤c β := final.toConvexEmbedding.undual

def OrderIso.toConvexEmbedding [PartialOrder α] [PartialOrder β] (f : α ≃o β) :
    α ≤c β := ⟨f, by simp [Set.ordConnected_univ]⟩
/--
  `A ∩ B` convexly embeds in `A`.
-/
def intersect_convex_first [LinearOrder α] (A B : Set α)
    (B_interval : B.OrdConnected) : (A ∩ B : Set α) ≤c A where
  toFun x := ⟨x.val, x.prop.1⟩
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  imageOrdConnected := by
    simp only [Set.ordConnected_iff, Set.inter_subset_left, Set.range_inclusion,
      Set.mem_inter_iff, Subtype.coe_prop, true_and, Set.mem_setOf_eq,
      Subtype.forall, Subtype.mk_le_mk] at B_interval ⊢
    intro a a_mem_A a_mem_B b b_mem_A b_mem_B a_le_b x x_mem_icc
    simp only [Set.mem_setOf_eq]
    exact B_interval a a_mem_B b b_mem_B a_le_b x_mem_icc

/--
  `A ∩ B` convexly embeds in `B`.
-/
def intersect_convex_second [LinearOrder α] (A B : Set α)
    (A_interval : A.OrdConnected) : (A ∩ B : Set α) ≤c B where
  toFun x := ⟨x.val, x.prop.2⟩
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  imageOrdConnected := by
    simp [Set.ordConnected_iff] at A_interval ⊢
    intro a a_mem_B a_mem_A b b_mem_B b_mem_A a_le_b x x_mem_icc
    simp only [Set.mem_setOf_eq]
    exact A_interval a a_mem_A b b_mem_A a_le_b x_mem_icc
