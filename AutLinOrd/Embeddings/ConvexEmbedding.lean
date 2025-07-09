import Mathlib.Algebra.Group.Defs
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

def refl : α ≤c α where
  toFun := id
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  imageOrdConnected := by simp [Set.ordConnected_univ]

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

instance : EmbeddingLike (α ≤c β) α β where
  injective' f := f.inj'

instance : OrderHomClass (α ≤c β) α β where
  map_rel f := f.map_rel_iff'.mpr

@[simp]
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b := f.map_rel_iff

@[simp]
theorem lt_iff_lt {a b} : f a < f b ↔ a < b := by
  have {x} : f x = f.toOrdEmbedding x := by rfl
  simp [this]

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

/--
  If `z` is in between `f x` and `f y`, then `z` is in the range of `f`.
-/
theorem le_and_le_mem_range
    (fx_le_z : f x ≤ z) (z_le_fy : z ≤ f y) : z ∈ Set.range f := by
  have z_mem_range : z ∈ Set.Icc (f x) (f y) := by simp [fx_le_z, z_le_fy]
  have x_le_y : x ≤ y := by
    have : f x ≤ f y := Preorder.le_trans _ _ _ fx_le_z z_le_fy
    simpa
  exact mem_icc_mem_range f x_le_y z_mem_range

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
    simp only [Set.mem_range, Function.comp_apply]
    simp only [Set.mem_preimage] at z_mem_icc
    have := mem_icc_mem_range f y_le_x z_mem_icc
    simp only [Set.mem_range] at this
    obtain ⟨y, hy⟩ := this
    use OrderDual.ofDual y
    exact (Equiv.apply_eq_iff_eq_symm_apply OrderDual.ofDual).mpr hy
    ⟩

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
    rw [Set.ordConnected_iff] at interval_s
    exact interval_s x hx z hz x_le_z ⟨x_le_t, t_lt_z⟩
  · exact ht

def comp (g : β ≤c γ) (f : α ≤c β) : α ≤c γ where
  toFun := g ∘ f
  inj' := Function.Injective.comp g.inj' f.inj'
  map_rel_iff' := Iff.trans g.map_rel_iff' f.map_rel_iff'
  imageOrdConnected := by
    rw [Set.range_comp]
    exact interval_convexEmbedding_interval g f.imageOrdConnected

instance : Monoid (α ≤c α) where
  one := .refl
  mul f g := f.comp g
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

lemma one_def : (1 : α ≤c α) = .refl := rfl
lemma mul_def (f g : α ≤c α) : (f * g) = f.comp g := rfl

@[simp] lemma coe_one : ⇑(1 : α ≤c α) = id := rfl
@[simp] lemma coe_mul (f g : α ≤c α) : ⇑(f * g) = f ∘ g := rfl

lemma one_apply (a : α) : (1 : α ≤c α) a = a := rfl
lemma mul_apply (e₁ e₂ : α ≤c α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp]
theorem image_Ico : f '' Set.Ico a b = Set.Ico (f a) (f b) := by
  ext z
  simp only [Set.mem_image, Set.mem_Ico]
  constructor
  · intro h
    obtain ⟨x, a_le_x, x_lt_b, fx_eq_z⟩ := h
    simp [a_le_x]
  · intro h
    obtain ⟨y, hy⟩ := le_and_le_mem_range f h.1 h.2.le
    use y
    constructor
    · constructor
      · have := h.1
        simpa [←hy, h.1]
      · have := h.2
        simpa [←hy]
    · exact hy

@[simp]
theorem image_Ioc : f '' Set.Ioc a b = Set.Ioc (f a) (f b) := by
  ext z
  simp only [Set.mem_image, Set.mem_Ioc]
  constructor
  · intro h
    obtain ⟨x, a_le_x, x_lt_b, fx_eq_z⟩ := h
    simp [a_le_x]
  · intro h
    obtain ⟨y, hy⟩ := le_and_le_mem_range f h.1.le h.2
    use y
    constructor
    · constructor
      · have := h.1
        simpa [←hy, h.1]
      · have := h.2
        simpa [←hy]
    · exact hy
end ConvexEmbedding

@[coe]
def OrderIso.toConvexEmbedding [Preorder α] [Preorder β] (f : α ≃o β) :
    α ≤c β := ⟨f, by simp [Set.ordConnected_univ]⟩

instance [Preorder α] [Preorder β] : Coe (α ≃o β) (α ≤c β) where
  coe f := f.toConvexEmbedding
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
    simp only [Set.ordConnected_iff, Set.inter_subset_right, Set.range_inclusion, Set.mem_inter_iff,
      Subtype.coe_prop, and_true, Set.mem_setOf_eq, Subtype.forall,
      Subtype.mk_le_mk] at A_interval ⊢
    intro a a_mem_B a_mem_A b b_mem_B b_mem_A a_le_b x x_mem_icc
    simp only [Set.mem_setOf_eq]
    exact A_interval a a_mem_A b b_mem_A a_le_b x_mem_icc
