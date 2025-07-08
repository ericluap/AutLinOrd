import AutLinOrd.Embeddings.ConvexEmbedding
import Mathlib.Algebra.Order.Group.End
import Mathlib.Order.InitialSeg
import Mathlib.Tactic.ApplyFun

seal OrderDual
seal Lex

/--
  The image of an `InitialSeg` is `OrdConnected`.
-/
theorem image_initialSeg_ordConnected [Preorder α] [PartialOrder β]
    (f : α ≤i β) : (Set.range f).OrdConnected := by
  have := f.mem_range_of_rel'
  simp only [Set.ordConnected_iff, Set.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff]
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

def InitialSeg.undual [PartialOrder α] [PartialOrder β]
    (final : αᵒᵈ ≤i βᵒᵈ) : α ≤c β := final.toConvexEmbedding.undual

section Preorder
variable [Preorder α] [Preorder β]

/--
  `α` is initial in `α + β`
-/
def fst_inital_sum : α ≤i α ⊕ₗ β where
  toFun x := Sum.inlₗ x
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by simp

/--
  `β` is final in `α + β`
-/
def snd_final_sum : βᵒᵈ ≤i (α ⊕ₗ β)ᵒᵈ where
  toFun x := OrderDual.toDual (Sum.inrₗ (OrderDual.ofDual x))
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by simp

/--
  The complement of the range of the initial segment
-/
def InitialSeg.compl (initial : α ≤i β) : Set β := (Set.range initial)ᶜ

/--
  The complement of the range of an initial segment is a final segment
-/
def InitialSeg.complFinal (initial : α ≤i β) : initial.complᵒᵈ ≤i βᵒᵈ where
  toFun x := OrderDual.toDual (OrderDual.ofDual x).val
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [InitialSeg.compl, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.mem_range,
      OrderDual.exists, OrderDual.ofDual_toDual, Subtype.exists, Set.mem_compl_iff, not_exists,
      exists_prop, OrderDual.forall, OrderDual.toDual_lt_toDual, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, Subtype.forall]
    intro b b_mem c b_lt_c a initial_a_eq_c
    subst_vars
    have b_mem_range := initial.mem_range_of_rel' a b b_lt_c
    simp only [InitialSeg.coe_coe_fn, Set.mem_range] at b_mem_range
    grind

end Preorder

section InitialAsSum
variable [PartialOrder α] [LinearOrder β] (initial : α ≤i β)

theorem complFinal_apply (a_mem : a ∈ initial.compl) :
    initial.complFinal.undual ⟨a, a_mem⟩ = a := by rfl

theorem complFinal_range_eq_compl :
    Set.range initial.complFinal.undual = initial.compl := by
  ext z
  simp [complFinal_apply]

theorem complFinal_apply_not_mem_initial (a_mem : a ∈ initial.compl) :
    ¬initial.complFinal.undual ⟨a, a_mem⟩ ∈ Set.range initial := by
  simpa [InitialSeg.compl] using a_mem

theorem exists_compl_eq_complFinal_apply (a_mem : a ∈ initial.compl) :
    ∃x, initial.complFinal.undual.toRelEmbedding x =
    initial.complFinal.undual ⟨a, a_mem⟩ := by
  use ⟨a, a_mem⟩
  rfl

theorem initial_lt_mem_compl (b_mem : b ∈ initial.compl) : initial a < b := by
  by_contra!
  simp only [InitialSeg.compl, Set.mem_compl_iff, Set.mem_range, not_exists] at b_mem
  obtain lt | eq := this.lt_or_eq
  · have := initial.mem_range_of_rel' a b lt
    simp only [InitialSeg.coe_coe_fn, Set.mem_range] at this
    grind
  · grind

theorem initial_le_mem_compl (b_mem : b ∈ initial.compl) : initial a ≤ b :=
  (initial_lt_mem_compl initial b_mem).le

theorem exists_compl_choose_eq_compl (a_mem : a ∈ initial.compl) :
    (exists_compl_eq_complFinal_apply initial a_mem).choose = ⟨a, a_mem⟩ := by
  generalize_proofs h
  have := h.choose_spec
  simp only [complFinal_apply] at this
  apply_fun initial.complFinal.undual.toRelEmbedding
  · simp only [this]
    rfl
  · simp [Function.Injective]

theorem mem_range_initial_nonempty (a_mem : a ∈ Set.range initial) :
    Nonempty α := by
  simp only [Set.mem_range] at a_mem
  obtain ⟨y, _⟩ := a_mem
  use y

theorem not_mem_range_compl_nonempty (not_mem : a ∉ Set.range initial) :
    Nonempty initial.compl := by
  have : a ∈ initial.compl := not_mem
  use a

/--
  If `α` is initial in `β`, then we can write `β` as
  `α + γ = β` where `γ` is the linear order `initial.compl`.
-/
noncomputable def initial_as_sum (initial : α ≤i β) :
    α ⊕ₗ initial.compl ≃o β where
  toFun x := (ofLex x).elim (fun a => initial a)
    (fun c => initial.complFinal.undual c)
  invFun x :=
    open scoped Classical in
    if h : x ∈ Set.range initial then
      have : Nonempty α := mem_range_initial_nonempty initial h
      Sum.inlₗ (initial.toFun.invFun x)
    else
      have : Nonempty (initial.compl) := not_mem_range_compl_nonempty initial h
      Sum.inrₗ (initial.complFinal.undual.toFun.invFun x)
  left_inv := by
    simp only [Function.LeftInverse, Set.mem_range, Function.invFun,
      Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, InitialSeg.coe_coe_fn,
      Subtype.exists, Lex.forall, ofLex_toLex, Sum.forall, Sum.elim_inl,
      EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte, Classical.choose_eq, implies_true,
      Sum.elim_inr, complFinal_apply_not_mem_initial initial,
      exists_compl_eq_complFinal_apply initial, exists_compl_choose_eq_compl initial,
      Subtype.coe_eta, and_self]
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Set.mem_range,
      Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, InitialSeg.coe_coe_fn]
    intro b
    by_cases h : b ∈ Set.range initial
    · simp only [h]
      have : Nonempty α := mem_range_initial_nonempty initial h
      apply Function.invFun_eq
      simpa using h
    · have : Nonempty initial.compl := not_mem_range_compl_nonempty initial h
      simp only [h, ↓reduceDIte, ofLex_toLex, Sum.elim_inr]
      apply Function.invFun_eq
      use ⟨b, h⟩
      rfl
  map_rel_iff' := by
    simp only [Set.mem_range, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      InitialSeg.coe_coe_fn, Equiv.coe_fn_mk, ge_iff_le, Lex.forall, ofLex_toLex, Sum.forall,
      Sum.elim_inl, Sum.elim_inr, Subtype.forall, complFinal_apply, Sum.Lex.toLex_le_toLex,
      InitialSeg.le_iff_le, Sum.lex_inl_inl, implies_true, Sum.Lex.sep, iff_true, true_and,
      Sum.lex_inr_inl, iff_false, not_le, Sum.lex_inr_inr, Subtype.mk_le_mk, and_true]
    constructor
    · grind [initial_le_mem_compl]
    · grind [initial_lt_mem_compl]

end InitialAsSum

namespace InitialSeg
variable {α : Type*} [Preorder α]

instance : Monoid (α ≤i α) where
  one := .refl (· < ·)
  mul f g := g.trans f
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

lemma one_def : (1 : α ≤i α) = .refl (· < ·) := rfl
lemma mul_def (f g : α ≤i α) : (f * g) = g.trans f := rfl

@[simp] lemma coe_one : ⇑(1 : α ≤i α) = id := rfl
@[simp] lemma coe_mul (f g : α ≤i α) : ⇑(f * g) = f ∘ g := rfl

lemma one_apply (a : α) : (1 : α ≤i α) a = a := rfl
lemma mul_apply (e₁ e₂ : α ≤i α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
end InitialSeg
