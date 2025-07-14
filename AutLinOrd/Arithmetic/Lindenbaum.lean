import AutLinOrd.Arithmetic.Sum
import AutLinOrd.Embeddings.SelfConvexEmbedding
import AutLinOrd.Embeddings.InitialSeg
import AutLinOrd.CalcOrderIso

/-!
  This file proves Lindenbaum's theorem which says that if
  `A` is initial in `B` and `B` is final in `A`, then
  `A` is isomorphic to `B`.
-/

seal OrderDual
seal Lex

variable [LinearOrder X] [LinearOrder A] [LinearOrder B]
    (x_eq_axb : X ≃o A ⊕ₗ X ⊕ₗ B)

macro "lex_cases" z:ident : tactic => `(tactic|
  (cases' $z:term with $z:ident; obtain $z | $z := $z;))
macro "axb_cases " z:ident : tactic => `(tactic|
  (lex_cases $z; rotate_left; lex_cases $z; rotate_right))

/--
  Reinterpret the map `X ≃o A ⊕ₗ X ⊕ₗ B`
  as an embedding from `A ⊕ₗ X ⊕ₗ B` to itself
-/
def axb_emb : A ⊕ₗ X ⊕ₗ B ≤c A ⊕ₗ X ⊕ₗ B where
  toFun x := Sum.inrₗ (Sum.inlₗ (x_eq_axb.symm x))
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  imageOrdConnected := by
    simp only [Set.ordConnected_iff,
    Set.mem_range, Lex.exists, Sum.exists, Lex.forall, EmbeddingLike.apply_eq_iff_eq, Sum.forall,
    reduceCtorEq, exists_false, or_self, IsEmpty.forall_iff, implies_true, Sum.inr.injEq,
    Sum.inl.injEq, and_true, true_and, Sum.Lex.toLex_le_toLex, Sum.Lex.sep, forall_const,
    Sum.lex_inr_inr, Sum.lex_inl_inl, Sum.lex_inr_inl, not_false_eq_true, Set.Icc_eq_empty,
    Set.empty_subset]
    rintro x (⟨a, ha⟩ | ⟨a, ha⟩ | ⟨a, ha⟩) y (⟨b, hb⟩ | ⟨b, hb⟩ | ⟨b, hb⟩)
      x_le_y z ⟨x_le_z, z_le_y⟩
    <;> axb_cases z
    all_goals simp at x_le_z
    all_goals simp at z_le_y
    all_goals (use x_eq_axb z; simp)

@[simp]
theorem axb_emb_apply (x : A ⊕ₗ X ⊕ₗ B) :
    (axb_emb x_eq_axb) x = Sum.inrₗ (Sum.inlₗ (x_eq_axb.symm x)) := by
  rfl

/--
  The range of `axb_emb` is all of `X` in `A + X + B`
-/
theorem axb_emb_range_x :
    Set.range (axb_emb x_eq_axb) = Set.range (Sum.inrₗ ∘ Sum.inlₗ) := by
  ext z
  simp
  constructor
  · grind
  · rintro ⟨y, hy⟩
    axb_cases z
    · simp at hy
    · simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, Sum.inl.injEq] at hy
      subst_vars
      have : ∃t, x_eq_axb.symm t = z := (OrderIso.surjective x_eq_axb.symm) z
      simpa
    · simp at hy

/--
  `axb_emb.lt_image` is isomorphic to `A` in `A + X + B`
-/
theorem axb_ltImage_eq_left : (axb_emb x_eq_axb).lt_image = Set.range Sum.inlₗ := by
  ext z
  axb_cases z
  <;> simp [ConvexEmbedding.lt_image, axb_emb_range_x]
  · use z
  · use (x_eq_axb.symm (Sum.inrₗ (Sum.inrₗ z)))
/--
   The `A` in `A + X + B` is isomorphic to `A`
-/
noncomputable def A_iso_left : A ≃o (Set.range Sum.inlₗ : Set (A ⊕ₗ X ⊕ₗ B)) :=
  OrderEmbedding.orderIso (f := ⟨⟨Sum.inlₗ, by simp [Function.Injective]⟩, by simp⟩)

/--
  `axb_emb.gt_image` is isomorphic to `B` in `A + X + B`
-/
theorem axb_gtImage_eq_right :
    (axb_emb x_eq_axb).gt_image = Set.range (Sum.inrₗ ∘ Sum.inrₗ) := by
  ext z
  axb_cases z
  <;> simp [ConvexEmbedding.gt_image, axb_emb_range_x]
  · use (x_eq_axb.symm (Sum.inlₗ z))
  · use z
/--
  The `B` in `A + X + B` is isomorphic to `B`
-/
noncomputable def B_iso_right : B ≃o (Set.range (Sum.inrₗ ∘ Sum.inrₗ) : Set (A ⊕ₗ X ⊕ₗ B)) :=
  OrderEmbedding.orderIso (f := ⟨⟨Sum.inrₗ ∘ Sum.inrₗ, by simp [Function.Injective]⟩, by simp⟩)

/--
  If `X` is isomorphic to `A + X + B`, then,
  `A + X + B` is isomorphic to `ℕA + (axb_emb x_eq_axb).center + ℕᵒᵈB`
-/
noncomputable def axb_decomp : A ⊕ₗ X ⊕ₗ B ≃o ℕ ×ₗ A ⊕ₗ (axb_emb x_eq_axb).center ⊕ₗ ℕᵒᵈ ×ₗ B := by
  orderCalc A ⊕ₗ X ⊕ₗ B
  _ ≃o ℕ ×ₗ (axb_emb x_eq_axb).lt_image ⊕ₗ (axb_emb x_eq_axb).center ⊕ₗ
      ℕᵒᵈ ×ₗ (axb_emb x_eq_axb).gt_image := (axb_emb x_eq_axb).decomp
  _ ≃o ℕ ×ₗ A ⊕ₗ (axb_emb x_eq_axb).center ⊕ₗ ℕᵒᵈ ×ₗ B := by
    orderCongr
    · exact ((axb_ltImage_eq_left x_eq_axb) ▸ A_iso_left).symm
    · exact ((axb_gtImage_eq_right x_eq_axb) ▸ B_iso_right).symm

/--
  If `X` is isomorphic to `A + X + B`, then
  `X` is isomorphic to `ℕA + (axb_emb x_eq_axb).center + ℕᵒᵈB`
-/
noncomputable def x_decomp := x_eq_axb.trans (axb_decomp x_eq_axb)

/--
  If `X` is isomorphic to `A + X + B`, then
  `ℕA` is initial in `X`
-/
noncomputable def omegaA_initial_x : ℕ ×ₗ A ≤i X := by
  orderCalc ℕ ×ₗ A
  _ ≤i ℕ ×ₗ A ⊕ₗ (axb_emb x_eq_axb).center ⊕ₗ ℕᵒᵈ ×ₗ B := fst_inital_sum
  _ ≤i X := (x_decomp x_eq_axb).symm.toInitialSeg

/--
  If `X` is isomorphic to `A + X + B`, then
  `ℕᵒᵈB` is final in `X`
-/
noncomputable def omegaDualB_final_x : (ℕᵒᵈ ×ₗ B)ᵒᵈ ≤i Xᵒᵈ := by
  orderCalc (ℕᵒᵈ ×ₗ B)ᵒᵈ
  _ ≤i ((axb_emb x_eq_axb).center ⊕ₗ ℕᵒᵈ ×ₗ B)ᵒᵈ := snd_final_sum
  _ ≤i (ℕ ×ₗ A ⊕ₗ (axb_emb x_eq_axb).center ⊕ₗ ℕᵒᵈ ×ₗ B)ᵒᵈ := snd_final_sum
  _ ≤i Xᵒᵈ := (x_decomp x_eq_axb).symm.dual.toInitialSeg

/--
  If `X` is isomorphic to `A + X + B`, then
  `X` is isomorphic to `A + X`
-/
noncomputable def ax_eq_x_of_x_eq_axb : X ≃o A ⊕ₗ X :=
  omegaA_initial_absorbs (omegaA_initial_x x_eq_axb) |>.symm

/--
  If `X` is isomorphic to `A + X + B`, then
  `X` is isomorphic to `X + B`
-/
noncomputable def xb_eq_x_of_x_eq_axb: X ≃o X ⊕ₗ B:=
  omegaDualA_final_absorbs (omegaDualB_final_x x_eq_axb) |>.symm

/--
  Lindenbaum's Theorem:
  If `A` is initial in `B` and `B` is final in `A`,
  then `A` is isomporphic to `B`
-/
noncomputable def initial_final_iso (initial : A ≤i B) (final : Bᵒᵈ ≤i Aᵒᵈ) : A ≃o B :=
  let B_sum : A ⊕ₗ initial.compl ≃o B := initial_as_sum initial
  let A_sum : final.complDual ⊕ₗ B ≃o A := final_as_sum final
  let A_split : A ≃o final.complDual ⊕ₗ A ⊕ₗ initial.compl := by
    orderCalc A
    _ ≃o final.complDual ⊕ₗ B := A_sum.symm
    _ ≃o final.complDual ⊕ₗ A ⊕ₗ initial.compl := by orderCongr [B_sum.symm]
  xb_eq_x_of_x_eq_axb A_split |>.trans B_sum
