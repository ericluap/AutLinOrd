import AutLinOrd.Arithmetic.Sum
import AutLinOrd.Embeddings.SelfConvexEmbedding

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
  The range of `axb_emb` is all of `X `in `A + X + B`
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
noncomputable def axb_decomp :=
  let axb_eq_omegaLtImage_center_omegaDualGtImage := (axb_emb x_eq_axb).decomp
  let B_iso_gtImage := (axb_gtImage_eq_right x_eq_axb).symm ▸ B_iso_right
  let A_iso_ltImage := (axb_ltImage_eq_left x_eq_axb).symm ▸ A_iso_left
  let omegaLtImage_iso_omegaA := OrderIso.prodCongr (OrderIso.refl ℕ) A_iso_ltImage.symm
  let omegaDualGtImage_iso_omegaDualB := OrderIso.prodCongr (OrderIso.refl ℕᵒᵈ) B_iso_gtImage.symm
  let omegaLtImage_center_omegaDualGtImage_eq_A_center_B := OrderIso.sumLexCongr omegaLtImage_iso_omegaA
    (OrderIso.sumLexCongr
      (OrderIso.refl (axb_emb x_eq_axb).center)
      omegaDualGtImage_iso_omegaDualB)
  axb_eq_omegaLtImage_center_omegaDualGtImage.trans
    omegaLtImage_center_omegaDualGtImage_eq_A_center_B

/--
  If `X` is isomorphic to `A + X + B`, then
  `X` is isomorphic to `ℕA + (axb_emb x_eq_axb).center + ℕᵒᵈB`
-/
noncomputable def x_decomp := x_eq_axb.trans (axb_decomp x_eq_axb)

/--
  If `X` is isomorphic to `A + X + B`, then
  `ℕA` is initial in `X`
-/
noncomputable def omegaA_initial_x : ℕ ×ₗ A ≤i X :=
 let omegaA_initial_decomp := fst_inital_sum (α := ℕ ×ₗ A) (β := (axb_emb x_eq_axb).center ⊕ₗ ℕᵒᵈ ×ₗ B)
 omegaA_initial_decomp.trans (x_decomp x_eq_axb).symm.toInitialSeg

/--
  If `X` is isomorphic to `A + X + B`, then
  `ℕᵒᵈB` is final in `X`
-/
noncomputable def omegaDualB_final_x : (ℕᵒᵈ ×ₗ B)ᵒᵈ ≤i Xᵒᵈ :=
 let centerB_final_decomp := snd_final_sum (α := ℕ ×ₗ A) (β := (axb_emb x_eq_axb).center ⊕ₗ ℕᵒᵈ ×ₗ B)
 let omegaDualB_final_centerB := snd_final_sum (α := (axb_emb x_eq_axb).center) (β := ℕᵒᵈ ×ₗ B)
 (omegaDualB_final_centerB.trans centerB_final_decomp).trans (x_decomp x_eq_axb).symm.dual.toInitialSeg

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
  let B_sum := initial_as_sum initial
  let A_sum := final_as_sum final
  let A_split := A_sum.symm.trans (OrderIso.sumLexCongr (OrderIso.refl final.complDual) B_sum.symm)
  xb_eq_x_of_x_eq_axb A_split |>.trans B_sum
