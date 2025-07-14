import AutLinOrd.Embeddings.SelfConvexEmbedding
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Set.Fin
import AutLinOrd.CalcOrderIso

/-!
  This file proves basic facts about splitting linear orders.
  In particular, it shows that if `2A` convexly embeds in `A`,
  then `A` is isomorphic to `2A`.
-/

seal OrderDual
seal Lex

variable [LinearOrder A]

/--
  If `(a, b) ≤ (a', b')`, then `a ≤ a'`
-/
theorem le_lex_fst_le [LinearOrder B] {a a' : A} {b b' : B}
    (le_lex : toLex (a, b) ≤ toLex (a', b')) : a ≤ a' := by
  simp only [ge_iff_le, Prod.Lex.le_iff, ofLex_toLex] at le_lex
  obtain _ | ⟨_, _⟩ := le_lex
  <;> order

/--
  If `(a, b) ≤ z ≤ (a', b')`, then `a ≤ z.1 ≤ a'`
-/
theorem mem_icc_le_fst [LinearOrder B] {z : A ×ₗ B} {a a' : A} {b b' : B}
    (mem_icc : z ∈ Set.Icc (toLex (a, b)) (toLex (a', b'))) :
    (ofLex z).1 ∈ Set.Icc a a' := by
  have : z = toLex ((ofLex z).1, (ofLex z).2) := by simp
  simp only [Set.mem_Icc] at mem_icc ⊢
  rw [this] at mem_icc
  exact ⟨le_lex_fst_le mem_icc.1, le_lex_fst_le mem_icc.2⟩

/--
  If `A` convexly embeds in `B`, then
  `A ×ₗ C` convexly embeds in `B ×ₗ C`
-/
def first_convex_prod_convex [LinearOrder B] [LinearOrder C]
    (first_convex : A ≤c B) : A ×ₗ C ≤c B ×ₗ C where
  toFun x := toLex (first_convex (ofLex x).1, (ofLex x).2)
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp [Prod.Lex.le_iff]
  imageOrdConnected := by
    simp only [Set.ordConnected_iff, Set.mem_range, Lex.exists, ofLex_toLex, Prod.exists,
      forall_exists_index, Lex.forall, EmbeddingLike.apply_eq_iff_eq, Prod.forall, Prod.mk.injEq,
      and_imp, forall_eq_apply_imp_iff]
    intro b c a fa_eq_b b' c' a' fa_eq_b' bc_le_bc' z z_mem
    have b_le_b' : b ≤ b' := (le_lex_fst_le bc_le_bc' : b ≤ b')
    have z1_mem_icc : (ofLex z).1 ∈ Set.Icc b b' := mem_icc_le_fst z_mem
    rw [←fa_eq_b, ←fa_eq_b'] at z1_mem_icc b_le_b'
    have a_le_a' : a ≤ a' :=
      (OrderEmbedding.le_iff_le first_convex.toRelEmbedding).mp b_le_b'
    have mem_range :=
      ConvexEmbedding.mem_icc_mem_range (f := first_convex) a_le_a' z1_mem_icc
    simp only [Set.mem_range] at mem_range
    obtain ⟨y, hy⟩ := mem_range
    simp only [Set.mem_range, Lex.exists, ofLex_toLex, Prod.exists]
    use y, (ofLex z).2
    simp [hy]

/--
  `2` convexly embeds in `ℕ`
-/
def two_convex_omega : Fin 2 ≤c ℕ where
  toFun x := x
  inj' := by simp [Function.Injective, Fin.val_inj]
  map_rel_iff' := by simp
  imageOrdConnected := by simp [Fin.range_val, Set.ordConnected_Iio]

/-- `2` and its order dual are isomorphic -/
def two_iso_twoDual : (Fin 2) ≃o (Fin 2)ᵒᵈ := Fin.revOrderIso.symm

/--
  `2` convexly embeds in `ℕᵒᵈ`
-/
def two_convex_omegaDual : Fin 2 ≤c ℕᵒᵈ :=
  two_convex_omega.dual.comp two_iso_twoDual

/--
  `2A` convexly embeds in `ℕA`
-/
def two_convex_omega_prod : Fin 2 ×ₗ A ≤c ℕ ×ₗ A :=
  first_convex_prod_convex two_convex_omega

/--
  `2A` convexly emebds in `ℕᵒᵈA`
-/
def two_convex_omegaDual_prod : Fin 2 ×ₗ A ≤c ℕᵒᵈ ×ₗ A :=
  first_convex_prod_convex two_convex_omegaDual

/--
  If `ℕA` convexly embeds in `A`, then `2A` convexly embeds in `A`
-/
def omega_convex_two_convex (omega_convex : ℕ ×ₗ A ≤c A) :
    Fin 2 ×ₗ A ≤c A := omega_convex.comp two_convex_omega_prod

/--
  If `ℕᵒᵈA` convexly emebeds in `A`, then `2A` convexly embeds in `A`
-/
def omegaDual_convex_two_convex (omegaDual_convex : ℕᵒᵈ ×ₗ A ≤c A) :
    Fin 2 ×ₗ A ≤c A := omegaDual_convex.comp two_convex_omegaDual_prod

/--
  The map from `A` to `2A` that maps
  `A` to the first copy of `A` in `2A`
-/
def leftConvex_two : A ≤c Fin 2 ×ₗ A where
  toFun x := toLex (0, x)
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp [Prod.Lex.le_iff]
  imageOrdConnected := by
    simp only [Fin.isValue, Set.ordConnected_iff, Set.mem_range, Prod.Lex.le_iff,
      forall_exists_index, forall_apply_eq_imp_iff, ofLex_toLex, Fin.not_lt_zero, false_or, and_imp,
      forall_const]
    intro a b a_le_b z z_mem
    simp only [Fin.isValue, Set.mem_Icc, Set.mem_range] at z_mem ⊢
    have : z = toLex ((ofLex z).1, (ofLex z).2) := by simp
    rw [this] at z_mem
    simp only [Fin.isValue, Prod.mk.eta, toLex_ofLex, Prod.Lex.le_iff, ofLex_toLex, Fin.not_lt_zero,
      false_or] at z_mem
    grind

@[simp]
theorem leftConvexTwo_apply (a : A) : leftConvex_two a = toLex (0, a) := rfl

/--
  The map from `A` to `2A` that maps
  `A` to the second copy of `A` in `2A`
-/
def rightConvex_two : A ≤c Fin 2 ×ₗ A where
  toFun x := toLex (1, x)
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp [Prod.Lex.le_iff]
  imageOrdConnected := by
    simp only [Fin.isValue, Set.ordConnected_iff, Set.mem_range, Prod.Lex.le_iff,
      forall_exists_index, forall_apply_eq_imp_iff, ofLex_toLex]
    intro a b a_le_b z z_mem
    simp only [Fin.isValue, Set.mem_Icc, Set.mem_range] at z_mem ⊢
    have : z = toLex ((ofLex z).1, (ofLex z).2) := by simp
    rw [this] at z_mem
    simp only [Fin.isValue, Prod.mk.eta, toLex_ofLex, Prod.Lex.le_iff, ofLex_toLex] at z_mem
    grind

@[simp]
theorem rightConvexTwo_apply (a : A) : rightConvex_two a = toLex (1, a) := rfl

theorem leftConvex_lt_rightConvex (a : A) : leftConvex_two a < rightConvex_two a := by
  simp [Prod.Lex.lt_iff]

section twoConvex
variable (twoConvex : Fin 2 ×ₗ A ≤c A)
/--
  Map `A` into the left copy of `2A` and then back into itself
-/
def leftEmb : A ≤c A := twoConvex.comp leftConvex_two

theorem leftEmb_apply (a : A) : leftEmb twoConvex a = twoConvex (toLex (0, a)) := by rfl

/--
  Map `A` into the right copy of `2A` and then back into itself
-/
def rightEmb : A ≤c A := twoConvex.comp rightConvex_two

theorem rightEmb_apply (a : A) : rightEmb twoConvex a = twoConvex (toLex (1, a)) := by rfl

theorem leftEmb_lt_rightEmb (twoConvex : Fin 2 ×ₗ A ≤c A) (a : A) :
    leftEmb twoConvex a < rightEmb twoConvex a := by
  simp [leftEmb_apply, rightEmb_apply, Prod.Lex.lt_iff]

/--
  If `b` lies above the image of the left copy of `A` inside itself,
  and below some point in the right copy of `A` inside itself,
  then `b` is in the image of the right copy of `A` inside itself
-/
theorem mem_range_of_between_left_right
    (leftEmb_lt : ∀ (a : A), twoConvex (toLex (0, a)) < b)
    (lt_rightEmb : b < twoConvex (toLex (1, a))) :
    ∃ y, twoConvex (toLex (1, y)) = b := by
  have b_mem_range :
      b ∈ Set.Icc (twoConvex (toLex (0, a))) (twoConvex (toLex (1, a))) := by
    simp [(fun x => (leftEmb_lt x).le), lt_rightEmb.le]
  have := ConvexEmbedding.mem_icc_mem_range twoConvex (by simp [Prod.Lex.le_iff]) b_mem_range
  simp only [Set.mem_range, Lex.exists, Prod.exists] at this
  obtain ⟨c0, c1, h⟩ := this
  have : c0 = 1 := by
    by_contra!
    rw [show c0 = 0 by omega] at h
    have := leftEmb_lt c1
    order
  use c1
  simp [←this, h]

/--
  `A` is initial in the set of elements greater than the image of
  of mapping `A` into the left copy of `A` inside itself
-/
def A_initial_leftEmbGtImage :
    A ≤i (leftEmb twoConvex).gt_image where
  toFun x := ⟨(rightEmb twoConvex) x, by
    simp [ConvexEmbedding.gt_image, leftEmb_apply, rightEmb_apply, Prod.Lex.lt_iff]⟩
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [ConvexEmbedding.gt_image, Set.coe_setOf, Set.mem_setOf_eq, rightEmb_apply,
      Fin.isValue, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.mem_range, Subtype.forall,
      leftEmb_apply, forall_exists_index, forall_apply_eq_imp_iff, Subtype.mk_lt_mk,
      Subtype.mk.injEq]
    exact fun a a_2 b a_3 ↦ mem_range_of_between_left_right twoConvex b a_3

theorem A_initial_leftEmbGtImage_apply (a : A) :
    A_initial_leftEmbGtImage twoConvex a = rightEmb twoConvex a := by rfl

/--
  If `x` is an element of the points greater than the embedding of `A`
  into the set of points above the left copy of `A`, then it is
  in the set of points greater than the right copy of `A`
-/
theorem A_initial_leftEmbGtImage_mem_rightCompl
    (x : (A_initial_leftEmbGtImage twoConvex).compl) :
    ↑x ∈ (rightEmb twoConvex).gt_image := by
  simp [ConvexEmbedding.gt_image, rightEmb_apply]
  intro a
  have not_equal := x.prop
  simp [A_initial_leftEmbGtImage, rightEmb, InitialSeg.compl, compl, Subtype.eq_iff] at not_equal
  change ∀x_1 : A, ¬(twoConvex (toLex (1,x_1))) = x at not_equal
  have left_lt : ∀x_1 : A, twoConvex (toLex (0, x_1)) < x := by
    have := x.val.prop.out
    simp only [Set.mem_range, leftEmb_apply, Fin.isValue, ConvexEmbedding.gt_image,
      Set.mem_setOf_eq, Set.coe_setOf, forall_exists_index, forall_apply_eq_imp_iff] at this
    exact this
  by_contra!
  obtain lt | eq := this.lt_or_eq
  · obtain ⟨y, hy⟩ := mem_range_of_between_left_right twoConvex left_lt lt
    specialize not_equal y
    order
  · specialize not_equal a
    order

/--
  If `x` is a term of the type of points greater than the right copy of `A`,
  then `x` is an element of the set of points greater than the left copy of `A`
-/
theorem mem_leftGtImage_of_rightGtImage (x : (rightEmb twoConvex).gt_image) :
    ↑x ∈ (leftEmb twoConvex).gt_image := by
  have := x.prop
  simp only [ConvexEmbedding.gt_image, Set.mem_range, rightEmb_apply, Fin.isValue,
    forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq, leftEmb_apply] at ⊢ this
  intro a
  specialize this a
  transitivity twoConvex (toLex (1, a))
  · simp [Prod.Lex.lt_iff]
  · exact this

/--
  If `x` is a term of the type of points greater than the right copy of `A`,
  then `x` is an element of the set of points greater than the embedding of `A`
  into the set of elements above the left copy of `A`
-/
theorem mem_leftGtImageCompl_of_rightGtImage (x : (rightEmb twoConvex).gt_image) :
    ⟨x, mem_leftGtImage_of_rightGtImage twoConvex x⟩ ∈ (A_initial_leftEmbGtImage twoConvex).compl := by
  simp only [InitialSeg.compl, A_initial_leftEmbGtImage, rightEmb_apply, Fin.isValue,
    Set.mem_compl_iff, Set.mem_range, not_exists]
  intro a eq
  simp only [Fin.isValue, Subtype.eq_iff] at eq
  change twoConvex (toLex (1, a)) = x at eq
  have := x.prop
  simp only [ConvexEmbedding.gt_image, Set.mem_range, rightEmb_apply, Fin.isValue,
    forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq] at this
  specialize this a
  order

/--
  The set of elements above the embedding of `A` into the set
  of elements above the left copy of `A` is isomorphic to the set
  of elements above the right copy of `A`
-/
def A_initial_leftEmbGtImage_iso_rightCompl :
    (A_initial_leftEmbGtImage twoConvex).compl ≃o (rightEmb twoConvex).gt_image where
  toFun x := ⟨x, A_initial_leftEmbGtImage_mem_rightCompl twoConvex x⟩
  invFun x := ⟨⟨x, mem_leftGtImage_of_rightGtImage twoConvex x⟩,
    mem_leftGtImageCompl_of_rightGtImage twoConvex x⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp

/--
  The linear order `m` plus the linear order `n`
  is isomorphic to the linear order `m + n`
-/
def finSumIso (m n : ℕ) : Fin m ⊕ₗ Fin n ≃o Fin (m + n) where
  toFun := finSumFinEquiv (m := m) (n := n) ∘ ofLex
  invFun := toLex ∘ (finSumFinEquiv (m := m) (n := n)).invFun
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by
    intro a b
    cases' a with a; obtain a | a := a
    <;> (cases' b with b; obtain b | b := b)
    all_goals simp [Fin.castAdd, Fin.natAdd, Fin.castLE]
    <;> omega

/--
  `A + A` is isomorphic to `2A`
-/
def A_plus_A_iso_2A : A ⊕ₗ A ≃o Fin 2 ×ₗ A := by
  orderCalc A ⊕ₗ A
  _ ≃o Fin 1 ×ₗ A ⊕ₗ Fin 1 ×ₗ A := by orderCongr [(Prod.Lex.uniqueProd (Fin 1) A).symm]
  _ ≃o (Fin 1 ⊕ₗ Fin 1) ×ₗ A := OrderIso.sumProdDistrib (Fin 1) (Fin 1) A |>.symm
  _ ≃o Fin 2 ×ₗ A := by orderCongr [finSumIso]

/--
  If `2A` convexly embeds in `A`,
  then `A` is isomorphic to `2A`
-/
noncomputable def splitting_of_twoConvex : A ≃o Fin 2 ×ₗ A := by
  orderCalc A
  _ ≃o A ⊕ₗ (leftEmb twoConvex).gt_image := (leftEmb twoConvex).absorb_gtImage.symm
  _ ≃o A ⊕ₗ A ⊕ₗ (A_initial_leftEmbGtImage twoConvex).compl := by
      orderCongr [(initial_as_sum (A_initial_leftEmbGtImage twoConvex)).symm]
  _ ≃o A ⊕ₗ A ⊕ₗ (rightEmb twoConvex).gt_image := by
      orderCongr [A_initial_leftEmbGtImage_iso_rightCompl]
  _ ≃o A ⊕ₗ A := by orderCongr [(rightEmb twoConvex).absorb_gtImage]
  _ ≃o Fin 2 ×ₗ A := A_plus_A_iso_2A

end twoConvex
