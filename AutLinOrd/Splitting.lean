import Mathlib
import AutLinOrd.ConvexEmbedding

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
