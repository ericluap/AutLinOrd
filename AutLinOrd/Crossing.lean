import Mathlib
import AutLinOrd.ConvexEmbedding
import AutLinOrd.ExtendsLeftRight
import AutLinOrd.Embeddings
import AutLinOrd.OmegaSum

variable [LinearOrder α]

variable {A B : Set α}

/--
  If `ExtendsLeftRight A B`, `A` is `ℕ` copies of `I`,
  and `B` is `ℕᵒᵈ` copies of `J`, then there exists `T` such that
  `T` is initial in `ℕᵒᵈ ×ₗ J` and `T` convexly embeds in `I`.
-/
theorem initial_seg_embeds_in_single {I J : Type u} [LinearOrder I]
    [LinearOrder J] {A B : Set α} (A_interval : A.OrdConnected)
    (B_interval : B.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B)
    (A_iso : A ≃o ℕ ×ₗ I) (B_iso : B ≃o ℕᵒᵈ ×ₗ J) :
    ∃(T : Type u) (_ : LinearOrder T),
    Nonempty (T ≤i ℕᵒᵈ ×ₗ J) ∧ Nonempty (T ≤c I) ∧ Nonempty T := by
  set S := A ∩ B with S_def

  have S_final_A : Sᵒᵈ ≤i Aᵒᵈ :=
    intersect_extendsLeftRight_final B_interval extendsLeftRight
  have S_initial_B : S ≤i B :=
    intersect_extendsLeftRight_initial A_interval extendsLeftRight

  set map_S_to_A := OrderEmbedding.undual (S_final_A : Sᵒᵈ ↪o Aᵒᵈ)
  set S' := Set.range (map_S_to_A.trans (A_iso : A ↪o ℕ ×ₗ I))
    with S'_def

  have S_nonempty : Nonempty S := by
      simp [S_def, extendsLeftRight_nonempty_inter A B extendsLeftRight]
  have S_ordConnected : S.OrdConnected := Set.OrdConnected.inter'

  have S_iso_S' : S ≃o S' :=
    @ordEmbedding_iso_range _ _ _ _ S_nonempty
      (map_S_to_A.trans (A_iso : A ↪o ℕ ×ₗ I))
  have S'_nonempty : Nonempty S' :=
    (Equiv.nonempty_congr S_iso_S').mp S_nonempty


  have S'_ordConnected : S'.OrdConnected := by
    have : (OrderDual.toDual '' (Set.univ : Set S)).OrdConnected := by
      simp [Set.dual_ordConnected_iff, Set.ordConnected_univ]
    have :
      (S_final_A ∘ OrderDual.toDual '' (Set.univ : Set S)).OrdConnected := by
      rw [Set.image_comp]
      exact ConvexEmbedding.interval_convexEmbedding_interval
        S_final_A.toConvexEmbedding this
    have : (map_S_to_A ''
      (Set.univ : Set S)).OrdConnected := by
      exact Set.ordConnected_dual.mp this
    rw [S'_def, ←Set.image_univ, RelEmbedding.coe_trans, Set.image_comp]
    exact Set.ordConnected_image A_iso

  obtain ⟨T, _, ⟨T_init_S'⟩, ⟨T_convex_I⟩, T_nonempty⟩ :=
    lowerbound_subset_omega S' S'_nonempty S'_ordConnected

  use T, inferInstance
  constructor
  · have S_init_NJ := iso_initial S_initial_B B_iso
    have T_init_S := iso_initial T_init_S' S_iso_S'.symm
    exact Nonempty.intro (T_init_S.trans S_init_NJ)
  · constructor
    · exact Nonempty.intro T_convex_I
    · exact T_nonempty


noncomputable def initial_in_omega_star_swap [LinearOrder T]
    [LinearOrder J] [t_nonempty : Nonempty T] (initial : T ≤i ℕᵒᵈ ×ₗ J) :
    ℕᵒᵈ ×ₗ J ≤i T := by
  let intersectsT (n : ℕ) := ∃(t : T) (j : J),
    toLex (OrderDual.toDual n, j) = initial t
  have existsValidN : ∃n, intersectsT n := by
    simp only [←exists_true_iff_nonempty] at t_nonempty
    obtain ⟨t, _⟩ := t_nonempty
    use OrderDual.ofDual (ofLex (initial t)).1
    simp only [OrderDual.toDual_ofDual, intersectsT]
    use t, (ofLex (initial t)).2
    simp
  open Classical in (
  have n_intersectsT := Nat.find_spec existsValidN
  have n_min_intersectsT (m : ℕ) := Nat.find_min' (m := m) existsValidN
  set n := Nat.find existsValidN)

  have n_lt_intersectsT {m : ℕ} (n_lt_m : n < m) : intersectsT m := by
    simp only [intersectsT] at n_intersectsT ⊢
    obtain ⟨t, j, htj⟩ := n_intersectsT
    set z := toLex (OrderDual.toDual m, j) with z_def
    have z_lt_initialt: z < initial t := by
      simp [←htj, z, Prod.Lex.lt_iff, n_lt_m]
    have := initial.mem_range_of_rel' t z z_lt_initialt
    simp only [InitialSeg.coe_coe_fn, Set.mem_range, z, intersectsT, n] at this
    obtain ⟨y, hy⟩ := this
    use y, j
    simp [←z_def, hy]

  have le_intersect_j {a : ℕ} (h : OrderDual.toDual a ≤ OrderDual.toDual n + 1)
      (j : J) : ∃x : T, initial x = toLex (OrderDual.toDual a, j) := by
    change n + 1 ≤ a at h
    have n_lt_a : n < a := by omega
    obtain ⟨t, _, htj⟩ := n_intersectsT
    set z := toLex (OrderDual.toDual a, j) with z_def
    have z_lt_initialt : z < initial t := by
      simp [z, ←htj, Prod.Lex.lt_iff, n_lt_a]
    have := initial.mem_range_of_rel' t z z_lt_initialt
    simp only [InitialSeg.coe_coe_fn, Set.mem_range, z, n] at this
    exact this


  have : beforeN J (n+1) ≤i T := {
    toFun x := (Function.invFun initial) x.val
    inj' := by
      simp only [Function.Injective, beforeN, toDual_add, toDual_one,
        Set.coe_setOf, Function.invFun, Set.mem_setOf_eq, Subtype.forall,
        Lex.forall, ofLex_toLex, Prod.forall, OrderDual.forall,
        Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, n]
      intro a j a_le_n1 b k b_le_n1 h
      have a_image := le_intersect_j a_le_n1 j
      have a_image_spec := a_image.choose_spec
      have b_image := le_intersect_j b_le_n1 k
      have b_image_spec := b_image.choose_spec
      simp only [a_image, ↓reduceDIte, b_image, n] at h
      generalize_proofs at h
      apply_fun initial at h
      simp only [a_image_spec, b_image_spec, EmbeddingLike.apply_eq_iff_eq,
        Prod.mk.injEq, n] at h
      exact h
    map_rel_iff' := by
      simp only [beforeN, toDual_add, toDual_one, Set.coe_setOf,
        Function.invFun, Set.mem_setOf_eq, Function.Embedding.coeFn_mk,
        Subtype.forall, Lex.forall, ofLex_toLex, Prod.forall, OrderDual.forall,
        Subtype.mk_lt_mk, Prod.Lex.lt_iff, OrderDual.toDual_lt_toDual,
        EmbeddingLike.apply_eq_iff_eq, n]
      intro a j a_le_n1 b k b_le_n1
      have a_image := le_intersect_j a_le_n1 j
      have a_image_spec := a_image.choose_spec
      have b_image := le_intersect_j b_le_n1 k
      have b_image_spec := b_image.choose_spec
      simp only [a_image, ↓reduceDIte, b_image, n]
      generalize_proofs
      have : a_image.choose < b_image.choose ↔
          initial a_image.choose < initial b_image.choose := by
        exact Iff.symm (InitialSeg.lt_iff_lt initial)
      simp [this, a_image_spec, b_image_spec, Prod.Lex.lt_iff]
    mem_range_of_rel' := by
      simp only [beforeN, toDual_add, toDual_one, Set.coe_setOf,
        Set.mem_setOf_eq, Function.invFun, RelEmbedding.coe_mk,
        Function.Embedding.coeFn_mk, Set.mem_range, Subtype.exists, Lex.exists,
        ofLex_toLex, Prod.exists, OrderDual.exists, Subtype.forall, Lex.forall,
        Prod.forall, OrderDual.forall, n]
      intro a j a_le_n1 t h
      have a_image := le_intersect_j a_le_n1 j
      have a_image_spec := a_image.choose_spec
      simp only [a_image, ↓reduceDIte, n] at h
      generalize_proofs at h
      have : initial t < initial a_image.choose := by
        exact (InitialSeg.lt_iff_lt initial).mpr h
      simp only [a_image_spec, Prod.Lex.lt_iff, ofLex_toLex, n] at this
      have : (ofLex (initial t)).1 ≤ OrderDual.toDual n + 1 := by
        obtain _ | ⟨_, _⟩ := this
        <;> order
      have exists_initial_t := le_intersect_j this (ofLex (initial t)).2
      use (ofLex (initial t)).1, (ofLex (initial t)).2, this
      simp only [exists_initial_t, ↓reduceDIte, n]
      apply_fun initial
      · simp [exists_initial_t.choose_spec]
        rfl
      · exact EmbeddingLike.injective' initial
  }

  exact domain_iso_initial this (beforeN_iso J (n + 1))


theorem crossing_embed {I J : Type u} [LinearOrder I] [LinearOrder J]
    {A B : Set α} (A_interval : A.OrdConnected) (B_interval : B.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B) (A_iso : A ≃o ℕ ×ₗ I)
    (B_iso : B ≃o ℕᵒᵈ ×ₗ J) : Nonempty (ℕ ×ₗ I ≤c J) ∧ Nonempty (ℕᵒᵈ ×ₗ J ≤c I)
    := by
  constructor
  · sorry
  · obtain ⟨T, _, init, convex, T_nonempty⟩ := initial_seg_embeds_in_single
      A_interval B_interval extendsLeftRight A_iso B_iso
    simp only [←exists_true_iff_nonempty] at init convex
    obtain ⟨init⟩ := init
    obtain ⟨convex⟩ := convex
    have := initial_in_omega_star_swap init
    exact Nonempty.intro (convex.comp this)
