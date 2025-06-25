import AutLinOrd.Embeddings
import AutLinOrd.OmegaSum

seal OrderDual
seal Lex

/-!
  This file proves that if two intervals in a linear order `A` and `B`
  intersect such that `A` extends to the left and `B` extends to the right
  and `A ≃o ℕ ×ₗ I` and `B ≃o ℕᵒᵈ ×ₗ J`, then
  `ℕ ×ₗ I` convexly embeds in `J` and `ℕᵒᵈ ×ₗ J` convexly embeds in `I`.
-/

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

  set map_S_to_A := (A_iso.toConvexEmbedding).comp
    S_final_A.toUndualConvexEmbedding
  set S' := Set.range map_S_to_A

  have S_nonempty : Nonempty S := by
      simp [S_def, extendsLeftRight_nonempty_inter A B extendsLeftRight]
  have S_ordConnected : S.OrdConnected := Set.OrdConnected.inter'

  have S_iso_S' : S ≃o S' :=
    ordEmbedding_iso_range (α := S) (β := ℕ ×ₗ I) map_S_to_A
  have S'_nonempty : Nonempty S' :=
    (Equiv.nonempty_congr S_iso_S').mp S_nonempty
  have S'_ordConnected : S'.OrdConnected := map_S_to_A.imageOrdConnected

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

/--
  If `ExtendsLeftRight A B`, `A` is `ℕ` copies of `I`,
  and `B` is `ℕᵒᵈ` copies of `J`, then there exists `T` such that
  `T` is final in `ℕ ×ₗ I` and `T` convexly embeds in `J`.
-/
theorem final_seg_embeds_in_single {I J : Type u} [LinearOrder I]
    [LinearOrder J] {A B : Set α} (A_interval : A.OrdConnected)
    (B_interval : B.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B)
    (A_iso : A ≃o ℕ ×ₗ I) (B_iso : B ≃o ℕᵒᵈ ×ₗ J) :
    ∃(T : Type u) (_ : LinearOrder T),
    Nonempty (Tᵒᵈ ≤i (ℕ ×ₗ I)ᵒᵈ) ∧ Nonempty (T ≤c J) ∧ Nonempty T := by
  set S := A ∩ B with S_def

  have S_final_A : Sᵒᵈ ≤i Aᵒᵈ :=
    intersect_extendsLeftRight_final B_interval extendsLeftRight
  have S_initial_B : S ≤i B :=
    intersect_extendsLeftRight_initial A_interval extendsLeftRight

  set S' := Set.range (iso_initial S_initial_B B_iso)

  have S_nonempty : Nonempty S := by
      simp [S_def, extendsLeftRight_nonempty_inter A B extendsLeftRight]
  have S_ordConnected : S.OrdConnected := Set.OrdConnected.inter'

  have S_iso_S' : S ≃o S' := ordEmbedding_iso_range (α := S) (β := ℕᵒᵈ ×ₗ J)
      (iso_initial S_initial_B B_iso)
  have S'_nonempty : Nonempty S' :=
    (Equiv.nonempty_congr S_iso_S').mp S_nonempty
  have S'_ordConnected : S'.OrdConnected := image_initialSeg_ordConnected
    (iso_initial S_initial_B B_iso)

  obtain ⟨T, _, ⟨T_final_S'⟩, ⟨T_convex_J⟩, T_nonempty⟩ :=
    upperbound_subset_omega_dual S' S'_nonempty S'_ordConnected

  use T, inferInstance
  constructor
  · have S_final_NI := iso_initial S_final_A A_iso.dual
    have T_final_S := iso_initial T_final_S' S_iso_S'.symm.dual
    exact Nonempty.intro (T_final_S.trans S_final_NI)
  · constructor
    · exact Nonempty.intro T_convex_J
    · exact T_nonempty

/--
  If `T` is initial in `ℕᵒᵈ ×ₗ J`, then `ℕᵒᵈ ×ₗ J` is initial in `T`.
-/
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

  have le_intersect_j {a : ℕ} (h : OrderDual.toDual a ≤ OrderDual.toDual n + 1)
      (j : J) : ∃x : T, initial x = toLex (OrderDual.toDual a, j) := by
    change n + 1 ≤ a at h
    have n_lt_a : n < a := by omega
    obtain ⟨t, _, htj⟩ := n_intersectsT
    set z := toLex (OrderDual.toDual a, j) with z_def
    have z_lt_initialt : z < initial t := by
      simp [z, ←htj, Prod.Lex.lt_iff, n_lt_a]
    have := initial.mem_range_of_rel' t z z_lt_initialt
    simpa

  have n_lt_intersectsT {m : ℕ} (n_lt_m : n < m) : intersectsT m := by
    simp only [intersectsT] at n_intersectsT ⊢
    obtain ⟨t, j, htj⟩ := n_intersectsT
    have := le_intersect_j n_lt_m j
    grind

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
      simpa [a_image_spec, b_image_spec] using h
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
      have : OrderDual.toDual (OrderDual.ofDual ((ofLex (initial t)).1)) ≤ OrderDual.toDual n + 1 := by
        obtain _ | ⟨_, _⟩ := this
        <;> simp
        all_goals order
      have exists_initial_t := le_intersect_j this (ofLex (initial t)).2
      use OrderDual.ofDual (ofLex (initial t)).1, (ofLex (initial t)).2, this
      simp only [exists_initial_t, ↓reduceDIte, n]
      apply_fun initial
      · simp [exists_initial_t.choose_spec]
      · exact EmbeddingLike.injective' initial
  }

  exact domain_iso_initial this (beforeN_iso J (n + 1))

/--
  If `T` is final in `ℕ ×ₗ J`, then `ℕ ×ₗ J` is final in `T`.
-/
noncomputable def final_in_omega_swap [LinearOrder T]
    [LinearOrder J] [t_nonempty : Nonempty T] (final : Tᵒᵈ ≤i (ℕ ×ₗ J)ᵒᵈ) :
    (ℕ ×ₗ J)ᵒᵈ ≤i Tᵒᵈ := by
  let intersectsT (n : ℕ) := ∃(t : T) (j : J),
    OrderDual.toDual (toLex (n, j)) = final (OrderDual.toDual t)
  have existsValidN : ∃n, intersectsT n := by
    simp only [←exists_true_iff_nonempty] at t_nonempty
    obtain ⟨t, _⟩ := t_nonempty
    use (ofLex (OrderDual.ofDual (final (OrderDual.toDual t)))).1
    simp only [intersectsT]
    use t, (ofLex (OrderDual.ofDual ((final (OrderDual.toDual t))))).2
    simp
  open Classical in (
  have n_intersectsT := Nat.find_spec existsValidN
  have n_min_intersectsT (m : ℕ) := Nat.find_min' (m := m) existsValidN
  set n := Nat.find existsValidN)

  have le_intersect_j {a : ℕ} (h : n < a)
      (j : J) : ∃x : Tᵒᵈ,
      final x = OrderDual.toDual (toLex (a, j)) := by
    obtain ⟨t, _, htj⟩ := n_intersectsT
    set z := OrderDual.toDual (toLex (a, j)) with z_def
    have z_lt_finalt : z < final (OrderDual.toDual t) := by
      simp [z, ←htj, Prod.Lex.lt_iff, h]
    have := final.mem_range_of_rel' (OrderDual.toDual t) z z_lt_finalt
    simpa

  have n_lt_intersectsT {m : ℕ} (n_lt_m : n < m) : intersectsT m := by
    simp only [intersectsT] at n_intersectsT ⊢
    obtain ⟨t, j, htj⟩ := n_intersectsT
    obtain ⟨x, hx⟩ := le_intersect_j n_lt_m j
    use OrderDual.ofDual x, j
    simp [hx]

  set afterN_map : (afterN J (n+1))ᵒᵈ → Tᵒᵈ := fun x =>
    (Function.invFun final) (OrderDual.toDual ((OrderDual.ofDual x).val))

  have afterN_map_inj: Function.Injective afterN_map := by
    simp only [afterN_map, Function.Injective, afterN, Set.coe_setOf, Function.invFun, Set.mem_setOf_eq,
        OrderDual.exists, OrderDual.forall, OrderDual.ofDual_toDual, Subtype.forall, Lex.forall,
        ofLex_toLex, Prod.forall, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, Prod.mk.injEq]
    intro a j a_le_n1 b k b_le_n1 h
    have a_image := le_intersect_j a_le_n1 j
    have a_image_spec := a_image.choose_spec
    have b_image := le_intersect_j b_le_n1 k
    have b_image_spec := b_image.choose_spec
    simp only [afterN_map, a_image, ↓reduceDIte, b_image, n, intersectsT] at h
    generalize_proofs at h
    apply_fun final at h
    simpa [a_image_spec, b_image_spec] using h

  have afterN_map_rel_iff' : ∀ {a b : (↑(afterN J (n + 1)))ᵒᵈ},
      afterN_map a < afterN_map b ↔ a < b := by
    simp only [afterN_map, afterN, Set.coe_setOf, Function.invFun, Set.mem_setOf_eq, OrderDual.exists,
        Function.Embedding.coeFn_mk, OrderDual.forall, OrderDual.ofDual_toDual, Subtype.forall,
        Lex.forall, ofLex_toLex, Prod.forall, OrderDual.toDual_lt_toDual, Subtype.mk_lt_mk, n,
        intersectsT]
    intro a j a_le_n1 b k b_le_n1
    have a_image := le_intersect_j a_le_n1 j
    have a_image_spec := a_image.choose_spec
    have b_image := le_intersect_j b_le_n1 k
    have b_image_spec := b_image.choose_spec
    simp only [a_image, ↓reduceDIte, b_image, n]
    generalize_proofs
    have : a_image.choose < b_image.choose ↔
        final a_image.choose < final b_image.choose := by
      exact Iff.symm (InitialSeg.lt_iff_lt final)
    simp [this, a_image_spec, b_image_spec, Prod.Lex.lt_iff]

  have afterN_map_mem_range_of_rel' : ∀ (a : (↑(afterN J (n + 1)))ᵒᵈ),
      ∀ b < afterN_map a, b ∈ Set.range afterN_map := by
    simp [afterN_map, afterN, Function.invFun]
    intro a j n1_le_a t h
    have a_image := le_intersect_j n1_le_a j
    have a_image_spec := a_image.choose_spec
    simp only [a_image, ↓reduceDIte, n] at h
    generalize_proofs at h
    have : final (OrderDual.toDual t) < final a_image.choose := by
      exact (InitialSeg.lt_iff_lt final).mpr h
    simp [a_image_spec, ←OrderDual.ofDual_lt_ofDual, Prod.Lex.lt_iff] at this
    set z := (ofLex <| OrderDual.ofDual <| final (OrderDual.toDual t))
    have : n < z.1 := by grind
    have exists_initial_t := le_intersect_j this z.2
    use z.1, z.2, this
    simp only [exists_initial_t, ↓reduceDIte, n]
    apply_fun final
    · simp [z]
    · exact EmbeddingLike.injective' final

  have : (afterN J (n+1))ᵒᵈ ≤i Tᵒᵈ := {
    toFun := afterN_map
    inj' := afterN_map_inj
    map_rel_iff' := afterN_map_rel_iff'
    mem_range_of_rel' := afterN_map_mem_range_of_rel'
  }

  exact domain_iso_initial this (afterN_iso J (n + 1) |>.dual)

/--
  If `A` is an interval isomorphic to `ℕ ×ₗ I`,
  `B` is an interval isomorphic to `ℕᵒᵈ ×ₗ J`,
  `A` extends `B` to the left, and `B` extends `A` to the right,
  then `ℕ ×ₗ I` convexly embeds in `J` and `ℕᵒᵈ ×ₗ J` convexly embeds in `I`.
-/
theorem crossing_embed {I J : Type u} [LinearOrder I] [LinearOrder J]
    {A B : Set α} (A_interval : A.OrdConnected) (B_interval : B.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B) (A_iso : A ≃o ℕ ×ₗ I)
    (B_iso : B ≃o ℕᵒᵈ ×ₗ J) : Nonempty (ℕ ×ₗ I ≤c J) ∧ Nonempty (ℕᵒᵈ ×ₗ J ≤c I)
    := by
  constructor
  · obtain ⟨T, _, final, convex, T_nonempty⟩ := final_seg_embeds_in_single
      A_interval B_interval extendsLeftRight A_iso B_iso
    simp only [←exists_true_iff_nonempty] at final convex
    obtain ⟨final⟩ := final
    obtain ⟨convex⟩ := convex
    have := final_in_omega_swap final
    exact Nonempty.intro (convex.comp this.toUndualConvexEmbedding)
  · obtain ⟨T, _, init, convex, T_nonempty⟩ := initial_seg_embeds_in_single
      A_interval B_interval extendsLeftRight A_iso B_iso
    simp only [←exists_true_iff_nonempty] at init convex
    obtain ⟨init⟩ := init
    obtain ⟨convex⟩ := convex
    have := initial_in_omega_star_swap init
    exact Nonempty.intro (convex.comp this)
