import Mathlib
import AutLinOrd.ConvexEmbedding

variable [LinearOrder α]

@[simp]
theorem toLex_fst (a : A) (b : B) : (toLex (a,b)).1 = a := rfl

@[simp]
theorem toLex_snd (a : A) (b : B) : (toLex (a,b)).2 = b := rfl

/--
  If `S` is an `OrdConnected` and `Nonempty` subset of `ℕ ×ₗ A`, then
  there exists an initial segment of `S` that convexly embeds in `A`.
-/
theorem lowerbound_subset_omega {A : Type u} [LinearOrder A] (S : Set (ℕ ×ₗ A))
    (s_nonempty : Nonempty S) (s_ordConnected : S.OrdConnected) :
    ∃(T : Type u) (_ : LinearOrder T),
    Nonempty (T ≤i S) ∧ Nonempty (T ≤c A) := by
  -- Find the minimal `n : ℕ` such that `n × A` intersects `S`
  let intersectsS (n : ℕ) := ∃s ∈ S, ∃a : A, toLex (n, a) = s
  have existsValidN : ∃n, intersectsS n := by
    simp only [nonempty_subtype, Lex.exists, Prod.exists] at s_nonempty
    obtain ⟨n, ⟨a, a_n_mem⟩⟩ := s_nonempty
    use n, toLex (n, a)
    simp [a_n_mem]
  open Classical in
  have n_intersectsS := Nat.find_spec existsValidN
  have n_min_intersectsS (m : ℕ) := Nat.find_min' (m := m) existsValidN
  set n := Nat.find existsValidN

  -- Let `T` be the intersection of `S` and `n × A`
  set nA := {x : ℕ ×ₗ A | x.1 = n}
  set T := S ∩ nA
  use T, inferInstance
  constructor

  -- `T` is an `InitialSeg` of `S`
  · refine exists_true_iff_nonempty.mp ?_
    use {
      toFun x := ⟨x.val, x.prop.1⟩
      inj' := by simp [Function.Injective]
      map_rel_iff' := by simp
      mem_range_of_rel' := by
        simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
          Set.mem_range, Subtype.exists, Lex.exists, Prod.exists,
          Subtype.forall, Subtype.mk_lt_mk, Subtype.mk.injEq, exists_prop,
          Lex.forall, EmbeddingLike.apply_eq_iff_eq, Prod.forall,
          Prod.mk.injEq, exists_eq_right_right, exists_eq_right]
        intro m b m_b_mem_T l c l_c_mem_S l_c_lt_m_b
        simp only [exists_and_left, Set.mem_setOf_eq,
          EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, exists_eq',
          and_true, T]
        constructor
        · exact l_c_mem_S
        · have l_intersectsS : intersectsS l := by
            simp only [Lex.exists, EmbeddingLike.apply_eq_iff_eq,
              Prod.exists, Prod.mk.injEq, exists_eq_right, exists_and_right,
              exists_eq_right', intersectsS, T]
            use c
          have := n_min_intersectsS l l_intersectsS
          have m_eq_n : m = n := by
            have := m_b_mem_T.2
            simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
              intersectsS, T] at this
            exact this
          simp only [Prod.Lex.lt_iff, ofLex_toLex, intersectsS, T] at l_c_lt_m_b
          simp only [Set.mem_setOf_eq, toLex_fst, nA, intersectsS, T, n]
          obtain l_lt_m | ⟨l_eq_m, _⟩ := l_c_lt_m_b
          · order
          · order
    }
  -- `T` convexly embeds in `A`
  · refine exists_true_iff_nonempty.mp ?_
    use {
      toFun x := x.val.2
      inj' := by
        simp only [Function.Injective, Subtype.forall, Set.mem_inter_iff,
          Set.mem_setOf_eq, Lex.forall, Prod.forall, toLex_fst, toLex_snd,
          Subtype.mk.injEq, and_imp, EmbeddingLike.apply_eq_iff_eq,
          Prod.mk.injEq, T, nA, n, intersectsS]
        grind
      map_rel_iff' := by
        simp only [Function.Embedding.coeFn_mk, Subtype.forall,
          Set.mem_inter_iff, Set.mem_setOf_eq, Lex.forall, Prod.forall,
          toLex_fst, toLex_snd, Subtype.mk_le_mk, Prod.Lex.le_iff,
          ofLex_toLex, and_imp, T, nA, n]
        grind
      imageOrdConnected := by
        simp only [Set.ordConnected_iff, Set.mem_range, Subtype.exists,
          Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop, Lex.exists,
          Prod.exists, toLex_fst, toLex_snd, exists_eq_right, T, nA]
        simp only [Set.ordConnected_iff, Lex.forall, Prod.forall,
          T] at s_ordConnected
        intro a n_a_mem_S b n_b_mem_S a_le_b
        intro c c_mem_set
        simp only [Set.mem_Icc, nA, T] at c_mem_set
        have na_le_nc : toLex (n, a) ≤ toLex (n, c) := by
          simp [Prod.Lex.le_iff, c_mem_set.1]
        have nc_le_nb : toLex (n, c) ≤ toLex (n, b) := by
          simp [Prod.Lex.le_iff, c_mem_set.2]
        specialize s_ordConnected n a n_a_mem_S n b n_b_mem_S (by order)
        have : toLex (n, c) ∈ Set.Icc (toLex (n,a)) (toLex (n,b)) := by
          simp [T, na_le_nc, nc_le_nb]
        have nc_mem_S := s_ordConnected this
        simp [Set.range, nc_mem_S]
    }

variable {A B : Set α}

/--
  `ExtendsLeft A B` means that `A` has an element in it
  less than or equal to all of `B`.
-/
def ExtendsLeft (A B : Set α) := ∃l, l ∈ A ∧ ∀b ∈ B, l ≤ b
/--
  `ExtendsRight A B` means that `A` has an element in it
  greater than or equal to all of `B`.
-/
def ExtendsRight (A B : Set α) := ∃u, u ∈ A ∧ ∀b ∈ B, b ≤ u

/--
  `ExtendsLeftRight A B` means that `A` and `B` intersect,
  `A` has an element less than or equal to all of `B`,
  and `B` has an element greater than or equal to all of `A`.
-/
def ExtendsLeftRight (A B : Set α) :=
  (∃x, x ∈ A ∧ x ∈ B) ∧ ExtendsLeft A B ∧ ExtendsRight B A

/--
  If `a` is in both `A` and `B`, `z` is in `B`, and `z ≤ a`,
  then `z ∈ A`.
-/
theorem mem_le_inter_mem (A_interval : A.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B)
    (a_mem_A : a ∈ A) (a_mem_B : a ∈ B) (z_mem_B : z ∈ B) (z_le_a : z ≤ a) :
    z ∈ A := by
  simp only [Set.ordConnected_iff] at A_interval
  obtain ⟨l, l_mem_A, hl⟩ := extendsLeftRight.2.1
  apply A_interval l l_mem_A a a_mem_A (hl a a_mem_B)
  exact ⟨hl z z_mem_B, z_le_a⟩

/--
  If `a` is in both `A` and `B`, `z` is in `A`, and `a ≤ z`,
  then `z ∈ B`.
-/
theorem mem_ge_inter_mem (B_interval : B.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B)
    (a_mem_A : a ∈ A) (a_mem_B : a ∈ B) (z_mem_A : z ∈ A) (a_le_z : a ≤ z) :
    z ∈ B := by
  simp only [Set.ordConnected_iff] at B_interval
  obtain ⟨u, u_mem_B, hl⟩ := extendsLeftRight.2.2
  apply B_interval a a_mem_B u u_mem_B (hl a a_mem_A)
  exact ⟨a_le_z, hl z z_mem_A⟩

/--
  If `ExtendsLeftRight A B`, then `A ∩ B` is an initial segment of `B`.
-/
def intersect_extendsLeftRight_initial
    (A_interval : A.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B) : (A ∩ B : Set α) ≤i B where
  toFun x := ⟨x.val, x.prop.2⟩
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Set.inter_subset_right, Set.range_inclusion, Set.mem_inter_iff,
      Subtype.coe_prop, and_true, Set.mem_setOf_eq, Subtype.forall,
      Subtype.mk_lt_mk, and_imp]
    intro a a_mem_A a_mem_B z z_mem_A z_lt_a
    exact mem_le_inter_mem A_interval extendsLeftRight a_mem_A
      a_mem_B z_mem_A z_lt_a.le

/--
  If `ExtendsLeftRight A B`, then `A ∩ B` is a final segment of `A`.
-/
def intersect_extendsLeftRight_final
    (B_interval : B.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B) : (A ∩ B : Set α)ᵒᵈ ≤i Aᵒᵈ where
  toFun x := OrderDual.toDual
    ⟨(OrderDual.ofDual x).val, (OrderDual.ofDual x).prop.1⟩
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.mem_range,
      OrderDual.exists, OrderDual.ofDual_toDual, Subtype.exists,
      Set.mem_inter_iff, OrderDual.forall, OrderDual.toDual_lt_toDual,
      EmbeddingLike.apply_eq_iff_eq, Subtype.forall, Subtype.mk_lt_mk,
      Subtype.mk.injEq, exists_prop, exists_eq_right, and_imp]
    intro a a_mem_A a_mem_B z z_mem_A a_lt_z
    constructor
    · exact z_mem_A
    · exact mem_ge_inter_mem B_interval extendsLeftRight a_mem_A
        a_mem_B z_mem_A a_lt_z.le

theorem initial_seg_embeds_in_single {y l u} {I J : Type u} [LinearOrder I]
    [LinearOrder J] {A B : Set α} (A_interval : A.OrdConnected)
    (B_interval : B.OrdConnected) (y_mem_a : y ∈ A) (y_mem_b : y ∈ B)
    (l_mem_a : l ∈ A) (l_lowerbound : ∀b ∈ B, l < b)
    (u_mem_b : u ∈ B) (u_upperbound : ∀a ∈ A, a < u)
    (A_iso : A ≃o ℕ ×ₗ I) (B_iso : B ≃o ℕᵒᵈ ×ₗ J) :
    ∃(T : Type u) (_ : LinearOrder T),
    Nonempty (T ≤i ℕᵒᵈ ×ₗ J) ∧ Nonempty (T ≤c I) := by sorry

theorem initial_in_omega_star_swap [LinearOrder T] [LinearOrder J]
  (h : T ≤i ℕᵒᵈ ×ₗ J) : Nonempty (ℕᵒᵈ ×ₗ J ≤i T) := by sorry

theorem crossing_embed {y l u} {I J : Type u} [LinearOrder I] [LinearOrder J]
    {A B : Set α} (A_interval : A.OrdConnected) (B_interval : B.OrdConnected)
    (y_mem_a : y ∈ A) (y_mem_b : y ∈ B) (l_mem_a : l ∈ A)
    (l_lowerbound : ∀b ∈ B, l < b) (u_mem_b : u ∈ B)
    (u_upperbound : ∀a ∈ A, a < u) (A_iso : A ≃o ℕ ×ₗ I)
    (B_iso : B ≃o ℕᵒᵈ ×ₗ J) : Nonempty (ℕ ×ₗ I ≤c J) ∧ Nonempty (ℕᵒᵈ ×ₗ J ≤c I)
    := by
  constructor
  · sorry
  · obtain ⟨T, _, ⟨init, convex⟩⟩ := initial_seg_embeds_in_single
      A_interval B_interval y_mem_a y_mem_b l_mem_a l_lowerbound u_mem_b
      u_upperbound A_iso B_iso
    simp only [←exists_true_iff_nonempty] at init convex
    obtain ⟨init⟩ := init
    obtain ⟨convex⟩ := convex
    have := initial_in_omega_star_swap init
    obtain ⟨initial⟩ := Classical.exists_true_of_nonempty this
    have := initial_emb_convex_emb initial
    exact Nonempty.intro (convex.comp this)
