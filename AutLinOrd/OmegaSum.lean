import Mathlib
import AutLinOrd.ConvexEmbedding
import AutLinOrd.ExtendsLeftRight

attribute [local irreducible] OrderDual
attribute [local irreducible] Lex

/--
  If `S` is an `OrdConnected` and `Nonempty` subset of `ℕ ×ₗ A`, then
  there exists an initial segment of `S` that convexly embeds in `A`.
-/
theorem lowerbound_subset_omega {A : Type u} [LinearOrder A] (S : Set (ℕ ×ₗ A))
    (s_nonempty : Nonempty S) (s_ordConnected : S.OrdConnected) :
    ∃(T : Type u) (_ : LinearOrder T),
    Nonempty (T ≤i S) ∧ Nonempty (T ≤c A) ∧ Nonempty T := by
  have a_elem : A := by
    simp at s_nonempty
    choose a b hab using s_nonempty
    exact b

  -- Find the minimal `n : ℕ` such that `n × A` intersects `S`
  let intersectsS (n : ℕ) := ∃s ∈ S, ∃a : A, toLex (n, a) = s
  have existsValidN : ∃n, intersectsS n := by
    simp only [nonempty_subtype, Lex.exists, Prod.exists] at s_nonempty
    obtain ⟨n, ⟨a, a_n_mem⟩⟩ := s_nonempty
    use n, toLex (n, a)
    simp [a_n_mem]
  open Classical in (
  have n_intersectsS := Nat.find_spec existsValidN
  have n_min_intersectsS (m : ℕ) := Nat.find_min' (m := m) existsValidN
  set n := Nat.find existsValidN)

  -- Let `T` be the intersection of `S` and `n × A`
  set nA := {x : ℕ ×ₗ A | (ofLex x).1 = n}

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
          simp [nA]
          obtain l_lt_m | ⟨l_eq_m, _⟩ := l_c_lt_m_b
          · order
          · order
    }
  -- `T` convexly embeds in `A`
  · constructor
    · refine exists_true_iff_nonempty.mp ?_
      use {
        toFun x := (ofLex x.val).2
        inj' := by
          simp only [Function.Injective, Subtype.forall, Lex.exists,
            EmbeddingLike.apply_eq_iff_eq, Prod.exists, Prod.mk.injEq,
            exists_eq_right, exists_and_right, exists_eq_right',
            Set.mem_inter_iff, Set.mem_setOf_eq, Lex.forall, ofLex_toLex,
            Prod.forall, Subtype.mk.injEq, and_imp, T, nA, n, intersectsS]
          grind
        map_rel_iff' := by
          simp [T, nA, n]
          simp only [Function.Embedding.coeFn_mk, Subtype.forall,
            Set.mem_inter_iff, Set.mem_setOf_eq, Lex.forall, Prod.forall,
            Subtype.mk_le_mk, Prod.Lex.le_iff, ofLex_toLex, and_imp, T, nA, n]
          grind
        imageOrdConnected := by
          simp only [Set.ordConnected_iff, Set.mem_range, Subtype.exists,
            Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop, Lex.exists,
            ofLex_toLex, Prod.exists, exists_eq_right, T, nA]
          simp only [Set.ordConnected_iff, Lex.forall, Prod.forall,
            nA, T, intersectsS, n] at s_ordConnected
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
    · simp only [nonempty_subtype, Set.mem_inter_iff, Lex.exists,
        Prod.exists, T, nA]
      simp only [Lex.exists, EmbeddingLike.apply_eq_iff_eq, Prod.exists,
        Prod.mk.injEq, exists_eq_right, exists_and_right, exists_eq_right',
        intersectsS, T, nA] at n_intersectsS
      obtain ⟨x, hx⟩ := n_intersectsS
      use n, x
      simp [hx, nA]

/--
  The final segment of `ℕ ×ₗ I` starting at `n`
  instead of `0` in the first coordinate.
-/
def afterN (I : Type*) [LinearOrder I] (n : ℕ) :=
  {x : ℕ ×ₗ I | n ≤ (ofLex x).1}
/--
  The initial segment of `ℕᵒᵈ ×ₗ J` starting at `n`
  instead of `0` in the first coordinate.
-/
def beforeN (J : Type*) [LinearOrder J] (n : ℕ) :=
  {x : ℕᵒᵈ ×ₗ J | (ofLex x).1 ≤ OrderDual.toDual n}

/--
  `beforeN J n` is an initial segment of `ℕᵒᵈ ×ₗ J`.
-/
def beforeN_initial (J : Type*) [LinearOrder J] (n : ℕ) :
    beforeN J n ≤i ℕᵒᵈ ×ₗ J where
  toFun x := x.val
  inj' := by simp
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Subtype.range_coe_subtype, Set.setOf_mem_eq, Lex.forall, Prod.forall,
      OrderDual.forall, Subtype.forall]
    intro a b h_mem c d lt
    simp only [Prod.Lex.lt_iff, ofLex_toLex, OrderDual.toDual_lt_toDual,
      EmbeddingLike.apply_eq_iff_eq] at lt
    simp only [beforeN, Set.mem_setOf_eq, ofLex_toLex,
      OrderDual.toDual_le_toDual] at h_mem ⊢
    obtain a_lt_c | c_eq_a | d_lt_b := lt
    <;> order

/--
  `before J n` is order isomorphic to `ℕᵒᵈ ×ₗ J`.
-/
def beforeN_iso (J : Type*) [LinearOrder J] (n : ℕ) :
    beforeN J n ≃o ℕᵒᵈ ×ₗ J where
  toFun x := toLex ((ofLex x.val).1 - OrderDual.toDual n, (ofLex x.val).2)
  invFun x := ⟨toLex ((ofLex x).1 + OrderDual.toDual n, (ofLex x).2),
    by simp [beforeN, ←OrderDual.ofDual_le_ofDual]⟩
  left_inv := by
    simp only [Function.LeftInverse, beforeN, Set.coe_setOf, Set.mem_setOf_eq,
      toDual_sub, OrderDual.toDual_ofDual, ofLex_toLex, ofDual_sub,
      OrderDual.ofDual_toDual, toDual_add, Subtype.forall, Subtype.mk.injEq,
      Lex.forall, EmbeddingLike.apply_eq_iff_eq, Prod.forall,
      Prod.mk.injEq, and_true, OrderDual.forall, OrderDual.toDual_le_toDual]
    intro a b n_le_a
    simp [←toDual_sub, ←toDual_add]
    omega
  right_inv := by simp [Function.RightInverse, Function.LeftInverse,
    ←toDual_sub, ←toDual_add]
  map_rel_iff' := by
    simp only [beforeN, Set.coe_setOf, Set.mem_setOf_eq, toDual_sub,
      OrderDual.toDual_ofDual, toDual_add, Equiv.coe_fn_mk, Prod.Lex.le_iff,
      ofLex_toLex, Subtype.forall, Lex.forall, Prod.forall, OrderDual.forall,
      OrderDual.toDual_le_toDual, Subtype.mk_le_mk, OrderDual.toDual_lt_toDual,
      EmbeddingLike.apply_eq_iff_eq]
    intro a b n_le_a c d n_le_c
    constructor
    · intro h
      obtain an_lt_cn | ⟨an_eq_cn, b_le_d⟩ := h
      · simp only [← toDual_sub, OrderDual.toDual_lt_toDual] at an_lt_cn
        omega
      · simp only [← toDual_sub, EmbeddingLike.apply_eq_iff_eq] at an_eq_cn
        grind
    · intro h
      simp only [← toDual_sub, OrderDual.toDual_lt_toDual,
        EmbeddingLike.apply_eq_iff_eq]
      obtain c_lt_a | ⟨a_eq_c, b_le_d⟩ := h
      <;> grind
