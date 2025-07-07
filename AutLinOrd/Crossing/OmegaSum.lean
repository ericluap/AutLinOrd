import AutLinOrd.Embeddings.InitialSeg
import AutLinOrd.Crossing.ExtendsLeftRight
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Data.Nat.Find
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Nat.Cast.Synonym

/-!
  This file proves facts about linear orders of the form `ℕ ×ₗ A` and `ℕᵒᵈ ×ₗ A`.

  It shows that if `S` is a subset of `ℕ ×ₗ A`, then there exists a `T` such that
  `T` is initial in `S` and `T` convexly embeds in `A` (and the dual statement).

  It also shows that for any `n : ℕ`, `ℕ≥n ×ₗ A` is isomorphic to `ℕ ×ₗ A`
  (and the dual statement).
-/

seal OrderDual
seal Lex

/--
  For a given `A : A`, it is `a ×ₗ B` (which is a subset of `A ×ₗ B`).
-/
def fixed_first_coord (B : Type*) [LinearOrder A] [LinearOrder B] (a : A) :=
  {x : A ×ₗ B | (ofLex x).1 = a}

/--
  `a ×ₗ B` is `OrdConnected`.
-/
theorem fixed_first_coord_ordConnected [LinearOrder A] [LinearOrder B]
    (a : A) : (fixed_first_coord B a).OrdConnected := by
  simp [Set.ordConnected_iff, fixed_first_coord, Prod.Lex.le_iff]
  intro m c m_eq_n j b j_eq_n m_comp_j x x_mem_icc
  subst_vars
  simp [Prod.Lex.le_iff] at x_mem_icc ⊢ m_comp_j
  obtain ⟨h1a | h1b, h2a | h2b⟩ := x_mem_icc
  · order
  all_goals grind

/--
  `a ×ₗ B` is order isomorphic to `B`.
-/
def fixed_first_coord_iso [LinearOrder A] [LinearOrder B]
    (a : A) : (fixed_first_coord B a) ≃o B where
  toFun x := (ofLex x.val).2
  invFun x := ⟨toLex (a, x), by simp [fixed_first_coord]⟩
  left_inv := by simp [Function.LeftInverse, fixed_first_coord]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by
    simp only [fixed_first_coord, Set.coe_setOf, Set.mem_setOf_eq, Equiv.coe_fn_mk, Subtype.forall,
      Lex.forall, ofLex_toLex, Prod.forall, Subtype.mk_le_mk, Prod.Lex.le_iff]
    intro b c b_eq_c d e d_eq_a
    subst_vars
    simp

/--
  If `S` is an `OrdConnected` and `Nonempty` subset of `ℕ ×ₗ A`, then
  there exists an initial segment of `S` that convexly embeds in `A`.
-/
theorem lowerbound_subset_omega {A : Type u} [LinearOrder A] (S : Set (ℕ ×ₗ A))
    (s_nonempty : Nonempty S) (s_ordConnected : S.OrdConnected) :
    ∃(T : Type u) (_ : LinearOrder T),
    Nonempty (T ≤i S) ∧ Nonempty (T ≤c A) ∧ Nonempty T := by
  -- Find the minimal `n : ℕ` such that `n ×ₗ A` intersects `S`
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

  -- `n ×ₗ A` extends `S` to the left and is `OrdConnected`.
  set nA := fixed_first_coord A n

  have na_extendsLeft_S : ExtendsLeft nA S := by
    simp only [ExtendsLeft, fixed_first_coord, Set.mem_setOf_eq, Prod.Lex.le_iff, Lex.exists,
      ofLex_toLex, Prod.exists, exists_and_left, exists_eq_left, Lex.forall, Prod.forall, Intersect,
      nA]
    simp only [Lex.exists, EmbeddingLike.apply_eq_iff_eq, Prod.exists, Prod.mk.injEq,
      exists_eq_right, exists_and_right, exists_eq_right', intersectsS, nA] at n_intersectsS
    obtain ⟨x, hx⟩ := n_intersectsS
    have nx_mem_nA : toLex (n, x) ∈ nA := by simp [nA, fixed_first_coord]
    constructor
    · intro m a ma_mem_S
      use a
      have := n_min_intersectsS m (by grind)
      simp  [le_refl, and_true, this.lt_or_eq]
    · grind

  have nA_ordConnected : nA.OrdConnected := fixed_first_coord_ordConnected n

  set T := nA ∩ S
  use T, inferInstance
  constructor

  -- `T` is an `InitialSeg` of `S`
  · have : T ≤i S :=
      extendsLeft_intersect_initial nA S nA_ordConnected na_extendsLeft_S
    exact Nonempty.intro this
  · constructor
    -- `T` convexly embeds in `A`
    · have t_convex_na : T ≤c nA := intersect_convex_first nA S s_ordConnected
      have na_iso_a : nA ≃o A := fixed_first_coord_iso n
      have : T ≤c A := na_iso_a.toInitialSeg.toConvexEmbedding.comp t_convex_na
      exact Nonempty.intro this
    -- `T` is nonempty
    · simp only [fixed_first_coord, nonempty_subtype, Set.mem_inter_iff, Set.mem_setOf_eq,
      Lex.exists, ofLex_toLex, Prod.exists, exists_and_left, exists_eq_left, T, nA, n]
      simp only [Lex.exists, EmbeddingLike.apply_eq_iff_eq, Prod.exists,
        Prod.mk.injEq, exists_eq_right, exists_and_right, exists_eq_right',
        intersectsS, T, nA] at n_intersectsS
      obtain ⟨x, hx⟩ := n_intersectsS
      use x

/--
  If `S` is an `OrdConnected` and `Nonempty` subset of `ℕᵒᵈ ×ₗ A`, then
  there exists an final segment of `S` that convexly embeds in `A`.
-/
theorem upperbound_subset_omega_dual {A : Type u} [LinearOrder A] (S : Set (ℕᵒᵈ ×ₗ A))
    (s_nonempty : Nonempty S) (s_ordConnected : S.OrdConnected) :
    ∃(T : Type u) (_ : LinearOrder T),
    Nonempty (Tᵒᵈ ≤i Sᵒᵈ) ∧ Nonempty (T ≤c A) ∧ Nonempty T := by
  -- Find the minimal `n : ℕ` such that `n ×ₗ A` intersects `S`
  let intersectsS (n : ℕ) := ∃s ∈ S, ∃a : A, toLex (OrderDual.toDual n, a) = s
  have existsValidN : ∃n, intersectsS n := by
    simp only [nonempty_subtype, Lex.exists, Prod.exists] at s_nonempty
    obtain ⟨n, ⟨a, a_n_mem⟩⟩ := s_nonempty
    use OrderDual.ofDual n, toLex (n, a)
    simp only [a_n_mem, ofDual_natCast, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
      exists_eq_right, true_and]
    rfl
  open Classical in (
  have n_intersectsS := Nat.find_spec existsValidN
  have n_min_intersectsS (m : ℕ) := Nat.find_min' (m := m) existsValidN
  set n := Nat.find existsValidN)

  -- `n ×ₗ A` extends `S` to the left and is `OrdConnected`.
  set nA := fixed_first_coord A (OrderDual.toDual n)

  have na_extendsRight_S : ExtendsRight nA S := by
    simp only [ExtendsRight, fixed_first_coord, Set.mem_setOf_eq, Prod.Lex.le_iff, Lex.exists,
      ofLex_toLex, Prod.exists, exists_and_left, exists_eq_left, Lex.forall, Prod.forall,
      OrderDual.forall, OrderDual.toDual_lt_toDual, EmbeddingLike.apply_eq_iff_eq, Intersect, nA]
    simp only [Lex.exists, EmbeddingLike.apply_eq_iff_eq, Prod.exists, Prod.mk.injEq,
      exists_eq_right, exists_and_right, exists_eq_right', intersectsS, nA] at n_intersectsS
    obtain ⟨x, hx⟩ := n_intersectsS
    have nx_mem_nA : toLex (OrderDual.toDual n, x) ∈ nA := by
      simp [nA, fixed_first_coord]
    constructor
    · intro m a ma_mem_S
      use a
      have := n_min_intersectsS m (by grind)
      conv => enter [2, 1]; rw [Eq.comm]
      simp [this.lt_or_eq]
    · grind

  have nA_ordConnected : nA.OrdConnected :=
    fixed_first_coord_ordConnected (OrderDual.toDual n)

  set T := S ∩ nA
  use T, inferInstance
  constructor

  -- `T` is an `InitialSeg` of `S`
  · have : Tᵒᵈ ≤i Sᵒᵈ :=
      extendsRight_intersect_final S nA nA_ordConnected na_extendsRight_S
    exact Nonempty.intro this
  · constructor
    -- `T` convexly embeds in `A`
    · have t_convex_na : T ≤c nA := intersect_convex_second S nA s_ordConnected
      have na_iso_a : nA ≃o A := fixed_first_coord_iso (OrderDual.toDual n)
      have : T ≤c A := na_iso_a.toInitialSeg.toConvexEmbedding.comp t_convex_na
      exact Nonempty.intro this
    -- `T` is nonempty
    · simp only [fixed_first_coord, nonempty_subtype, Set.mem_inter_iff, Set.mem_setOf_eq,
      Lex.exists, ofLex_toLex, Prod.exists, exists_and_right, exists_eq_right, T, nA]
      simp only [Lex.exists, EmbeddingLike.apply_eq_iff_eq, Prod.exists,
        Prod.mk.injEq, exists_eq_right, exists_and_right, exists_eq_right',
        intersectsS, T, nA] at n_intersectsS
      obtain ⟨x, hx⟩ := n_intersectsS
      use x

/--
  The final segment of `ℕ ×ₗ I` starting at `n`
  instead of `0` in the first coordinate.
-/
def afterN (I : Type*) [LinearOrder I] (n : ℕ) :=
  {x : ℕ ×ₗ I | n ≤ (ofLex x).1}

/--
  `afterN I n` is order isomorphic to `ℕ ×ₗ I`.
-/
def afterN_iso (I : Type*) [LinearOrder I] (n : ℕ) :
    afterN I n ≃o ℕ ×ₗ I where
  toFun x := toLex ((ofLex x.val).1 - n, (ofLex x.val).2)
  invFun x := ⟨toLex ((ofLex x).1 + n, (ofLex x).2), by simp [afterN]⟩
  left_inv := by simp (disch := omega) [Function.LeftInverse, afterN]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by
    simp only [afterN, Set.coe_setOf, Set.mem_setOf_eq, Equiv.coe_fn_mk, Prod.Lex.le_iff,
      ofLex_toLex, Subtype.forall, Lex.forall, Prod.forall, Subtype.mk_le_mk]
    grind

/--
  The initial segment of `ℕᵒᵈ ×ₗ J` starting at `n`
  instead of `0` in the first coordinate.
-/
def beforeN (J : Type*) [LinearOrder J] (n : ℕ) :=
  {x : ℕᵒᵈ ×ₗ J | (ofLex x).1 ≤ OrderDual.toDual n}

/--
  `before J n` is order isomorphic to `ℕᵒᵈ ×ₗ J`.
-/
def beforeN_iso (J : Type*) [LinearOrder J] (n : ℕ) :
    beforeN J n ≃o ℕᵒᵈ ×ₗ J where
  toFun x := toLex ((ofLex x.val).1 - OrderDual.toDual n, (ofLex x.val).2)
  invFun x := ⟨toLex ((ofLex x).1 + OrderDual.toDual n, (ofLex x).2),
    by simp [beforeN, ←OrderDual.ofDual_le_ofDual]⟩
  left_inv := by
    simp only [Function.LeftInverse, beforeN, Set.coe_setOf, Set.mem_setOf_eq, ofLex_toLex,
      Subtype.forall, Subtype.mk.injEq, Lex.forall, EmbeddingLike.apply_eq_iff_eq, Prod.forall,
      Prod.mk.injEq, and_true, OrderDual.forall, OrderDual.toDual_le_toDual, ← toDual_sub, ←
      toDual_add]
    omega
  right_inv := by simp [Function.RightInverse, Function.LeftInverse,
    ←toDual_sub, ←toDual_add]
  map_rel_iff' := by
    simp only [beforeN, Set.coe_setOf, Set.mem_setOf_eq, Equiv.coe_fn_mk, Prod.Lex.le_iff,
      ofLex_toLex, Subtype.forall, Lex.forall, Prod.forall, OrderDual.forall,
      OrderDual.toDual_le_toDual, ← toDual_sub, Subtype.mk_le_mk, OrderDual.toDual_lt_toDual,
      EmbeddingLike.apply_eq_iff_eq]
    grind
