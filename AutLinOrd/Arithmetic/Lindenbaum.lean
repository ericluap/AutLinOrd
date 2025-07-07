import Mathlib
import AutLinOrd.Embeddings.ConvexEmbedding
import AutLinOrd.Embeddings.InitialSeg
import AutLinOrd.Embeddings.Embeddings

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
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.ordConnected_iff,
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

theorem pow_plus_one_left_increasing (a : A) (n : ℕ) :
    (axb_emb x_eq_axb ^ n) (Sum.inlₗ a) <
    (axb_emb x_eq_axb ^ (n + 1)) (Sum.inlₗ a) := by simp [pow_add]

theorem pow_left_increasing (a : A) (n : ℕ) :
    Sum.inlₗ a < (axb_emb x_eq_axb ^ (n+1)) (Sum.inlₗ a) := by
  induction n with
  | zero => simp
  | succ m ih => exact ih.trans (by simp [pow_add])

theorem left_lt_pow_image (a a' : A) (n : ℕ) :
    Sum.inlₗ a < (axb_emb x_eq_axb ^ (n+1)) (Sum.inlₗ a') := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact ih.trans (pow_plus_one_left_increasing x_eq_axb a' (n+1))

theorem pow_image_lt_right (a a' : A) (n : ℕ) :
    Sum.inlₗ a < (axb_emb x_eq_axb ^ (n+1)) (Sum.inlₗ a') := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact ih.trans (pow_plus_one_left_increasing x_eq_axb a' (n+1))

theorem pow_left_lt_pow_add_left (n k : ℕ) (a a' : A) :
    (axb_emb x_eq_axb ^ n) (Sum.inlₗ a) <
    (axb_emb x_eq_axb ^ (n + (k+1))) (Sum.inlₗ a') := by
  induction k with
  | zero => simp [pow_add]
  | succ k ih => simp [pow_add _ n, left_lt_pow_image]

theorem pow_lt_left_lt (n_lt_m : n < m) (a a' : A) :
    (axb_emb x_eq_axb ^ n) (Sum.inlₗ a) <
    (axb_emb x_eq_axb ^ m) (Sum.inlₗ a') := by
  obtain ⟨k, hk⟩ := Nat.le.dest n_lt_m.le
  have := pow_left_lt_pow_add_left x_eq_axb n (k-1) a a'
  have eq_k : k - 1 + 1 = k := by omega
  simp only [eq_k, hk] at this
  exact this

/--
  For any `a` in `A` and `b` in `B` of `A + X + B`,
  `axb_emb^n a` is less than `b`
-/
theorem pow_left_lt_right (n : ℕ) (a : A) (b : B) :
    (axb_emb x_eq_axb ^ n) (Sum.inlₗ a) < Sum.inrₗ (Sum.inrₗ b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [add_comm n, pow_add]

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
  Every element of `X` in `A + X + B` lies in the image
  of `axb_emb`
-/
theorem mem_range_x (x : X) :
    Sum.inrₗ (Sum.inlₗ x) ∈ Set.range (axb_emb x_eq_axb) := by
  simp [axb_emb_range_x x_eq_axb]

/--
  If `z` lies in the interval `[a, axb_emb a]`,
  then `z` is in the image of some power of `axb_emb`
-/
theorem interval_a_mapa_mem_pow_image (a : A) (a_le_z : Sum.inlₗ a ≤ z)
    (z_lt_mapa : z < (axb_emb x_eq_axb (Sum.inlₗ a))) :
    ∃n' a', (axb_emb x_eq_axb ^ n') (Sum.inlₗ a') = z := by
  axb_cases z
  · use 0, z
    simp
  · simp only [axb_emb_apply, gt_iff_lt, Sum.Lex.toLex_lt_toLex, Sum.lex_inr_inr,
    Sum.lex_inl_inl] at z_lt_mapa
    have := mem_range_x x_eq_axb z
    simp only [Set.mem_range, axb_emb_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq,
      Sum.inl.injEq, Lex.exists, Sum.exists] at this
    obtain ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩ := this
    · use 1, y
      simp [hy]
    · simp [←hy] at z_lt_mapa
    · simp [←hy] at z_lt_mapa
  · simp at z_lt_mapa

/--
  If `z` lies in the interval `[axb_emb^n a, axb_emb^(n+1) a]`,
  then `z` is in the image of some power of `axb_emb`
-/
theorem pow_interval_a_mapa_mem_pow_image
    (a_le_z : (axb_emb x_eq_axb ^ n) (Sum.inlₗ a) ≤ z)
    (z_lt_mapa : z < (axb_emb x_eq_axb ^ (n+1)) (Sum.inlₗ a)) :
    ∃n' a', (axb_emb x_eq_axb ^ n') (Sum.inlₗ a') = z := by
  induction n generalizing z with
  | zero =>
    simp only [pow_zero, ConvexEmbedding.coe_one, id_eq, ge_iff_le, zero_add, pow_one,
      axb_emb_apply, gt_iff_lt] at a_le_z z_lt_mapa
    exact interval_a_mapa_mem_pow_image x_eq_axb a a_le_z z_lt_mapa
  | succ n ih =>
    simp only [ge_iff_le, gt_iff_lt] at a_le_z z_lt_mapa
    set prev_interval := Set.Ico
      ((axb_emb x_eq_axb ^ n) (Sum.inlₗ a))
      ((axb_emb x_eq_axb ^ (n+1)) (Sum.inlₗ a))
    set next_interval := Set.Ico
      ((axb_emb x_eq_axb ^ (n+1)) (Sum.inlₗ a))
      ((axb_emb x_eq_axb ^ (n+1+1)) (Sum.inlₗ a))
    have z_mem_next : z ∈ next_interval := by
      simp [next_interval, a_le_z, z_lt_mapa]
    have : axb_emb x_eq_axb '' prev_interval = next_interval := by
      simp only [prev_interval, ConvexEmbedding.image_Ico]
      conv =>
        enter [1, 1]
        rw [ConvexEmbedding.add_pows_one _ n, add_comm]
      conv =>
        enter [1, 2]
        rw [ConvexEmbedding.add_pows_one _ n, add_comm]
    simp only [← this, Set.mem_image] at z_mem_next
    obtain ⟨y, y_mem_prev, y_map_z⟩ := z_mem_next
    simp only [Set.mem_Ico, prev_interval, next_interval] at y_mem_prev
    obtain ⟨n', a', h⟩ := ih y_mem_prev.1 y_mem_prev.2
    use 1+n', a'
    simp [-axb_emb_apply, pow_add, h, y_map_z]

/--
  Define a map from `ℕA` to `A + X + B`
-/
def omegaA_axb_map (na : ℕ ×ₗ A) : A ⊕ₗ X ⊕ₗ B :=
  (axb_emb x_eq_axb ^ (ofLex na).1) (Sum.inlₗ (ofLex na).2)

/--
  The map from `ℕA` to `A + X + B` is injective
-/
theorem omegaA_axb_map_inj : Function.Injective (omegaA_axb_map x_eq_axb) := by
  simp only [Function.Injective, Lex.forall, ofLex_toLex, Prod.forall,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, omegaA_axb_map]
  intro n a n' a' eq
  obtain n_lt_n' | n_eq_n' | n'_lt_n := lt_trichotomy n n'
  · have := pow_lt_left_lt x_eq_axb n_lt_n' a a'
    order
  · simpa [n_eq_n'] using eq
  · have := pow_lt_left_lt x_eq_axb n'_lt_n a' a
    order

/--
  The map from `ℕA` to `A + X + B` preserves the ordering
-/
theorem omegaA_axb_map_rel_iff : ∀ {a b : ℕ ×ₗ A},
    omegaA_axb_map x_eq_axb a < omegaA_axb_map x_eq_axb b ↔ a < b := by
  simp only [omegaA_axb_map, gt_iff_lt, Prod.Lex.lt_iff, Lex.forall, ofLex_toLex, Prod.forall]
  intro n a n' a'
  constructor
  · intro lt
    obtain n_lt_n' | n_eq_n' | n'_lt_n := lt_trichotomy n n'
    · simp [n_lt_n']
    · simpa [n_eq_n'] using lt
    · have := pow_lt_left_lt x_eq_axb n'_lt_n a' a
      order
  · intro lt
    obtain n_lt_n' | ⟨n_eq_n', a_lt_a'⟩ := lt
    · exact pow_lt_left_lt x_eq_axb n_lt_n' a a'
    · simp [n_eq_n', a_lt_a']

/--
  If `x` is less than some element of in the image of the map
  from from `ℕA` to `A + X + B`, then `x` is in the image of the map.
-/
theorem omegaA_axb_mem_range_of_rel : ∀ a : ℕ ×ₗ A,
    ∀ b < omegaA_axb_map x_eq_axb a, b ∈ Set.range (omegaA_axb_map x_eq_axb) := by
  simp only [omegaA_axb_map, gt_iff_lt, Set.mem_range, Lex.exists, ofLex_toLex, Prod.exists,
    Lex.forall, Sum.forall, Prod.forall]
  intro n a
  constructor
  · intro a' lt
    use 0, a'
    simp
  · constructor
    · intro x lt
      induction n with
      | zero => simp at lt
      | succ n ih =>
        by_cases h : toLex (Sum.inr (toLex (Sum.inl x))) <
          (axb_emb x_eq_axb ^ n) (Sum.inlₗ a)
        · exact ih h
        · simp only [not_lt] at h
          exact pow_interval_a_mapa_mem_pow_image x_eq_axb h lt
    · intro b lt
      have := pow_left_lt_right x_eq_axb n a b
      order

/--
  `ℕA` is an initial segment of `A + X + B`
-/
def omegaA_initial_axb : ℕ ×ₗ A ≤i A ⊕ₗ X ⊕ₗ B where
  toFun := omegaA_axb_map x_eq_axb
  inj' := omegaA_axb_map_inj x_eq_axb
  map_rel_iff' := omegaA_axb_map_rel_iff x_eq_axb
  mem_range_of_rel' := omegaA_axb_mem_range_of_rel x_eq_axb

/--
  `ℕA` is an initial segment of `X`
-/
def omegaA_initial_x : ℕ ×ₗ A ≤i X :=
  (omegaA_initial_axb x_eq_axb).trans x_eq_axb.symm.toInitialSeg
