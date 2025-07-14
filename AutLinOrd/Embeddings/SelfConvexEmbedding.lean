import AutLinOrd.Embeddings.InitialSeg
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Tactic.Order
import AutLinOrd.CalcOrderIso
import AutLinOrd.Arithmetic.Sum

/-!
  This file proves facts about convex embeddings from a linear order to itself.
  In particular, it shows that if `f` if a convex embedding from `α` to itself,
  then `α` is isomorphic to `ℕ(f.lt_image) + f.center + ℕᵒᵈ(f.gt_image)`
-/

seal OrderDual
seal Lex

namespace ConvexEmbedding
variable [LinearOrder α] (f : α ≤c α)

theorem add_pows_one (n : ℕ) :
    f ((f ^ n) x) = (f ^ (1 + n)) x := by
  conv =>
    enter [1, 1]
    rw [show f = f^1 by simp]
  simp only [←Function.comp_apply (f := f^(1 : ℕ))]
  simp only [←coe_mul, ←pow_add]

/--
  The set of points in `α` that are less than every element
  in the image of `f`
-/
def lt_image : Set α := {x | ∀y ∈ Set.range f, x < y}

/--
  The set of points in `α` that are greater than every element
  in the image of `f`
-/
def gt_image : Set α := {x | ∀y ∈ Set.range f, y < x}

/--
  `f.lt_image` is an initial segment of `α`
-/
def ltImage_initial : f.lt_image ≤i α where
  toFun x := x
  inj' := by simp
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [lt_image, Set.coe_setOf, Set.mem_setOf_eq, RelEmbedding.coe_mk,
      Function.Embedding.coeFn_mk, Subtype.range_coe_subtype, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Subtype.forall]
    intro _ a_lt_image _ _ c
    have := a_lt_image c
    order

/--
  `f.gt_image` is a final segment of `α`
-/
def gtImage_final : f.gt_imageᵒᵈ ≤i αᵒᵈ where
  toFun x := OrderDual.toDual (OrderDual.ofDual x).val
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp [gt_image]
    intro _ a_gt_image _ _ c
    have := a_gt_image c
    order

theorem ltImage_lt_pow (a a' : f.lt_image) (n : ℕ) : a < (f ^ (n+1)) a' := by
  simp [add_comm n, pow_add, a.prop.out]

theorem gtImage_gt_pow (a a' : f.gt_image) (n : ℕ) : (f ^ (n+1)) a' < a := by
  simp [add_comm n, pow_add, a.prop.out]

theorem ltImage_lt_pow_add (n k : ℕ) (a a' : f.lt_image) :
  (f ^ n) a < (f ^ (n + (k+1))) a' := by simp [add_comm k, pow_add, a.prop.out]

theorem gtImage_gt_pow_add (n k : ℕ) (a a' : f.gt_image) :
  (f ^ (n + (k+1))) a' < (f ^ n) a := by simp [add_comm k, pow_add, a.prop.out]

/--
  `f` is increasing on `f.lt_image`
-/
theorem ltImage_lt_pow_lt (n_lt_m : n < m) (a a' : f.lt_image) :
    (f ^ n) a < (f ^ m) a' := by
  obtain ⟨k, hk⟩ := Nat.le.dest n_lt_m.le
  have := ltImage_lt_pow_add f n (k-1) a a'
  simpa (disch := omega) [hk]

/--
  `f` is decreaisng on `f.gt_image`
-/
theorem gtImage_lt_pow_gt (n_lt_m : n < m) (a a' : f.gt_image) :
    (f ^ m) a' < (f ^ n) a := by
  obtain ⟨k, hk⟩ := Nat.le.dest n_lt_m.le
  have := gtImage_gt_pow_add f n (k-1) a a'
  simpa (disch := omega) [hk]

/--
  If `z` lies between `a` and `f a` for some `a` in `f.lt_image`,
  then `z` is in the image of some power of `f` applied to `f.lt_image`
-/
theorem ltImage_mem_interval_mem_pow_image {z : α} {a : f.lt_image}
    (a_le_z : a ≤ z) (z_lt_mapa : z < f a) :
    ∃(n' : ℕ) (a' : f.lt_image), (f ^ n') a' = z := by
  by_cases h : z ∈ f.lt_image
  · use 0, ⟨z, h⟩
    simp
  · simp only [lt_image, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_setOf_eq, not_forall, not_lt] at h
    obtain ⟨x, hx⟩ := h
    have : z ∈ f '' Set.Ico x a := by simp [hx, z_lt_mapa]
    have : z ∈ Set.range f := Set.mem_range_of_mem_image (⇑f) (Set.Ico x ↑a) this
    obtain ⟨y, hy⟩ := this
    subst_vars
    simp only [lt_iff_lt] at z_lt_mapa
    have y_mem : y ∈ f.lt_image := by
      simp only [lt_image, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
        Set.mem_setOf_eq]
      intro c
      have := a.prop.out (f c) (by simp)
      order
    use 1, ⟨y, y_mem⟩
    simp

/--
  If `z` lies between `a` and `f a` for some `a` in `f.gt_image`,
  then `z` is in the image of some power of `f` applied to `f.gt_image`
-/
theorem gtImage_mem_interval_mem_pow_image {z : α} {a : f.gt_image}
    (z_le_a : z ≤ a) (mapa_lt_z : f a < z) :
    ∃(n' : ℕ) (a' : f.gt_image), (f ^ n') a' = z := by
  by_cases h : z ∈ f.gt_image
  · use 0, ⟨z, h⟩
    simp
  · simp only [gt_image, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_setOf_eq, not_forall, not_lt] at h
    obtain ⟨x, hx⟩ := h
    have : z ∈ f '' Set.Ioc a x := by simp [hx, mapa_lt_z]
    have : z ∈ Set.range f := Set.mem_range_of_mem_image (⇑f) (Set.Ioc a x) this
    obtain ⟨y, hy⟩ := this
    subst_vars
    simp only [lt_iff_lt] at mapa_lt_z
    have y_mem : y ∈ f.gt_image := by
      simp only [gt_image, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
        Set.mem_setOf_eq]
      intro c
      have := a.prop.out (f c) (by simp)
      order
    use 1, ⟨y, y_mem⟩
    simp

/--
  If `z` lies between `(f ^ n) a` and `(f ^ (n+1)) a`
  for some `a` in `f.lt_image,`
  then `z` is in the image of some power of `f` applied to `f.lt_image`
-/
theorem ltImage_mem_pow_interval_mem_pow_image {a : f.lt_image}
    (a_le_z : (f ^ n) a ≤ z) (z_lt_mapa : z < (f ^ (n+1)) a) :
    ∃(n' : ℕ) (a' : f.lt_image), (f ^ n') a' = z := by
  induction n generalizing z with
  | zero =>
    simp only [pow_zero, coe_one, id_eq, zero_add, pow_one] at a_le_z z_lt_mapa
    exact ltImage_mem_interval_mem_pow_image f a_le_z z_lt_mapa
  | succ n ih =>
    set prev_interval := Set.Ico ((f^n) a) ((f^(n+1)) a)
    set next_interval := Set.Ico ((f^(n+1)) a) ((f^(n+1+1)) a)
    have z_mem : z ∈ next_interval := by simp [next_interval, a_le_z, z_lt_mapa]
    have : f '' prev_interval = next_interval := by
      simp [prev_interval, next_interval, ConvexEmbedding.add_pows_one, add_comm]
    simp only [← this, Set.mem_image] at z_mem
    obtain ⟨x, x_mem, fx_eq_z⟩ := z_mem
    simp only [Set.mem_Ico, prev_interval] at x_mem
    obtain ⟨n', a', h⟩ := ih x_mem.1 x_mem.2
    use 1+n', a'
    simp [pow_add, h, fx_eq_z]

/--
  If `z` lies between `(f ^ n) a` and `(f ^ (n+1)) a`
  for some `a` in `f.gt_image,`
  then `z` is in the image of some power of `f` applied to `f.gt_image`
-/
theorem gtImage_mem_pow_interval_mem_pow_image {a : f.gt_image}
    (z_le_a : z ≤ (f ^ n) a) (mapa_lt_z : (f ^ (n+1)) a < z) :
    ∃(n' : ℕ) (a' : f.gt_image), (f ^ n') a' = z := by
  induction n generalizing z with
  | zero =>
    simp only [pow_zero, coe_one, id_eq, zero_add, pow_one] at z_le_a mapa_lt_z
    exact gtImage_mem_interval_mem_pow_image f z_le_a mapa_lt_z
  | succ n ih =>
    set prev_interval := Set.Ioc ((f^(n+1)) a) ((f^n) a)
    set next_interval := Set.Ioc ((f^(n+1+1)) a) ((f^(n+1)) a)
    have z_mem : z ∈ next_interval := by simp [next_interval, z_le_a, mapa_lt_z]
    have : f '' prev_interval = next_interval := by
      simp [prev_interval, next_interval, ConvexEmbedding.add_pows_one, add_comm]
    simp only [← this, Set.mem_image] at z_mem
    obtain ⟨x, x_mem, fx_eq_z⟩ := z_mem
    simp only [Set.mem_Ioc, prev_interval] at x_mem
    obtain ⟨n', a', h⟩ := ih x_mem.2 x_mem.1
    use 1+n', a'
    simp [pow_add, h, fx_eq_z]

/--
  For any `a` in `f.lt_image` and `a'` in `f.gt_image`,
  `(f ^ n) a` is less than `(f ^ n') a'`
-/
theorem ltImage_pow_lt_gtImage_pow (a : f.lt_image) (a' : f.gt_image)
    (n n' : ℕ) : (f ^ n) a < (f ^ n') a' := by
  by_contra!
  obtain n_lt_n' | n_eq_n' | n'_lt_n := lt_trichotomy n n'
  · obtain ⟨k, hk⟩ := Nat.le.dest n_lt_n'
    simp only [← hk, Nat.succ_eq_add_one, add_assoc, pow_add _ n, coe_mul, Function.comp_apply,
      le_iff_le] at this
    have := a.prop.out ((f^(1 + k)) a') (by simp [pow_add])
    order
  · simp only [n_eq_n', le_iff_le] at this
    have : a' < f a := calc
      ↑a' ≤ ↑a := this
      _ < f a := ltImage_lt_pow f a a 0
    have := a'.prop.out (f a) (by simp)
    order
  · obtain ⟨k, hk⟩ := Nat.le.dest n'_lt_n
    simp only [← hk, Nat.succ_eq_add_one, add_assoc, pow_add _ n', coe_mul, Function.comp_apply,
      le_iff_le] at this
    have := a'.prop.out ((f^(1 + k)) a) (by simp [pow_add])
    order



/--
  Define a map from `ℕ(f.lt_image)` to `α`
-/
def omegaLtImage_map (na : ℕ ×ₗ f.lt_image) : α :=
    (f ^ (ofLex na).1) (ofLex na).2

/--
  Define a map from `ℕᵒᵈ(f.gt_image)` to `α`
-/
def omegaDualGtImage_map (na : ℕᵒᵈ ×ₗ f.gt_image) : α :=
    (f ^ (OrderDual.ofDual (ofLex na).1)) (ofLex na).2

/--
  The map from `ℕ(f.lt_image)` to `α` is injective
-/
theorem omegaLtImage_map_inj : Function.Injective f.omegaLtImage_map := by
  simp only [Function.Injective, omegaLtImage_map, Lex.forall, ofLex_toLex, Prod.forall,
    Subtype.forall, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, Subtype.mk.injEq]
  intro n a a_mem_image n' a' a'_mem_image eq
  obtain n_lt_n' | n_eq_n' | n'_lt_n := lt_trichotomy n n'
  · have := ltImage_lt_pow_lt f n_lt_n' ⟨a, a_mem_image⟩ ⟨a', a'_mem_image⟩
    order
  · simpa [n_eq_n'] using eq
  · have := ltImage_lt_pow_lt f n'_lt_n ⟨a', a'_mem_image⟩ ⟨a, a_mem_image⟩
    order

/--
  The map from `ℕᵒᵈ(f.gt_image)` to `α` is injective
-/
theorem omegaDualGtImage_map_inj : Function.Injective f.omegaDualGtImage_map := by
  simp only [Function.Injective, omegaDualGtImage_map, pow_ofDual, Lex.forall, ofLex_toLex,
    Prod.forall, Subtype.forall, OrderDual.forall, pow_toDual, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq, Subtype.mk.injEq]
  intro n a a_mem_image n' a' a'_mem_image eq
  obtain n_lt_n' | n_eq_n' | n'_lt_n := lt_trichotomy n n'
  · have := gtImage_lt_pow_gt f n_lt_n' ⟨a, a_mem_image⟩ ⟨a', a'_mem_image⟩
    order
  · simpa [n_eq_n'] using eq
  · have := gtImage_lt_pow_gt f n'_lt_n ⟨a', a'_mem_image⟩ ⟨a, a_mem_image⟩
    order

/--
  The map from `ℕ(f.lt_image)` to `α` preserves the ordering
-/
theorem omegaLtImage_map_rel_iff : ∀ {a b : ℕ ×ₗ f.lt_image},
    f.omegaLtImage_map a < f.omegaLtImage_map b ↔ a < b := by
  simp only [omegaLtImage_map, Prod.Lex.lt_iff, Lex.forall, ofLex_toLex, Prod.forall,
    Subtype.forall, Subtype.mk_lt_mk]
  intro n a a_mem n' a' a'_mem
  constructor
  · intro lt
    obtain n_lt_n' | n_eq_n' | n'_lt_n := lt_trichotomy n n'
    · simp [n_lt_n']
    · simpa [n_eq_n'] using lt
    · have := ltImage_lt_pow_lt f n'_lt_n ⟨a', a'_mem⟩ ⟨a, a_mem⟩
      order
  · intro lt
    obtain n_lt_n' | ⟨n_eq_n', a_lt_a'⟩ := lt
    · exact ltImage_lt_pow_lt f n_lt_n' ⟨a, a_mem⟩ ⟨a', a'_mem⟩
    · simp [n_eq_n', a_lt_a']

/--
  The map from `ℕᵒᵈ(f.gt_image)` to `α` preserves the ordering
-/
theorem omegaDualGtImage_map_rel_iff : ∀ {a b : ℕᵒᵈ ×ₗ f.gt_image},
    f.omegaDualGtImage_map a < f.omegaDualGtImage_map b ↔ a < b := by
  simp only [omegaDualGtImage_map, pow_ofDual, Prod.Lex.lt_iff, Lex.forall, ofLex_toLex,
    Prod.forall, Subtype.forall, OrderDual.forall, pow_toDual, Subtype.mk_lt_mk,
    OrderDual.toDual_lt_toDual, EmbeddingLike.apply_eq_iff_eq]
  intro n a a_mem n' a' a'_mem
  constructor
  · intro lt
    obtain n_lt_n' | n_eq_n' | n'_lt_n := lt_trichotomy n n'
    · have := gtImage_lt_pow_gt f n_lt_n' ⟨a, a_mem⟩ ⟨a', a'_mem⟩
      order
    · simpa [n_eq_n'] using lt
    · simp [n'_lt_n]
  · intro lt
    obtain n_lt_n' | ⟨n_eq_n', a_lt_a'⟩ := lt
    · exact gtImage_lt_pow_gt f n_lt_n' ⟨a', a'_mem⟩ ⟨a, a_mem⟩
    · simp [n_eq_n', a_lt_a']

theorem omegaLtImage_map_mem_range_of_rel : ∀ a : ℕ ×ₗ f.lt_image,
    ∀ b < f.omegaLtImage_map a, b ∈ Set.range f.omegaLtImage_map := by
  simp only [lt_image, Set.coe_setOf, omegaLtImage_map, Set.mem_setOf_eq, Set.mem_range, Lex.exists,
    ofLex_toLex, Prod.exists, Subtype.exists, forall_exists_index, forall_apply_eq_imp_iff,
    exists_prop, Lex.forall, Prod.forall, Subtype.forall]
  intro n a a_mem b b_lt
  induction n with
  | zero =>
    use 0, b
    simp only [pow_zero, coe_one, id_eq, and_true] at b_lt ⊢
    intro c
    have := a_mem c
    order
  | succ n ih =>
    by_cases h : b < (f ^ n) a
    · exact ih h
    · simp only [not_lt] at h
      obtain ⟨n', a', fna_eq_b⟩ :=
        ltImage_mem_pow_interval_mem_pow_image
          (a := ⟨a, by simp [lt_image, a_mem]⟩) f h b_lt
      use n', a'
      simp [fna_eq_b, a'.prop.out]

theorem omegaDualGtImage_map_mem_range_of_rel : ∀ a : (ℕᵒᵈ ×ₗ f.gt_image)ᵒᵈ,
    ∀ b < (OrderDual.toDual ∘ f.omegaDualGtImage_map ∘ OrderDual.ofDual) a,
    b ∈ Set.range (OrderDual.toDual ∘ f.omegaDualGtImage_map ∘ OrderDual.ofDual) := by
  simp [omegaDualGtImage_map, gt_image]
  intro n a a_mem b b_gt
  induction n with
  | zero =>
    use 0, b
    simp only [pow_zero, coe_one, id_eq, and_true] at b_gt ⊢
    intro c
    have := a_mem c
    order
  | succ n ih =>
    by_cases h : b > (f ^ n) a
    · exact ih h
    · simp only [not_lt] at h
      obtain ⟨n', a', fna_eq_b⟩ :=
        gtImage_mem_pow_interval_mem_pow_image
          (a := ⟨a, by simp [gt_image, a_mem]⟩) f h b_gt
      use n', a'
      simp [fna_eq_b, a'.prop.out]

/--
  `ℕ(f.lt_image)` is initial in `α`
-/
def omegaLtImage_initial : ℕ ×ₗ f.lt_image ≤i α where
  toFun := f.omegaLtImage_map
  inj' := omegaLtImage_map_inj f
  map_rel_iff' := omegaLtImage_map_rel_iff f
  mem_range_of_rel' := omegaLtImage_map_mem_range_of_rel f

/--
  `ℕᵒᵈ(f.gt_image)` is final in `α`
-/
def omegaDualGtImage_final : (ℕᵒᵈ ×ₗ f.gt_image)ᵒᵈ ≤i αᵒᵈ where
  toFun := OrderDual.toDual ∘ f.omegaDualGtImage_map ∘ OrderDual.ofDual
  inj' := by
    simp [omegaDualGtImage_map_inj f]
    exact Equiv.injective OrderDual.ofDual
  map_rel_iff' := by simp [omegaDualGtImage_map_rel_iff f]
  mem_range_of_rel' := omegaDualGtImage_map_mem_range_of_rel f

noncomputable def omegaDualGtImage_final_sum := final_as_sum (omegaDualGtImage_final f)

def omegaLtImage_initial_leftover : ℕ ×ₗ f.lt_image ≤i f.omegaDualGtImage_final.complDual :=
  initial_subset_initial (s := f.omegaDualGtImage_final.complDual) (omegaLtImage_initial f)
    (by
      intro x x_mem
      simp only [Set.mem_range, Lex.exists, Prod.exists, Subtype.exists] at x_mem
      obtain ⟨n, a, a_mem, h⟩ := x_mem
      simp only [omegaLtImage_initial] at h
      change f.omegaLtImage_map _ = _ at h
      simp only [omegaLtImage_map, ofLex_toLex] at h
      simp only [InitialSeg.complDual, Set.mem_compl_iff, Set.mem_range, Lex.exists, Prod.exists,
        Subtype.exists, OrderDual.exists, not_exists]
      intro n' a' a'_mem h2
      simp only [InitialSeg.undual, undual, OrderEmbedding.undual', omegaDualGtImage_final] at h2
      change
        (OrderDual.ofDual ∘ ⇑OrderDual.toDual ∘ f.omegaDualGtImage_map ∘ ⇑OrderDual.ofDual ∘ OrderDual.toDual)
          _ = _ at h2
      simp only [Function.comp_apply, omegaDualGtImage_map, OrderDual.ofDual_toDual,
        ofLex_toLex] at h2
      simp only [← h2] at h
      have := ltImage_pow_lt_gtImage_pow f ⟨a, a_mem⟩ ⟨a', a'_mem⟩ n n'
      order
    )

abbrev center := (omegaLtImage_initial_leftover f).compl

/--
  If `f` if a convex embedding from `α` to itself,
  then `α` is isomorphic to `ℕ(f.lt_image) + f.center + ℕᵒᵈ(f.gt_image)`
-/
noncomputable def decomp : α ≃o ℕ ×ₗ f.lt_image ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image := by
  orderCalc α
  _ ≃o ↑f.omegaDualGtImage_final.complDual ⊕ₗ ℕᵒᵈ ×ₗ ↑f.gt_image :=
      (omegaDualGtImage_final_sum f).symm
  _ ≃o (ℕ ×ₗ f.lt_image ⊕ₗ f.center) ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image := by
      orderCongr [(initial_as_sum (omegaLtImage_initial_leftover f)).symm]
  _ ≃o ℕ ×ₗ f.lt_image ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image := by orderCongr

/--
  If `f` if a convex embedding from `α` to itself,
  then `f.lt_image + α` is isomorphic to `α`
-/
noncomputable def absorb_ltImage : f.lt_image ⊕ₗ α ≃o α := by
  orderCalc f.lt_image ⊕ₗ α
  _ ≃o f.lt_image ⊕ₗ ℕ ×ₗ f.lt_image ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image := by orderCongr [f.decomp]
  _ ≃o (f.lt_image ⊕ₗ ℕ ×ₗ f.lt_image) ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image := by orderCongr
  _ ≃o ℕ ×ₗ f.lt_image ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image := by orderCongr [A_plus_omegaA_iso_omegaA]
  _ ≃o α := f.decomp.symm

/--
  If `f` if a convex embedding from `α` to itself,
  then `α + f.gt_image` is isomorphic to `α`
-/
noncomputable def absorb_gtImage : α ⊕ₗ f.gt_image ≃o α := by
  orderCalc α ⊕ₗ f.gt_image
  _ ≃o (ℕ ×ₗ f.lt_image ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image) ⊕ₗ f.gt_image := by orderCongr [f.decomp]
  _ ≃o ℕ ×ₗ f.lt_image ⊕ₗ (f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image) ⊕ₗ f.gt_image := by orderCongr
  _ ≃o ℕ ×ₗ f.lt_image ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image ⊕ₗ f.gt_image := by orderCongr
  _ ≃o ℕ ×ₗ f.lt_image ⊕ₗ f.center ⊕ₗ ℕᵒᵈ ×ₗ f.gt_image := by orderCongr [omegaDualA_plus_A_iso_omegaDualA]
  _ ≃o α := f.decomp.symm

end ConvexEmbedding
