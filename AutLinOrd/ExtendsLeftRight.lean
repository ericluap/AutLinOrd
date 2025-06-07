import Mathlib.Order.InitialSeg
import Mathlib.Order.Interval.Set.OrdConnected
import AutLinOrd.ConvexEmbedding
import Mathlib

seal OrderDual
seal Lex

variable [LinearOrder α] {A B : Set α}

/--
  `Intersect A B` means that `A` and `B` intersect.
-/
def Intersect (A B : Set α) := ∃x, x ∈ A ∧ x ∈ B

/--
  `ExtendsLeft A B` means that for every `b ∈ B`,
  there exists an `a ∈ A` such that `a ≤ b`, and
  `A` and `B` intersect
-/
def ExtendsLeft (A B : Set α) := (∀b ∈ B, ∃a ∈ A, a ≤ b)
  ∧ Intersect A B
/--
  `ExtendsRight A B` means that for every `b ∈ B`,
  there exists an `a ∈ A` such that `b ≤ a`, and
  `A` and `B` intersect.
-/
def ExtendsRight (A B : Set α) := (∀b ∈ B, ∃a ∈ A, b ≤ a)
  ∧ Intersect A B

/--
  `ExtendsLeftRight A B` means that `A` extends `B` to the left
  and `B` extends `A` to the right.
-/
def ExtendsLeftRight (A B : Set α) := ExtendsLeft A B ∧ ExtendsRight B A

/--
  If `A` extends `B` to the left, then `A ∩ B` is an initial segment of `B`.
-/
def extendsLeft_intersect_initial (A B : Set α) (A_interval : A.OrdConnected)
    (extendsLeft : ExtendsLeft A B) : (A ∩ B : Set α) ≤i B where
  toFun x := ⟨x.val, x.prop.2⟩
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.inter_subset_right,
      Set.range_inclusion, Set.mem_inter_iff, Subtype.coe_prop, and_true, Set.mem_setOf_eq,
      Subtype.forall, Subtype.mk_lt_mk, and_imp]
    intro a a_mem_A a_mem_B b b_mem_B b_lt_a
    simp only [Set.ordConnected_iff] at A_interval
    obtain ⟨a', a'_mem_A, a'_le_b⟩ := extendsLeft.1 b b_mem_B
    have icc_subset_A := A_interval a' a'_mem_A a a_mem_A (by order)
    have b_mem_icc : b ∈ Set.Icc a' a := by
      simp only [Set.mem_Icc]
      constructor
      <;> order
    exact icc_subset_A b_mem_icc

unseal OrderDual in
/--
  If `B` extends `A` to the right, then `A ∩ B` is final in `A`.
-/
def extendsRight_intersect_final (A B : Set α) (B_interval : B.OrdConnected)
    (extendsRight : ExtendsRight B A) : (A ∩ B : Set α)ᵒᵈ ≤i Aᵒᵈ where
  toFun x := OrderDual.toDual
    ⟨(OrderDual.ofDual x).val, (OrderDual.ofDual x).prop.1⟩
  inj' := by simp [Function.Injective]
  map_rel_iff' := by simp
  mem_range_of_rel' := by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.mem_range, OrderDual.exists,
      OrderDual.ofDual_toDual, Subtype.exists, Set.mem_inter_iff, OrderDual.forall,
      OrderDual.toDual_lt_toDual, EmbeddingLike.apply_eq_iff_eq, Subtype.forall, Subtype.mk_lt_mk,
      Subtype.mk.injEq, exists_prop, exists_eq_right, and_imp]
    intro a a_mem_A a_mem_B b b_mem_A a_lt_b
    obtain ⟨c, c_mem_B, b_le_c⟩ := extendsRight.1 b b_mem_A
    simp only [Set.ordConnected_iff] at B_interval
    have icc_subset_B := B_interval a a_mem_B c c_mem_B (by order)
    have b_mem_icc: b ∈ Set.Icc a c := by
      simp only [Set.mem_Icc]
      constructor
      <;> order
    exact ⟨b_mem_A, icc_subset_B b_mem_icc⟩

/--
  If `ExtendsLeftRight A B`, then both `A` and `B` are nonempty.
-/
theorem extendsLeftRight_nonempty_both (A B : Set α)
    (extendsLeftRight : ExtendsLeftRight A B) : Nonempty A ∧ Nonempty B := by
  obtain ⟨⟨_, x, x_mem_A, x_mem_B⟩, _⟩ := extendsLeftRight
  constructor
  <;> use x

/--
  If `ExtendsLeftRight A B`, then `A ∩ B` is nonempty.
-/
theorem extendsLeftRight_nonempty_inter (A B : Set α)
    (extendsLeftRight : ExtendsLeftRight A B) : Nonempty (A ∩ B : Set α) := by
  obtain ⟨⟨_, x, x_mem_A, x_mem_B⟩, _⟩ := extendsLeftRight
  simp only [nonempty_subtype, Set.mem_inter_iff]
  use x

/--
  If `a` is in both `A` and `B`, `z` is in `B`, and `z ≤ a`,
  then `z ∈ A`.
-/
theorem mem_le_inter_mem (A_interval : A.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B)
    (a_mem_A : a ∈ A) (z_mem_B : z ∈ B) (z_le_a : z ≤ a) :
    z ∈ A := by
  simp only [Set.ordConnected_iff] at A_interval
  obtain ⟨l, l_mem_A, hl⟩ := extendsLeftRight.1.1 z z_mem_B
  apply A_interval l l_mem_A a a_mem_A (by order)
  exact ⟨hl, z_le_a⟩

/--
  If `a` is in both `A` and `B`, `z` is in `A`, and `a ≤ z`,
  then `z ∈ B`.
-/
theorem mem_ge_inter_mem (B_interval : B.OrdConnected)
    (extendsLeftRight : ExtendsLeftRight A B)
    (a_mem_B : a ∈ B) (z_mem_A : z ∈ A) (a_le_z : a ≤ z) :
    z ∈ B := by
  simp only [Set.ordConnected_iff] at B_interval
  obtain ⟨u, u_mem_A, hl⟩ := extendsLeftRight.2.1 z z_mem_A
  apply B_interval a a_mem_B u u_mem_A (by order)
  exact ⟨a_le_z, hl⟩

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
    intro a a_mem_A a_mem_B z z_mem_B z_lt_a
    exact mem_le_inter_mem A_interval extendsLeftRight a_mem_A z_mem_B z_lt_a.le

unseal OrderDual in
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
    · exact mem_ge_inter_mem B_interval extendsLeftRight a_mem_B z_mem_A
        a_lt_z.le
