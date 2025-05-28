import Mathlib.Order.InitialSeg
import Mathlib.Order.Interval.Set.OrdConnected

variable [LinearOrder α] {A B : Set α}

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
  If `ExtendsLeftRight A B`, then both `A` and `B` are nonempty.
-/
theorem extendsLeftRight_nonempty_both (A B : Set α)
    (extendsLeftRight : ExtendsLeftRight A B) : Nonempty A ∧ Nonempty B := by
  obtain ⟨⟨x, x_mem_A, x_mem_B⟩, _, _⟩ := extendsLeftRight
  constructor
  <;> use x

/--
  If `ExtendsLeftRight A B`, then `A ∩ B` is nonempty.
-/
theorem extendsLeftRight_nonempty_inter (A B : Set α)
    (extendsLeftRight : ExtendsLeftRight A B) : Nonempty (A ∩ B : Set α) := by
  obtain ⟨⟨x, x_mem_A, x_mem_B⟩, _, _⟩ := extendsLeftRight
  simp only [nonempty_subtype, Set.mem_inter_iff]
  use x

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
