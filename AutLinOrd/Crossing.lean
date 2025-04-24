import Mathlib

open InitialSeg

variable {α : Type*} [LinearOrder α]

variable (f : α ↪o α)

/--
  `isImageOrdConnected f` means that the image of `f`
  is an interval.
-/
def isImageOrdConnected [Preorder β] (f : α → β) :=
  (Set.range f).OrdConnected

/--
  `convexlyEmbeds α β` means that `α` convexly embeds in `β`
-/
def convexlyEmbeds (α β : Type*) [LinearOrder α] [LinearOrder β] :=
  ∃f : α ↪o β, isImageOrdConnected f

@[inherit_doc]
infixl:24 " ≤c " => convexlyEmbeds

theorem convexlyEmbedsTrans {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
  (_ : α ≤c β) (_ : β ≤c γ) : α ≤c γ := sorry

theorem initial_emb_convex_emb [LinearOrder α] [LinearOrder β]
    (initial : α ≤i β) : α ≤c β := by
  use initial.toOrderEmbedding
  simp [isImageOrdConnected]
  sorry

notation3:25 α:24 " ≤j " β:25 => @InitialSeg α β (· < ·) (· < ·)

theorem initial_seg_embeds_in_single {y l u} {I J : Type*} [LinearOrder I]
    [LinearOrder J] {A B : Set α} (y_mem_a : y ∈ A) (y_mem_b : y ∈ B)
    (l_mem_a : l ∈ A) (l_lowerbound : ∀b ∈ B, l < b)
    (u_mem_b : u ∈ B) (u_upperbound : ∀a ∈ A, a < u)
    (A_iso : A ≃o ℕ ×ₗ I) (B_iso : B ≃o ℕᵒᵈ ×ₗ J) :
    ∃(T : Type*) (_ : LinearOrder T),
    Nonempty (T ≤j ℕᵒᵈ ×ₗ J) ∧ Nonempty (T ≤c I) := by sorry

theorem initial_in_omega_star_swap [LinearOrder T] [LinearOrder J]
  (h : T ≤j ℕᵒᵈ ×ₗ J) : Nonempty (ℕᵒᵈ ×ₗ J ≤j T) := by sorry

theorem crossing_embed {y l u} {I J : Type*} [LinearOrder I] [LinearOrder J]
    {A B : Set α} (y_mem_a : y ∈ A) (y_mem_b : y ∈ B)
    (l_mem_a : l ∈ A) (l_lowerbound : ∀b ∈ B, l < b)
    (u_mem_b : u ∈ B) (u_upperbound : ∀a ∈ A, a < u)
    (A_iso : A ≃o ℕ ×ₗ I) (B_iso : B ≃o ℕᵒᵈ ×ₗ J) :
    Nonempty (ℕ ×ₗ I ≤c J) ∧ Nonempty (ℕᵒᵈ ×ₗ J ≤c I) := by
  constructor
  · sorry
  · obtain ⟨T, _, ⟨init, convex⟩⟩ := initial_seg_embeds_in_single
      y_mem_a y_mem_b l_mem_a l_lowerbound u_mem_b u_upperbound A_iso B_iso
    simp only [←exists_true_iff_nonempty] at init convex
    obtain ⟨init⟩ := init
    obtain ⟨convex⟩ := convex
    have := initial_in_omega_star_swap.{u_2} init
    obtain ⟨initial⟩ := Classical.exists_true_of_nonempty this
    have := initial_emb_convex_emb initial
    exact Nonempty.intro (convexlyEmbedsTrans this convex)
