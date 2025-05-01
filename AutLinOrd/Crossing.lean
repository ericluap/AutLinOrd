import Mathlib
import AutLinOrd.ConvexEmbedding

variable [LinearOrder α]

open InitialSeg

variable (n : ℕ)
#check ({n} : Set ℕ)

theorem lowerbound_subset_omega [LinearOrder A] (S : Set (ℕ ×ₗ A))
    (l : ℕ ×ₗ A) (l_lowerbound : ∀s ∈ S, l < s) :
    ∃(T : Type*) (_ : LinearOrder T),
    Nonempty (T ≤i S) ∧ Nonempty (T ≤c A) := by
  set possibleN := {n | ∃(a : A), ∀s ∈ S, toLex (n, a) ≤ s}
    with possibleN_def
  have : Nonempty possibleN := by
    simp only [nonempty_subtype]
    use 0, l.2
    intro s hs
    have : toLex (0, l.2) ≤ l := by
      have : l = toLex (l.1, l.2) := rfl
      conv_rhs => rw [this]
      simp only [Prod.mk.eta, Prod.Lex.le_iff, ofLex_toLex, le_refl, and_true]
      omega
    have := l_lowerbound s hs
    order
  sorry

theorem initial_seg_embeds_in_single {y l u} {I J : Type*} [LinearOrder I]
    [LinearOrder J] {A B : Set α} (A_interval : A.OrdConnected)
    (B_interval : B.OrdConnected) (y_mem_a : y ∈ A) (y_mem_b : y ∈ B)
    (l_mem_a : l ∈ A) (l_lowerbound : ∀b ∈ B, l < b)
    (u_mem_b : u ∈ B) (u_upperbound : ∀a ∈ A, a < u)
    (A_iso : A ≃o ℕ ×ₗ I) (B_iso : B ≃o ℕᵒᵈ ×ₗ J) :
    ∃(T : Type*) (_ : LinearOrder T),
    Nonempty (T ≤i ℕᵒᵈ ×ₗ J) ∧ Nonempty (T ≤c I) := by sorry

theorem initial_in_omega_star_swap [LinearOrder T] [LinearOrder J]
  (h : T ≤i ℕᵒᵈ ×ₗ J) : Nonempty (ℕᵒᵈ ×ₗ J ≤i T) := by sorry

theorem crossing_embed {y l u} {I J : Type*} [LinearOrder I] [LinearOrder J]
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
    have := initial_in_omega_star_swap.{u_2} init
    obtain ⟨initial⟩ := Classical.exists_true_of_nonempty this
    have := initial_emb_convex_emb initial
    exact Nonempty.intro (convex.comp this)
