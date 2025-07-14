import AutLinOrd.Embeddings.InitialSeg
import AutLinOrd.Embeddings.OrderIso
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Order.Fin.Basic
import AutLinOrd.CalcOrderIso

/-!
  This file proves basic facts about additive absorption.
-/

seal OrderDual
seal Lex

/--
  `n + ℕ` is isomorphic to `ℕ`
-/
def n_plus_omega_iso_omega (n : ℕ) : Fin n ⊕ₗ ℕ ≃o ℕ where
  toFun x :=
    match (ofLex x) with
    | Sum.inl x => x
    | Sum.inr x => x + n
  invFun x :=
    if h : x < n then
      Sum.inlₗ ⟨x, h⟩
    else
      Sum.inrₗ (x - n)
  left_inv := by simp [Function.LeftInverse]
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro x
    by_cases h : x < n
    · simp [h]
    · simp only [h, ↓reduceDIte, ofLex_toLex]
      omega
  map_rel_iff' := by
    intro a b
    cases' a with a; obtain a | a := a
    <;> (cases' b with b; obtain b | b := b)
    <;> simp
    · omega
    · omega

/--
  `ℕᵒᵈ + n` is isomorphic to `ℕᵒᵈ`
-/
def omegaDual_plus_n_iso_omegaDual (n : ℕ) : ℕᵒᵈ ⊕ₗ Fin n ≃o ℕᵒᵈ := by
  orderCalc ℕᵒᵈ ⊕ₗ Fin n
  _ ≃o ℕᵒᵈ ⊕ₗ (Fin n)ᵒᵈ := by orderCongr [Fin.revOrderIso.symm]
  _ ≃o (Fin n ⊕ₗ ℕ)ᵒᵈ := OrderIso.sumLexDualAntidistrib (Fin n) ℕ |>.symm
  _ ≃o ℕᵒᵈ := (n_plus_omega_iso_omega n).dual

/--
  `nA + ℕA` is isomorphic to `ℕA`
-/
def nA_plus_omegaA_iso_omegaA (A) [Preorder A] (n : ℕ) :
    (Fin n) ×ₗ A ⊕ₗ ℕ ×ₗ A ≃o ℕ ×ₗ A := by
  orderCalc (Fin n) ×ₗ A ⊕ₗ ℕ ×ₗ A
  _ ≃o (Fin n ⊕ₗ ℕ) ×ₗ A := OrderIso.sumProdDistrib (Fin n) ℕ A |>.symm
  _ ≃o ℕ ×ₗ A := by orderCongr [n_plus_omega_iso_omega]

/--
  `A + ℕA` is isomorphic to `ℕA`
-/
def A_plus_omegaA_iso_omegaA (A) [Preorder A] : A ⊕ₗ ℕ ×ₗ A ≃o ℕ ×ₗ A := by
  orderCalc A ⊕ₗ ℕ ×ₗ A
  _ ≃o Fin 1 ×ₗ A ⊕ₗ ℕ ×ₗ A := by orderCongr [(Prod.Lex.uniqueProd (Fin 1) A).symm]
  _ ≃o ℕ ×ₗ A := nA_plus_omegaA_iso_omegaA A 1

/--
  `ℕᵒᵈA + nA` is isomorphic to `ℕᵒᵈA`.
-/
def omegaDualA_plus_nA_iso_omegaDualA (A) [Preorder A] (n : ℕ) :
    ℕᵒᵈ ×ₗ A ⊕ₗ (Fin n) ×ₗ A ≃o ℕᵒᵈ ×ₗ A := by
  orderCalc ℕᵒᵈ ×ₗ A ⊕ₗ (Fin n) ×ₗ A
  _ ≃o (ℕᵒᵈ ⊕ₗ Fin n) ×ₗ A := OrderIso.sumProdDistrib ℕᵒᵈ (Fin n) A |>.symm
  _ ≃o ℕᵒᵈ ×ₗ A := by orderCongr [omegaDual_plus_n_iso_omegaDual]

/--
  `ℕᵒᵈA + A` is isomorphic to `ℕA`
-/
def omegaDualA_plus_A_iso_omegaDualA (A) [Preorder A] :
    ℕᵒᵈ ×ₗ A ⊕ₗ A ≃o ℕᵒᵈ ×ₗ A := by
  orderCalc ℕᵒᵈ ×ₗ A ⊕ₗ A
  _ ≃o ℕᵒᵈ ×ₗ A ⊕ₗ Fin 1 ×ₗ A := by orderCongr [(Prod.Lex.uniqueProd (Fin 1) A).symm]
  _ ≃o ℕᵒᵈ ×ₗ A := omegaDualA_plus_nA_iso_omegaDualA A 1

/--
  If `ℕA` is initial in `X`, then `A + X` is isomorphic to `X`
-/
noncomputable def omegaA_initial_absorbs [LinearOrder A] [LinearOrder X]
    (omegaA_initial : ℕ ×ₗ A ≤i X) : A ⊕ₗ X ≃o X := by
  orderCalc A ⊕ₗ X
  _ ≃o A ⊕ₗ ℕ ×ₗ A ⊕ₗ omegaA_initial.compl := by orderCongr [(initial_as_sum omegaA_initial).symm]
  _ ≃o (A ⊕ₗ ℕ ×ₗ A) ⊕ₗ omegaA_initial.compl := by orderCongr
  _ ≃o ℕ ×ₗ A ⊕ₗ omegaA_initial.compl := by orderCongr [A_plus_omegaA_iso_omegaA]
  _ ≃o X := initial_as_sum omegaA_initial

/--
  If `ℕᵒᵈA` is final in `X`, then `X + A` is isomorphic to `X`
-/
noncomputable def omegaDualA_final_absorbs [LinearOrder A] [LinearOrder X]
    (omegaDualA_final : (ℕᵒᵈ ×ₗ A)ᵒᵈ ≤i Xᵒᵈ) : X ⊕ₗ A ≃o X := by
  orderCalc X ⊕ₗ A
  _ ≃o (omegaDualA_final.complDual ⊕ₗ ℕᵒᵈ ×ₗ A) ⊕ₗ A := by orderCongr [(final_as_sum omegaDualA_final).symm]
  _ ≃o omegaDualA_final.complDual ⊕ₗ ℕᵒᵈ ×ₗ A ⊕ₗ A := by orderCongr
  _ ≃o omegaDualA_final.complDual ⊕ₗ ℕᵒᵈ ×ₗ A  := by orderCongr [omegaDualA_plus_A_iso_omegaDualA]
  _ ≃o X := final_as_sum omegaDualA_final
