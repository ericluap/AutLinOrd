import AutLinOrd.Embeddings.InitialSeg
import AutLinOrd.Embeddings.OrderIso
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Order.Fin.Basic

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
def omegaDual_plus_n_iso_omegaDual (n : ℕ) : ℕᵒᵈ ⊕ₗ Fin n ≃o ℕᵒᵈ :=
  let distrib_od : (Fin n ⊕ₗ ℕ)ᵒᵈ ≃o ℕᵒᵈ ⊕ₗ (Fin n)ᵒᵈ :=
    OrderIso.sumLexDualAntidistrib (Fin n) ℕ
  let fin_n_eq : (Fin n)ᵒᵈ ≃o (Fin n) := by exact Fin.revOrderIso
  (fin_n_eq.sumCongrRight (α₁ := ℕᵒᵈ)).symm.trans distrib_od.symm
    |>.trans (n_plus_omega_iso_omega n).dual

/--
  `nA + ℕA` is isomorphic to `ℕA`
-/
def nA_plus_omegaA_iso_omegaA (A) [Preorder A] (n : ℕ) :
    (Fin n) ×ₗ A ⊕ₗ ℕ ×ₗ A ≃o ℕ ×ₗ A :=
  (OrderIso.sumProdDistrib (Fin n) ℕ A).symm.trans
    ((n_plus_omega_iso_omega n).prodCongr (OrderIso.refl A))

/--
  `A + ℕA` is isomorphic to `ℕA`
-/
def A_plus_omegaA_iso_omegaA (A) [Preorder A] :
    A ⊕ₗ ℕ ×ₗ A ≃o ℕ ×ₗ A :=
  let : Fin 1 ×ₗ A ≃o A := Prod.Lex.uniqueProd (Fin 1) A
  let := OrderIso.sumLexCongr this (OrderIso.refl (ℕ ×ₗ A))
  this.symm.trans (nA_plus_omegaA_iso_omegaA A 1)

/--
  `ℕᵒᵈA + nA` is isomorphic to `ℕᵒᵈA`.
-/
def omegaDualA_plus_nA_iso_omegaDualA (A) [Preorder A] (n : ℕ) :
    ℕᵒᵈ ×ₗ A ⊕ₗ (Fin n) ×ₗ A ≃o ℕᵒᵈ ×ₗ A :=
  (OrderIso.sumProdDistrib ℕᵒᵈ (Fin n) A).symm.trans
    ((omegaDual_plus_n_iso_omegaDual n).prodCongr (OrderIso.refl A))

/--
  `ℕᵒᵈA + A` is isomorphic to `ℕA`
-/
def omegaDualA_plus_A_iso_omegaDualA (A) [Preorder A] :
    ℕᵒᵈ ×ₗ A ⊕ₗ A ≃o ℕᵒᵈ ×ₗ A :=
  let : Fin 1 ×ₗ A ≃o A := Prod.Lex.uniqueProd (Fin 1) A
  let := OrderIso.sumLexCongr (OrderIso.refl (ℕᵒᵈ ×ₗ A)) this
  this.symm.trans (omegaDualA_plus_nA_iso_omegaDualA A 1)

/--
  If `ℕA` is initial in `X`, then `A + X` is isomorphic to `X`
-/
noncomputable def omegaA_initial_absorbs [LinearOrder A] [LinearOrder X]
    (omegaA_initial : ℕ ×ₗ A ≤i X) : A ⊕ₗ X ≃o X :=
  let nA_compl_eq_X := initial_as_sum omegaA_initial
  let A_plus_nA_compl_eq_A_X := OrderIso.sumLexCongr (OrderIso.refl A) nA_compl_eq_X
  let A_nA_plus_compl_eq_A_plus_nA_compl := OrderIso.sumLexAssoc A (ℕ ×ₗ A) omegaA_initial.compl
  let A_nA_plus_compl_eq_A_X := A_nA_plus_compl_eq_A_plus_nA_compl.trans A_plus_nA_compl_eq_A_X
  let A_nA_plus_compl_eq_nA_plus_compl :=
    OrderIso.sumLexCongr (A_plus_omegaA_iso_omegaA A) (OrderIso.refl omegaA_initial.compl)
  let A_X_eq_nA_compl := A_nA_plus_compl_eq_A_X.symm.trans A_nA_plus_compl_eq_nA_plus_compl
  A_X_eq_nA_compl.trans nA_compl_eq_X

/--
  If `ℕᵒᵈA` is final in `X`, then `X + A` is isomorphic to `X`
-/
noncomputable def omegaDualA_final_absorbs [LinearOrder A] [LinearOrder X]
    (omegaDualA_final : (ℕᵒᵈ ×ₗ A)ᵒᵈ ≤i Xᵒᵈ) : X ⊕ₗ A ≃o X :=
  let complDual_plus_nA_eq_X := final_as_sum omegaDualA_final
  let complDual_nA_plus_A_eq_X_A := OrderIso.sumLexCongr complDual_plus_nA_eq_X (OrderIso.refl A)
  let complDual_plus_nA_A_eq_complDual_nA_plus_A := OrderIso.sumLexAssoc omegaDualA_final.complDual (ℕᵒᵈ ×ₗ A) A
  let complDual_plus_nA_A_eq_X_A := complDual_plus_nA_A_eq_complDual_nA_plus_A.symm.trans complDual_nA_plus_A_eq_X_A
  let complDual_plus_nA_A_eq_complDual_plus_nA :=
    OrderIso.sumLexCongr (OrderIso.refl omegaDualA_final.complDual) (omegaDualA_plus_A_iso_omegaDualA A)
  let complDual_nA_eq_X_A := complDual_plus_nA_A_eq_X_A.symm.trans complDual_plus_nA_A_eq_complDual_plus_nA
  complDual_nA_eq_X_A.trans complDual_plus_nA_eq_X
