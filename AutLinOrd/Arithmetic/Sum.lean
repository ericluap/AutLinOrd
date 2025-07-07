import Mathlib
import AutLinOrd.Embeddings.ConvexEmbedding
import AutLinOrd.Embeddings.Embeddings
import AutLinOrd.OrderIso

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
def nA_plus_omegaA_iso_omegaA [Preorder A] (n : ℕ) :
    (Fin n) ×ₗ A ⊕ₗ ℕ ×ₗ A ≃o ℕ ×ₗ A :=
  (OrderIso.sumProdDistrib (Fin n) ℕ A).symm.trans
    ((n_plus_omega_iso_omega n).prodCongr (OrderIso.refl A))

/--
  `ℕᵒᵈA + nA` is isomorphic to `ℕᵒᵈA`.
-/
def omegaDualA_plus_nA_iso_omegaDualA [Preorder A] (n : ℕ) :
    ℕᵒᵈ ×ₗ A ⊕ₗ (Fin n) ×ₗ A ≃o ℕᵒᵈ ×ₗ A :=
  (OrderIso.sumProdDistrib ℕᵒᵈ (Fin n) A).symm.trans
    ((omegaDual_plus_n_iso_omegaDual n).prodCongr (OrderIso.refl A))
