import Mathlib
import AutLinOrd.Embeddings.ConvexEmbedding
import AutLinOrd.Embeddings.Embeddings

seal OrderDual
seal Lex

namespace OrderIso
variable [Preorder α₁] [Preorder α₂] [Preorder β₁] [Preorder β₂]

def prodCongr (e₁ : α₁ ≃o α₂) (e₂ : β₁ ≃o β₂) : α₁ ×ₗ β₁ ≃o α₂ ×ₗ β₂ where
  toFun := toLex ∘ Prod.map e₁ e₂ ∘ ofLex
  invFun := toLex ∘ Prod.map e₁.symm e₂.symm ∘ ofLex
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp [Prod.Lex.le_iff]

def prodCongrLeft (e : β₁ ≃o β₂) : β₁ ×ₗ α₁ ≃o β₂ ×ₗ α₁ where
  toFun ba := toLex <| (ofLex ba).map e id
  invFun ba := toLex <| (ofLex ba).map e.symm id
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp [Prod.Lex.le_iff]

@[simp]
theorem prodCongrLeft_apply (e : β₁ ≃o β₂) (b : β₁) (a : α₁) :
    prodCongrLeft e (toLex (b, a)) = toLex (e b, a) := rfl

def prodCongrRight (e : β₁ ≃o β₂) : α₁ ×ₗ β₁ ≃o α₁ ×ₗ β₂ where
  toFun ba := toLex <| (ofLex ba).map id e
  invFun ba := toLex <| (ofLex ba).map id e.symm
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp [Prod.Lex.le_iff]

@[simp]
theorem prodCongrRight_apply (e : β₁ ≃o β₂) (a : α₁) (b : β₁) :
    prodCongrRight e (toLex (a, b)) = toLex (a, e b) := rfl

def sumCongr (e₁ : α₁ ≃o α₂) (e₂ : β₁ ≃o β₂) : α₁ ⊕ₗ β₁ ≃o α₂ ⊕ₗ β₂ where
  toFun := toLex ∘ Sum.map e₁ e₂ ∘ ofLex
  invFun := toLex ∘ Sum.map e₁.symm e₂.symm ∘ ofLex
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp [Prod.Lex.le_iff]

def sumCongrLeft (e : β₁ ≃o β₂) : β₁ ⊕ₗ α₁ ≃o β₂ ⊕ₗ α₁ where
  toFun ba := toLex <| (ofLex ba).map e id
  invFun ba := toLex <| (ofLex ba).map e.symm id
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp [Prod.Lex.le_iff]

def sumCongrRight (e : β₁ ≃o β₂) : α₁ ⊕ₗ β₁ ≃o α₁ ⊕ₗ β₂ where
  toFun ba := toLex <| (ofLex ba).map id e
  invFun ba := toLex <| (ofLex ba).map id e.symm
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp [Prod.Lex.le_iff]

def sumProdDistrib (α β γ) [Preorder α] [Preorder β] [Preorder γ] :
    (α ⊕ₗ β) ×ₗ γ ≃o α ×ₗ γ ⊕ₗ β ×ₗ γ where
  toFun x := toLex <| (ofLex (ofLex x).1).map
    (fun y => (toLex (y, (ofLex x).2))) (fun y => (toLex (y, (ofLex x).2)))
  invFun x := (ofLex x).elim (toLex ∘ Prod.map Sum.inlₗ id ∘ ofLex)
    (toLex ∘ Prod.map Sum.inrₗ id ∘ ofLex)
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by
    intro a b
    cases' a with a; obtain ⟨a1, a2⟩ := a
    cases' b with b; obtain ⟨b1, b2⟩ := b
    cases' a1 with a1; obtain a1 | a1 := a1
    <;> (cases' b1 with b1; obtain b1 | b1 := b1)
    <;> simp [Prod.Lex.le_iff]

 end OrderIso
