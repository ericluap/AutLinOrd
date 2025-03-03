import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Order.RelIso.Group

section MulAction
variable {α : Type*} {s : α → α → Prop}

instance RelIso.applyMulAction : MulAction (s ≃r s) α where
  smul f := f
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

end MulAction
