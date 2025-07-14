import Lean
import AutLinOrd.Embeddings.OrderIso
import AutLinOrd.Embeddings.InitialSeg

open Lean Elab Command Term Meta Tactic

def sumLeft [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : A ⊕ₗ B ≃o A ⊕ₗ C := OrderIso.sumLexCongr (OrderIso.refl A) h

def sumRight [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : B ⊕ₗ A ≃o C ⊕ₗ A := OrderIso.sumLexCongr h (OrderIso.refl A)

def prodLeft [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : A ×ₗ B ≃o A ×ₗ C := OrderIso.prodCongr (OrderIso.refl A) h

def prodRight [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : B ×ₗ A ≃o C ×ₗ A := OrderIso.prodCongr h (OrderIso.refl A)

def sumLexAssocSymm [LinearOrder A] [LinearOrder B] [LinearOrder C] :
    A ⊕ₗ B ⊕ₗ C ≃o (A ⊕ₗ B) ⊕ₗ C := OrderIso.sumLexAssoc A B C |>.symm

syntax "orderCongr" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| orderCongr $[[$arg,*]]?) =>
  `(tactic|
    try (first
      | assumption
      $[| exact $(arg.getD {})]*
      $[| apply $(arg.getD {})]*
      | apply OrderIso.refl
      | apply sumLeft
      | apply sumRight
      | apply prodLeft
      | apply prodRight
      | apply OrderIso.sumLexAssoc
      | apply sumLexAssocSymm
      | apply OrderIso.sumLexCongr
      | apply OrderIso.prodCongr)
    <;> orderCongr $[[$arg,*]]?
  )

structure OrderCalcRel where
  -- The relations to match (e.g. `OrderIso` or `InitialSeg`)
  relMatch : List Name
  -- The relation to use (e.g. `OrderIso` or `initalSegRel`)
  rel : Name
  -- The proof of reflexivity
  rfl : Name
  -- The proof of transitivity
  trans : Name

abbrev initialSegRefl (α) [LT α] : α ≤i α := InitialSeg.refl (· < ·)
abbrev initialSegRel (α) (β) [LT α] [LT β] := α ≤i β

def registeredOrderCalcRel : List OrderCalcRel := [
  ⟨[``OrderIso], ``OrderIso, ``OrderIso.refl, ``OrderIso.trans⟩,
  ⟨[``InitialSeg, ``initialSegRel], ``initialSegRel, ``initialSegRefl, ``InitialSeg.trans⟩,
]

def isOrderIso (e : Expr) : Bool := e.isAppOf ``OrderIso

def getOrderCalcRelation? (e : Expr) : MetaM (Option (OrderCalcRel × Expr × Expr)) := do
  let some orderCalcRel := registeredOrderCalcRel.find? (·.relMatch.any e.isAppOf) |
    return none
  return (orderCalcRel, e.getAppArgs[0]!, e.getAppArgs[1]!)

def mkOrderCalcFirstStepView (step0 : TSyntax ``calcFirstStep) (rel : OrderCalcRel) : TermElabM CalcStepView :=
  withRef step0 do
  match step0  with
  | `(calcFirstStep| $term:term) =>
    return {
      ref := step0,
      term := ← `($(mkIdent rel.rel) $term $term),
      proof := ← `($(mkIdent rel.rfl) _)
    }
  | `(calcFirstStep| $term := $proof) => return { ref := step0, term, proof}
  | _ => throwUnsupportedSyntax

def mkOrderCalcStepViews (steps : TSyntax ``calcSteps) (targetType : Expr) :
    TermElabM (Array CalcStepView) :=
  match steps with
  | `(calcSteps|
        $step0:calcFirstStep
        $rest*) => do
    let some (rel, _, _) := ← getOrderCalcRelation? targetType |
      throwError "target is not an 'orderCalc' relation"
    let mut steps := #[← mkOrderCalcFirstStepView step0 rel]
    for step in rest do
      let `(calcStep| $term := $proof) := step | throwUnsupportedSyntax
      steps := steps.push { ref := step, term, proof }
    return steps
  | _ => throwUnsupportedSyntax

def mkOrderCalcTrans (result step : Expr) (rel : OrderCalcRel) : MetaM (Expr × Expr) := do
  let result := ←mkAppM rel.trans #[result, step]
  let resultType := (← instantiateMVars (← inferType result)).headBeta
  unless (← getOrderCalcRelation? resultType).isSome do
    throwError "invalid 'calc' step, step result is not a relation{indentExpr resultType}"
  return (result, resultType)

def elabOrderCalcSteps (steps : Array CalcStepView) : TermElabM (Expr × Expr) := do
  let mut result? := none
  let mut prevRhs? := none
  for step in steps do
    let type ← elabType <| ← do
      if let some prevRhs := prevRhs? then
        annotateFirstHoleWithType step.term (←inferType prevRhs)
      else
        pure step.term
    let some (rel, lhs, rhs) ← getOrderCalcRelation? type |
      throwErrorAt step.term "invalid 'calc' step, relation expected{indentExpr type}"
    if let some prevRhs := prevRhs? then
      unless (← isDefEqGuarded lhs prevRhs) do
        throwErrorAt step.term "\
          invalid 'calc' step, left-hand side is{indentD m!"{lhs} : {← inferType lhs}"}\n\
          but previous right-hand side is{indentD m!"{prevRhs} : {← inferType prevRhs}"}"
    let proof ← withFreshMacroScope do elabTermEnsuringType step.proof type
    result? := some <| ← do
      if let some (result, _resultType) := result? then
        synthesizeSyntheticMVarsUsingDefault
        withRef step.term do mkOrderCalcTrans result proof rel
      else
        pure (proof, type)
    prevRhs? := rhs
  synthesizeSyntheticMVarsUsingDefault
  return result?.get!

elab "orderCalc" steps:calcSteps : tactic =>
    closeMainGoalUsing `orderCalc (checkNewUnassigned := false) fun target tag => do
    withTacticInfoContext steps do
      let target := (← instantiateMVars target).consumeMData
      let steps ← mkOrderCalcStepViews steps target

      let (val, mvarIds) ← withCollectingNewGoalsFrom (parentTag := tag) (tagSuffix := `orderCalc) <| runTermElab do
        let (val, valType) ← elabOrderCalcSteps steps
        if (← isDefEq valType target) then
          -- Immediately the right type, no need for further processing.
          return val

        -- Failed
        Term.ensureHasTypeWithErrorMsgs target val
          (mkImmedErrorMsg := fun _ => Term.throwCalcFailure steps)
          (mkErrorMsg := fun _ => Term.throwCalcFailure steps)
      pushGoals mvarIds
      return val

example [LinearOrder A] [LinearOrder B] [LinearOrder C] [LinearOrder D]
    (h : C ≃o D) : (A ⊕ₗ B) ⊕ₗ C ≃o A ⊕ₗ B ⊕ₗ D := by
  orderCalc (A ⊕ₗ B) ⊕ₗ C
  _ ≃o A ⊕ₗ B ⊕ₗ C := by orderCongr
  _ ≃o A ⊕ₗ B ⊕ₗ D := by orderCongr

example [LinearOrder A] [LinearOrder B] [LinearOrder C] [LinearOrder D]
    (h1 : C ≤i D) (h2 : A ≤i C) : A ≤i D := by
  orderCalc A
  _ ≤i C := h2
  _ ≤i D := h1
