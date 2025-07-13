import Lean
import AutLinOrd.Embeddings.OrderIso

open Lean Elab Command Term Meta Tactic

def sumLeft [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : A ⊕ₗ B ≃o A ⊕ₗ C := OrderIso.sumLexCongr (OrderIso.refl A) h

def sumRight [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : B ⊕ₗ A ≃o C ⊕ₗ A := OrderIso.sumLexCongr h (OrderIso.refl A)

def prodLeft [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : A ×ₗ B ≃o A ×ₗ C := OrderIso.prodCongr (OrderIso.refl A) h

def prodRight [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (h : B ≃o C) : B ×ₗ A ≃o C ×ₗ A := OrderIso.prodCongr h (OrderIso.refl A)

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
      | apply OrderIso.sumLexCongr
      | apply OrderIso.prodCongr)
    <;> orderCongr $[[$arg,*]]?
  )

def mkOrderCalcFirstStepView (step0 : TSyntax ``calcFirstStep) : TermElabM CalcStepView :=
  withRef step0 do
  match step0  with
  | `(calcFirstStep| $term:term)      =>
    return { ref := step0, term := ← `($term ≃o $term), proof := ← ``(OrderIso.refl _)}
  | `(calcFirstStep| $term := $proof) => return { ref := step0, term, proof}
  | _ => throwUnsupportedSyntax

def mkOrderCalcStepViews (steps : TSyntax ``calcSteps) : TermElabM (Array CalcStepView) :=
  match steps with
  | `(calcSteps|
        $step0:calcFirstStep
        $rest*) => do
    let mut steps := #[← mkOrderCalcFirstStepView step0]
    for step in rest do
      let `(calcStep| $term := $proof) := step | throwUnsupportedSyntax
      steps := steps.push { ref := step, term, proof }
    return steps
  | _ => throwUnsupportedSyntax

def isOrderIso (e : Expr) : Bool := e.isAppOf ``OrderIso

def getOrderCalcRelation? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if isOrderIso e then
    return (e.appFn!, e.getAppArgs[0]!, e.getAppArgs[1]!)
  else
    return none

def mkOrderCalcTrans (result step : Expr) : MetaM (Expr × Expr) := do
  let result := ←mkAppM ``OrderIso.trans #[result, step]
  let resultType := (← instantiateMVars (← inferType result)).headBeta
  unless (← getOrderCalcRelation? resultType).isSome do
    throwError "invalid 'calc' step, step result is not a relation{indentExpr resultType}"
  return (result, resultType)

partial def replaceFirstHoleWithTerm (t replace : Term) : TermElabM Term :=
  -- The state is true if we should annotate the immediately next hole with the type.
  return ⟨← StateT.run' (go t) true⟩
where
  go (t : Syntax) := do
    unless ← get do return t
    match t with
    | .node _ ``Lean.Parser.Term.hole _ =>
      set false
      `($(⟨replace⟩))
    | .node i k as => return .node i k (← as.mapM go)
    | _ => set false; return t

def elabOrderCalcSteps (steps : Array CalcStepView) : TermElabM (Expr × Expr) := do
  let mut result? := none
  let mut prevRhs? := none
  for step in steps do
    let type ← elabType <| ← do
      if let some prevRhs := prevRhs? then
        annotateFirstHoleWithType step.term (←inferType prevRhs)
      else
        pure step.term
    let some (_rel, lhs, rhs) ← getOrderCalcRelation? type |
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
        withRef step.term do mkOrderCalcTrans result proof
      else
        pure (proof, type)
    prevRhs? := rhs
  synthesizeSyntheticMVarsUsingDefault
  return result?.get!

elab "orderCalc" steps:calcSteps : tactic =>
    closeMainGoalUsing `orderCalc (checkNewUnassigned := false) fun target tag => do
    withTacticInfoContext steps do
      let steps ← mkOrderCalcStepViews steps
      let target := (← instantiateMVars target).consumeMData

      let (val, mvarIds) ← withCollectingNewGoalsFrom (parentTag := tag) (tagSuffix := `orderCalc) <| runTermElab do
        let (val, valType) ← elabOrderCalcSteps steps
        if (← isDefEq valType target) then
          -- Immediately the right type, no need for further processing.
          return val

        -- Calc extension failed, so let's go back and mimic the `calc` expression
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
