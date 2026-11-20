import Lean
import PlutusCore.UPLC.Term

open Lean Meta Elab Command Parser.Term

namespace UplcOptimizer

private structure RulePattern where
  pattern : Term
  used : Array FVarId

private partial def makePattern (variables : Array (FVarId × Ident)) (expr : Expr)
    (used : Array FVarId := #[]) : MetaM RulePattern := do
  let expr := expr.consumeMData
  if let .fvar fvar := expr then
    let some (_, ident) := variables.find? (fun pair => pair.1 == fvar)
      | throwError "unexpected variable in left-hand side: {expr}"
    if used.contains fvar then
      throwError "repeated variable in left-hand side: {expr}"
    return ⟨ident, used.push fvar⟩
  if let some n ← getNatValue? expr then
    unless ← isDefEq expr (mkNatLit n) do
      throwError "nonstandard natural literal in left-hand side: {expr}"
    return ⟨quote n, used⟩
  if let some i ← getIntValue? expr then
    unless ← isDefEq expr (mkIntLit i) do
      throwError "nonstandard integer literal in left-hand side: {expr}"
    let magnitude : Term := quote i.natAbs
    let numeral ← if i < 0 then `(-$magnitude) else pure magnitude
    return ⟨numeral, used⟩
  if let some s := getStringValue? expr then
    return ⟨quote s, used⟩
  let .const head _ := expr.getAppFn
    | throwError "expected a constructor pattern, variable or literal, found {expr}"
  let .ctorInfo ctor ← getConstInfo head
    | throwError "expected a constructor pattern, variable or literal, found {expr}"
  let args := expr.getAppArgs
  unless args.size == ctor.numParams + ctor.numFields do
    throwError "constructor pattern must be fully applied: {expr}"
  let mut patterns := #[]
  for _ in [:ctor.numParams] do
    patterns := patterns.push (← `(_))
  let mut used := used
  for field in args[ctor.numParams...*] do
    let sub ← makePattern variables field used
    patterns := patterns.push sub.pattern
    used := sub.used
  let pattern ← `(@$(mkIdent head):ident $patterns:term*)
  return ⟨pattern, used⟩

private def makeRule (relation : Name) (decl : Name) : MetaM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let .thmInfo theoremInfo ← getConstInfo decl
    | throwError "@[uplc_rule] requires a theorem"
  forallTelescope theoremInfo.type fun binders conclusion => do
    unless conclusion.isAppOfArity relation 2 do
      if relation == `UplcOptimizer.CekJoin then
        throwError "@[uplc_rule] theorem must conclude CekJoin lhs rhs"
      else
        throwError "@[uplc_deep_rule] theorem must conclude StepRule lhs rhs"
    let lhs := conclusion.getAppArgs[0]!
    let .const root _ := lhs.getAppFn
      | throwError "@[uplc_rule] requires a constructor at the head of its left-hand side"
    let .ctorInfo _ ← getConstInfo root
      | throwError "@[uplc_rule] requires a constructor at the head of its left-hand side"
    let variables ← binders.mapM fun binder =>
      return (binder.fvarId!, mkIdent (← mkFreshUserName `arg))
    let matched ← makePattern variables lhs
    let mut guards := #[]
    for (fvar, ident) in variables do
      unless matched.used.contains fvar do
        let proposition ← inferType (mkFVar fvar)
        unless ← isProp proposition do
          throwError "@[uplc_rule] data binder must occur in the left-hand side: {mkFVar fvar}"
        let .some _ ← trySynthInstance (mkApp (mkConst ``Decidable) proposition)
          | throwError "@[uplc_rule] premise needs a Decidable instance: {proposition}"
        guards := guards.push ident
    let arguments := variables.map fun (_, ident) => (ident : Term)
    let proof ← `(@$(mkIdent decl):ident $arguments:term*)
    let mut rhs ← `(some ⟨_, $proof⟩)
    for guard in guards.reverse do
      rhs ← `(if $guard:ident : _ then $rhs else none)
    `(matchAltExpr| | $matched.pattern => $rhs)

/-- Tag a theorem `CekJoin lhs rhs` for subsequent `def_uplc_rules` declarations.
The left-hand side is built from constructors, literals, and distinct data
variables. Additional premises must be decidable from those variables. -/
initialize uplcRuleAttr : TagAttribute ←
  registerTagAttribute `uplc_rule "register a CEK-checked UPLC rewrite theorem"
    (fun decl => do
      discard <| MetaM.run' (makeRule `UplcOptimizer.CekJoin decl)
      if (← collectAxioms decl).contains ``sorryAx then
        throwError "@[uplc_rule] theorem depends on sorryAx")

/-- Tag a theorem proving a positive local CEK transition for the deep pass. -/
initialize uplcDeepRuleAttr : TagAttribute ←
  registerTagAttribute `uplc_deep_rule "register a UPLC head reduction for the verified traversal"
    (fun decl => do
      discard <| MetaM.run' (makeRule `UplcOptimizer.Deep.StepRule decl)
      if (← collectAxioms decl).contains ``sorryAx then
        throwError "@[uplc_deep_rule] theorem depends on sorryAx")

def taggedDeclarations (attr : TagAttribute) (env : Environment) : Array Name := Id.run do
  let mut names := (attr.ext.getState env).toArray
  for moduleName in env.allImportedModuleNames do
    if let some index := env.getModuleIdx? moduleName then
      names := names ++ attr.ext.getModuleEntries env index
  return names.qsort Name.quickLt

private def defineRules (attr : TagAttribute) (relationName : Name) (name : Ident) : CommandElabM Unit := do
  let rules := taggedDeclarations attr (← getEnv)
  let alternatives : Array (TSyntax ``matchAlt) ← liftTermElabM do
    rules.mapM fun decl => do
      return (← makeRule relationName decl)
  let fallback ← `(matchAltExpr| | _ => none)
  let term := mkIdent `term
  let termType := mkIdent ``PlutusCore.UPLC.Term.Term
  let relation := mkIdent relationName
  let motive ← `((candidate : $termType) → Option { result : $termType // $relation candidate result })
  let mut matcher ← `(none)
  for alternative in alternatives.reverse do
    let cases := #[alternative, (fallback : TSyntax ``matchAlt)]
    let attempt ← `(match (motive := $motive) $term:ident with $cases:matchAlt*)
    matcher ← `($attempt <|> $matcher)
  elabCommand (← `(def $name ($term:ident : $termType) :
    Option { result : $termType // $relation $term:ident result } := $matcher))

/-- Try the visible tagged head-join theorems in deterministic Lean name order. -/
elab "def_uplc_rules " name:ident : command =>
  defineRules uplcRuleAttr `UplcOptimizer.CekJoin name

/-- Generate the proof-producing steps of the verified deep optimizer. -/
elab "def_uplc_deep_rules " name:ident : command =>
  defineRules uplcDeepRuleAttr `UplcOptimizer.Deep.StepRule name

end UplcOptimizer
