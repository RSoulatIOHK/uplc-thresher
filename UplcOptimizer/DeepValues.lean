import UplcOptimizer.DeepScope

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.BuiltinFunctions.Evaluate
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

mutual
  /-- A term correspondence lifted to values and captured environments. -/
  inductive ValueRel (R : Layout → Term → Term → Prop) : CekValue → CekValue → Prop where
    | const {constant} : ValueRel R (.VCon constant) (.VCon constant)
    | lam {layout left right leftEnv rightEnv} :
        R layout.underBinder left right → EnvRel R layout leftEnv rightEnv →
        ValueRel R (.VLam left leftEnv) (.VLam right rightEnv)
    | delay {layout left right leftEnv rightEnv} :
        R layout left right → EnvRel R layout leftEnv rightEnv →
        ValueRel R (.VDelay left leftEnv) (.VDelay right rightEnv)
    | constr {tag left right} : ValueListRel R left right →
        ValueRel R (.VConstr tag left) (.VConstr tag right)
    | builtin {builtin left right expected} : ValueListRel R left right →
        ValueRel R (.VBuiltin builtin left expected) (.VBuiltin builtin right expected)

  inductive ValueListRel (R : Layout → Term → Term → Prop) : List CekValue → List CekValue → Prop where
    | nil : ValueListRel R [] []
    | cons {left right leftTail rightTail} :
        ValueRel R left right → ValueListRel R leftTail rightTail →
        ValueListRel R (left :: leftTail) (right :: rightTail)

  /-- Align each original environment slot with a target slot. Each added slot
  carries either the declared builtin value or a related projection result. -/
  inductive EnvRel (R : Layout → Term → Term → Prop) :
      Layout → List CekValue → List CekValue → Prop where
    | same : ValueListRel R left right → EnvRel R .same left right
    | keep : ValueRel R left right → EnvRel R layout leftTail rightTail →
        EnvRel R (.keep layout) (left :: leftTail) (right :: rightTail)
    | insert (forced : ForcedBuiltin) : EnvRel R layout left right →
        EnvRel R (.insert forced layout) left (forced.value :: right)
    | cache (expr : CacheExpr) : expr.eval left = some original → ValueRel R original result →
        EnvRel R layout left right → EnvRel R (.cache expr layout) left (result :: right)
end

inductive ValueOptionRel (R : Layout → Term → Term → Prop) : Option CekValue → Option CekValue → Prop where
  | none : ValueOptionRel R none none
  | some {left right} : ValueRel R left right → ValueOptionRel R (some left) (some right)

variable {R : Layout → Term → Term → Prop}

theorem ValueListRel.lookup {left right} (related : ValueListRel R left right) (index : Nat) :
    ValueOptionRel R left[index]? right[index]? := by
  match related, index with
  | .nil, _ => exact .none
  | .cons head _, 0 => exact .some head
  | .cons _ tail, index + 1 => exact tail.lookup index

theorem ValueListRel.length {left right} (related : ValueListRel R left right) :
    left.length = right.length := by
  match related with
  | .nil => rfl
  | .cons _ tail => simp only [List.length_cons, tail.length]

theorem ValueListRel.append {left right leftTail rightTail} (related : ValueListRel R left right)
    (tail : ValueListRel R leftTail rightTail) :
    ValueListRel R (left ++ leftTail) (right ++ rightTail) := by
  match related with
  | .nil => exact tail
  | .cons head rest => exact .cons head (rest.append tail)

theorem ValueListRel.reverse {left right} (related : ValueListRel R left right) :
    ValueListRel R left.reverse right.reverse := by
  match related with
  | .nil => exact .nil
  | .cons head tail =>
    rw [List.reverse_cons, List.reverse_cons]
    exact tail.reverse.append (.cons head .nil)

theorem EnvRel.push {layout left right x y} (related : EnvRel R layout left right)
    (heads : ValueRel R x y) : EnvRel R layout.underBinder (x :: left) (y :: right) := by
  cases related with
  | same values => exact .same (.cons heads values)
  | keep values tail => exact .keep heads (.keep values tail)
  | insert forced tail => exact .keep heads (.insert forced tail)
  | cache expr evaluated values tail => exact .keep heads (.cache expr evaluated values tail)

theorem EnvRel.lookup {layout left right} (related : EnvRel R layout left right) (index : Nat) :
    ValueOptionRel R left[index]? right[layout.rename index]? := by
  match related, index with
  | .same values, idx => exact values.lookup idx
  | .keep values _, 0 => exact .some values
  | .keep _ tail, idx + 1 => exact tail.lookup idx
  | .insert _ tail, idx => exact tail.lookup idx
  | .cache _ _ _ tail, idx => exact tail.lookup idx

theorem EnvRel.hoistedLookup {layout left right index forced}
    (related : EnvRel R layout left right) (selected : layout.hoistedAt index = some forced) :
    right[index]? = some forced.value := by
  match related, index with
  | .same _, _ => simp [Layout.hoistedAt] at selected
  | .keep _ _, 0 => simp [Layout.hoistedAt] at selected
  | .keep _ tail, _ + 1 => exact tail.hoistedLookup selected
  | .insert builtin _, 0 =>
    change some builtin = some forced at selected
    cases Option.some.inj selected
    rfl
  | .insert _ tail, _ + 1 => exact tail.hoistedLookup selected
  | .cache _ _ _ _, 0 => simp [Layout.hoistedAt] at selected
  | .cache _ _ _ tail, _ + 1 => exact tail.hoistedLookup selected

theorem EnvRel.cachedLookup {layout left right index expr}
    (related : EnvRel R layout left right) (selected : layout.cachedAt index = some expr) :
    ∃ original result, expr.eval left = some original ∧ right[index]? = some result ∧
      ValueRel R original result := by
  match related, index with
  | .same _, _ => simp [Layout.cachedAt] at selected
  | .keep _ _, 0 => simp [Layout.cachedAt] at selected
  | .keep _ tail, _ + 1 =>
    simp only [Layout.cachedAt, Option.map_eq_some_iff] at selected
    obtain ⟨stored, found, rfl⟩ := selected
    obtain ⟨original, result, evaluated, lookup, values⟩ := tail.cachedLookup found
    exact ⟨original, result, by simpa only [CacheExpr.eval_shift] using evaluated, lookup, values⟩
  | .insert _ _, 0 => simp [Layout.cachedAt] at selected
  | .insert _ tail, _ + 1 => exact tail.cachedLookup selected
  | .cache cached evaluated values _, 0 =>
    change some cached = some expr at selected
    cases Option.some.inj selected
    exact ⟨_, _, evaluated, rfl, values⟩
  | .cache _ _ _ tail, _ + 1 => exact tail.cachedLookup selected

private theorem ValueOptionRel.bindSame {α : Type} (input : Option α)
    {left right : α → Option CekValue}
    (related : ∀ value, ValueOptionRel R (left value) (right value)) :
    ValueOptionRel R (input.bind left) (input.bind right) := by
  cases input with
  | none => exact .none
  | some value => exact related value

private theorem ValueOptionRel.mapSame {α : Type} (input : Option α)
    {left right : α → CekValue}
    (related : ∀ value, ValueRel R (left value) (right value)) :
    ValueOptionRel R (input.map left) (input.map right) := by
  cases input with
  | none => exact .none
  | some value => exact .some (related value)

open Lean Meta Elab Tactic in
private partial def countValueArguments (args : Expr) : MetaM Nat := do
  let args ← whnf args
  let fields := args.getAppArgs
  let count := if (← whnf fields[0]!).isConstOf ``ExpectedBuiltinArg.ArgV then 1 else 0
  if args.getAppFn.isConstOf ``ExpectedBuiltinArgs.More then
    return count + (← countValueArguments fields[1]!)
  return count

open Lean Meta Elab Tactic in
private def closeSimpleBuiltin : TacticM Bool := do
  let saved ← saveState
  let done ← withoutRecover <| tryTactic (evalTactic (← `(tactic|
    first
    | exact ValueOptionRel.none
    | exact ValueOptionRel.some ValueRel.const
    | exact ValueOptionRel.some (by assumption))))
  unless done do saved.restore
  return done

open Lean Meta Elab Tactic in
private partial def proveBuiltinResult (fuel : Nat := 15) : TacticM Unit := do
  if ← closeSimpleBuiltin then return
  evalTactic (← `(tactic| try simp_all [Option.bind, Option.map, Function.comp_def]))
  if (← getGoals).isEmpty then return
  if ← closeSimpleBuiltin then return
  if fuel == 0 then throwError "too many cases proving the builtin result: {← getMainTarget}"
  let target ← getMainTarget
  let subgoals ← evalTacticAt (← `(tactic|
    first
    | apply ValueOptionRel.bindSame
      intro value
    | exact ValueOptionRel.mapSame _ (fun _ => ValueRel.const)
    | split)) (← getMainGoal)
  for subgoal in subgoals do
    setGoals [subgoal]
    if (← getMainTarget) == target then
      throwError "builtin result proof did not progress: {target}"
    proveBuiltinResult (fuel - 1)
  setGoals []

open Lean Meta Elab Tactic in
private partial def proveBuiltinInputs (heads : List Expr) : TacticM Unit := do
  if ← closeSimpleBuiltin then return
  match heads with
  | [] => proveBuiltinResult
  | head :: rest =>
    for branch in ← (← getMainGoal).cases head.fvarId! do
      setGoals [branch.mvarId]
      proveBuiltinInputs (rest.map branch.subst.apply)
    setGoals []

open Lean Meta Elab Tactic in
private partial def proveBuiltinArguments (selector : Bool) (remaining : Nat) (tail : Expr)
    (heads : List Expr) : TacticM Unit := do
  for branch in ← (← getMainGoal).cases tail.fvarId! do
    setGoals [branch.mvarId]
    let heads := heads.map branch.subst.apply
    if branch.ctorName == ``ValueListRel.nil then
      proveBuiltinInputs (if selector && remaining == 0 then heads.take 1 else heads.reverse)
    else
      let head := branch.fields[branch.fields.size - 2]!
      let tail := branch.fields.back!
      if remaining == 0 then
        proveBuiltinInputs (if selector then heads.take 1 else (head :: heads).reverse)
      else
        proveBuiltinArguments selector (remaining - 1) tail (head :: heads)
  setGoals []

open Lean Meta Elab Tactic in
private def evalRelatedBuiltin (related : FVarId) : TacticM Unit := withMainContext do
  let builtin := (← getMainTarget).getAppArgs[1]!.getAppArgs[1]!
  let expected ← mkAppM ``expectedArgs #[builtin]
  let arity ← countValueArguments expected
  let selectors := [``BuiltinFun.IfThenElse, ``BuiltinFun.ChooseUnit, ``BuiltinFun.Trace,
    ``BuiltinFun.ChooseList, ``BuiltinFun.ChooseData]
  evalTactic (← `(tactic| simp only [evaluateBuiltinFunction]))
  let implementation := (← getMainTarget).getAppArgs[1]!.getAppFn.constName!
  evalTactic (← `(tactic| unfold $(mkIdent implementation)))
  evalTactic (← `(tactic| try simp only [PlutusCore.UPLC.BuiltinFunctions.Utils.tryCatchSome, Option.map, Option.bind,
    Except.toOption, Function.comp_def, PlutusCore.Bool.ifThenElse, PlutusCore.Unit.chooseUnit,
    PlutusCore.Trace.trace]))
  proveBuiltinArguments (selectors.contains builtin.constName!) arity (.fvar related) []

open Lean Meta Elab Tactic in
elab "prove_builtin_relation " related:ident : tactic => withMainContext do
  withoutRecover <| evalRelatedBuiltin (← getFVarId related)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
/-- Related arguments preserve the result of every builtin. The polymorphic
selectors return related input values, while other builtins compute from
equal constant payloads or fail in both runs. -/
theorem builtin_related (variant : BuiltinSemanticsVariant) (builtin : BuiltinFun)
    {inputs outputs} (related : ValueListRel R inputs outputs) :
    ValueOptionRel R (evaluateBuiltinFunction variant builtin inputs)
      (evaluateBuiltinFunction variant builtin outputs) := by
  cases builtin <;> prove_builtin_relation related

end UplcOptimizer.Deep
