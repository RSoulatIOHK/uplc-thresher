import UplcOptimizer.ContextualRules
import PlutusCore.UPLC.Term.Instances

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

private structure Reference (layout : Layout) (term : Term) where
  forced : ForcedBuiltin
  index : Nat
  found : layout.hoistedAt index = some forced
  same : term = forced.term

private def reference? (term : Term) : (layout : Layout) → Option (Reference layout term)
  | .same => none
  | .keep tail => (reference? term tail).map fun ref =>
      ⟨ref.forced, ref.index + 1, ref.found, ref.same⟩
  | .insert forced tail =>
    if h : term = forced.term then
      some ⟨forced, 0, rfl, h⟩
    else
      (reference? term tail).map fun ref => ⟨ref.forced, ref.index + 1, ref.found, ref.same⟩

mutual
  private def shareBody (layout : Layout) (term : Term) :
      { output : Term // ScopedTermRel layout term output } :=
    if let some ref := reference? term layout then
      ⟨.Var ref.index, by
        rcases ref with ⟨forced, index, found, same⟩
        change ScopedTermRel layout term (.Var index)
        rw [same]
        exact .reference forced index found⟩
    else
      match term with
      | .Var index => ⟨.Var (layout.rename index), .var index⟩
      | .Const value => ⟨.Const value, .const value⟩
      | .Builtin builtin => ⟨.Builtin builtin, .builtin builtin⟩
      | .Error => ⟨.Error, .error⟩
      | .Lam body =>
        let result := shareBody layout.underBinder body
        ⟨.Lam result.val, .lam result.property⟩
      | .Delay body =>
        let result := shareBody layout body
        ⟨.Delay result.val, .delay result.property⟩
      | .Force body =>
        let result := shareBody layout body
        ⟨.Force result.val, .force result.property⟩
      | .Apply fn arg =>
        let fn := shareBody layout fn
        let arg := shareBody layout arg
        ⟨.Apply fn.val arg.val, .apply fn.property arg.property⟩
      | .Constr tag fields =>
        let result := shareChildren layout fields
        ⟨.Constr tag result.val, .constr tag result.property⟩
      | .Case scrutinee branches =>
        let result := shareBody layout scrutinee
        let arms := shareChildren layout branches
        ⟨.Case result.val arms.val, .case result.property arms.property⟩
  termination_by sizeOf term

  private def shareChildren (layout : Layout) (terms : List Term) :
      { output : List Term // ScopedTermsRel layout terms output } :=
    match terms with
    | [] => ⟨[], .nil⟩
    | term :: rest =>
      let head := shareBody layout term
      let tail := shareChildren layout rest
      ⟨head.val :: tail.val, .cons head.property tail.property⟩
  termination_by sizeOf terms
end

private def bindAll (term : Term) (layout : Layout) : (builtins : List ForcedBuiltin) →
    { output : Term // ScopedTermRel layout term output }
  | [] => shareBody layout term
  | forced :: rest =>
    let body := bindAll term (.insert forced layout) rest
    ⟨.Apply (.Lam body.val) forced.term, .hoist forced body.property⟩

private structure Uses where
  forced : ForcedBuiltin
  count : Nat := 1
  recursive : Bool := false

private def recordUse (forced : ForcedBuiltin) (recursive : Bool) : List Uses → List Uses
  | [] => [{ forced, recursive }]
  | use :: rest =>
    if use.forced.builtin == forced.builtin then
      { use with count := use.count + 1, recursive := use.recursive || recursive } :: rest
    else
      use :: recordUse forced recursive rest

/-- Recognize the ordinary UPLC self-application encoding of recursion. -/
private partial def selfApplied (index : Nat) : Term → Bool
  | .Lam body => selfApplied (index + 1) body
  | .Delay body | .Force body => selfApplied index body
  | .Apply (.Var fn) (.Var arg) => fn == index && arg == index
  | .Apply fn arg => selfApplied index fn || selfApplied index arg
  | .Constr _ fields => fields.any (selfApplied index)
  | .Case scrutinee branches => selfApplied index scrutinee || branches.any (selfApplied index)
  | _ => false

private partial def collectUses (term : Term) (recursive : Bool) (uses : List Uses) : List Uses :=
  if let some found := ForcedBuiltin.match? term then
    recordUse found.val recursive uses
  else
    match term with
    | .Lam body | .Delay body | .Force body => collectUses body recursive uses
    | .Apply fn (.Lam body) =>
      collectUses body (recursive || selfApplied 0 body) (collectUses fn recursive uses)
    | .Apply fn arg => collectUses arg recursive (collectUses fn recursive uses)
    | .Constr _ fields => fields.foldl (fun acc field => collectUses field recursive acc) uses
    | .Case scrutinee branches => branches.foldl (fun acc arm => collectUses arm recursive acc)
        (collectUses scrutinee recursive uses)
    | _ => uses

/-- A binding needs a lambda, application, and one force chain. A variable
    takes the place of each use. Also consider repeated evaluation inside an
    explicit self-application even when the syntax contains a single use. -/
private def profitable (use : Uses) : Bool :=
  use.recursive || use.count * use.forced.forces > use.forced.forces + 3

private def hoistResult (term : Term) : Option { output : Term // TermRel term output } :=
  match (collectUses term false []).filterMap (fun use => if profitable use then some use.forced else none) with
  | [] => none
  | selected => some (bindAll term .same selected)

def hoistPolyBuiltin? (term : Term) : Option Term := (hoistResult term).map Subtype.val

@[uplc_contextual_rule] theorem hoistPolyBuiltin_sound : ContextualRule hoistPolyBuiltin? := by
  intro input output matched
  unfold hoistPolyBuiltin? at matched
  cases result : hoistResult input with
  | none => simp [result] at matched
  | some checked =>
    simp only [result, Option.map_some, Option.some.injEq] at matched
    subst output
    exact checked.property

def_uplc_contextual_rules contextualRule

end UplcOptimizer.Deep
