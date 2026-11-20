import UplcOptimizer.ContextualRules
import UplcOptimizer.Sharing
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
  | .cache _ tail => (reference? term tail).map fun ref =>
      ⟨ref.forced, ref.index + 1, ref.found, ref.same⟩
  | .splitPair tail => (reference? term tail).map fun ref =>
      ⟨ref.forced, ref.index + 2, ref.found, ref.same⟩

private def substituteForced : Substitute := fun layout term => do
  let ref ← reference? term layout
  return ⟨.Var ref.index, by
    rcases ref with ⟨forced, index, found, same⟩
    change ScopedTermRel layout term (.Var index)
    rw [same]
    exact .reference forced index found⟩

private def bindAll (term : Term) (layout : Layout) : (builtins : List ForcedBuiltin) →
    Option { output : Term // ScopedTermRel layout term output }
  | [] => do
    let body ← rewriteShared? substituteForced layout term
    return ⟨body.output, body.proof⟩
  | forced :: rest => do
    let body ← bindAll term (.insert forced layout) rest
    return ⟨.Apply (.Lam body.val) forced.term, .hoist forced body.property⟩

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
  | selected => bindAll term .same selected

def hoistPolyBuiltin? (term : Term) : Option Term := (hoistResult term).map Subtype.val

@[uplc_contextual_rule] theorem hoistPolyBuiltin_sound : ContextualRule hoistPolyBuiltin? :=
  .ofChecked hoistResult

def_uplc_contextual_rules contextualRule

end UplcOptimizer.Deep
