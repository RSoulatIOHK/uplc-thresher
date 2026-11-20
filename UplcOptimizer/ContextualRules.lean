import UplcOptimizer.DeepCode

open Lean hiding Term
open Lean.Meta Lean.Elab Lean.Elab.Command

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term (Term)

/-- A checked matcher for rewrites that change the CEK environment layout. -/
def ContextualRule (matcher : Term → Option Term) : Prop :=
  ∀ input output, matcher input = some output → TermRel input output

initialize uplcContextualRuleAttr : TagAttribute ←
  registerTagAttribute `uplc_contextual_rule "register a contextually equivalent UPLC rewrite"
    (fun decl => do
      let .thmInfo theoremInfo ← getConstInfo decl
        | throwError "@[uplc_contextual_rule] requires a theorem"
      unless theoremInfo.type.isAppOfArity ``ContextualRule 1 do
        throwError "@[uplc_contextual_rule] theorem must conclude ContextualRule matcher"
      if (← collectAxioms decl).contains ``sorryAx then
        throwError "@[uplc_contextual_rule] theorem depends on sorryAx")

structure ContextualMatch (input : Term) where
  theoremName : String
  output : Term
  proof : TermRel input output

private def certifyMatch {matcher : Term → Option Term}
    (name : String) (rule : ContextualRule matcher)
    (term : Term) : Option (ContextualMatch term) :=
  match found : matcher term with
  | none => none
  | some output => some ⟨name, output, rule term output found⟩

/-- Generate a dispatcher from the visible contextual rule theorems. -/
elab "def_uplc_contextual_rules " name:ident : command => do
  let rules := taggedDeclarations uplcContextualRuleAttr (← getEnv)
  let term := mkIdent `term
  let mut body ← `(none)
  for rule in rules.reverse do
    let ruleName := quote rule.getString!
    body ← `(certifyMatch $ruleName $(mkIdent rule):ident $term:ident <|> $body)
  elabCommand (← `(def $name ($term:ident : PlutusCore.UPLC.Term.Term) :
    Option (ContextualMatch $term:ident) := $body))

end UplcOptimizer.Deep
