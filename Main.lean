import UplcOptimizer

open Lean (Json toJson)
open PlutusCore.UPLC.Term
open UplcOptimizer

private def usage : String :=
  "Usage: uplc_opt INPUT [--stats] [--certified-root | --literal-arity N]\n" ++
    "INPUT is a textual UPLC program. The optimized program is written to stdout."

private structure Options where
  input : Option String := none
  stats : Bool := false
  certifiedArity : Option Nat := none

private def parseArgs (options : Options) : List String → Except String Options
  | [] => if options.input.isNone then .error "missing input file" else .ok options
  | "--stats" :: rest => parseArgs { options with stats := true } rest
  | "--certified-root" :: rest =>
      if options.certifiedArity.isSome then .error "choose one certified profile"
      else parseArgs { options with certifiedArity := some 0 } rest
  | "--literal-arity" :: value :: rest => do
      if options.certifiedArity.isSome then throw "choose one certified profile"
      let some arity := value.toNat? | throw "--literal-arity expects a natural number"
      parseArgs { options with certifiedArity := some arity } rest
  | ["--literal-arity"] => .error "--literal-arity expects a natural number"
  | input :: rest =>
      if input.startsWith "--" then .error s!"unknown option {input}"
      else if options.input.isSome then .error "expected exactly one input file"
      else parseArgs { options with input := some input } rest

private def statsJson (profile : String) (before after : Term) (stats : Stats) : Json :=
  Json.mkObj [
    ("profile", toJson profile),
    ("nodes_before", toJson (nodes before)),
    ("nodes_after", toJson (nodes after)),
    ("rewrites", toJson stats.rewrites),
    ("sweeps", toJson stats.sweeps),
    ("by_rule", Json.mkObj (stats.byRule.toList.map fun (name, count) => (name, toJson count)))]

private def run (options : Options) : IO Unit := do
  let inputPath := options.input.getD ""
  let input ← IO.FS.readFile inputPath
  let program ← IO.ofExcept (PlutusCore.UPLC.TextEncoding.programFromString input)
  let .Program version before := program
  let selection : Program × Stats × String :=
    if let some arity := options.certifiedArity then
      let certified := certifiedPrefix 1024 arity before
      let (body, count) := certified.val
      let profile := if arity == 0 then "certified-root" else "certified-prefix"
      (.Program version body, { rewrites := count }, profile)
    else
      let (optimized, stats) := optimize program
      (optimized, stats, "deep")
  let (output, stats, profile) := selection
  let .Program _ after := output
  let rendered ← IO.ofExcept (emitProgram output)
  IO.println rendered
  if options.stats then
    IO.eprintln (statsJson profile before after stats).compress

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then
    IO.println usage
    return 0
  match parseArgs {} args with
  | .error why =>
      IO.eprintln s!"uplc_opt: {why}\n{usage}"
      return 2
  | .ok options =>
      try
        run options
        return 0
      catch err =>
        IO.eprintln s!"uplc_opt: {err}"
        return 1
