# UPLC Thresher

Thresher optimizes Untyped Plutus Core written in any source language. It reads a textual UPLC program and emits another program with the same UPLC version. The optimizer and its checked rewrite rules are written in Lean 4.

## Run it

With [Elan](https://github.com/leanprover/elan) and Git installed:

```sh
lake build
lake env lean --run Main.lean input.uplc --stats > optimized.uplc
```

Use `--stats` for JSON on stderr with syntax node counts and rewrite counts. Node counts measure the AST. The benchmark encodes programs to measure Flat bytes.

The default profile traverses the entire AST and applies only tagged theorems. It cancels force/delay pairs, including when the force surrounds an exactly saturated lambda application whose body starts with a delay. Other rules remove identity calls on immediate values, fold integer arithmetic and comparisons on literals, select nullary constructor cases and delayed boolean branches, and propagate errors through strict positions. After the deep traversal, the optimizer shares fully forced builtins in fresh outer bindings. The selector considers repeated uses and occurrences in explicit self-application loops.

## Proof of the deep optimizer

`optimizeWithProof` returns the optimized program with a Lean proof. `optimize_preserves` states the same guarantee for the `optimize` function used by the CLI. For every UPLC context, argument list, and builtin semantics variant, the input and output have the same unmetered observations under the pinned PlutusCoreBlaster CEK evaluator. These observations include successful termination, evaluation errors, and the exact literal constant returned. A context can observe a returned closure by applying it or a returned delay by forcing it.

The proof uses a CEK simulation through related terms, closures, environments, and continuation frames, including the builtin evaluator. Fuel can differ between executions. Trace messages and CPU/memory budgets are outside the theorem.

## Root-only and fixed-arity modes

```sh
lake env lean --run Main.lean input.uplc --certified-root > optimized.uplc
lake env lean --run Main.lean validator.uplc --literal-arity 1 > optimized.uplc
```

The certified profile applies four rules: force/delay cancellation, identity applied to a constant, addition of two integer literals, and case selection on a constructor without fields. The library returns the output term with a kernel-checked proof that the input and output CEK executions reach a common state. This implies preservation of exact halt values and errors, allowing different numbers of CEK steps.

With `--literal-arity N`, the pass enters exactly N leading lambdas. The proof covers every call supplying exactly N literal arguments, including Data constants. If the program has fewer leading lambdas, the pass returns the input. `--certified-root` operates at the program root.

## Add a proved rewrite

For local deep rewrites, tag a `StepRule lhs rhs` theorem with `@[uplc_deep_rule]`. Each rule proves that the source reaches the head state of its replacement in a positive number of CEK steps under any continuation and environment. `def_uplc_deep_rules myRules` generates the dispatcher, which can be passed to `Deep.optimizeTerm myRules`. The standard local rules are in `UplcOptimizer/DeepRules.lean`.

Builtin hoisting is registered with `@[uplc_contextual_rule]`. Its theorem certifies every output of its matcher. The CEK simulation tracks the new environment slots and how existing de Bruijn indices move. Each hoisted force chain must stop at a builtin value before any term argument is applied. See `UplcOptimizer/PolyBuiltin.lean`.

Saturated force/delay cancellation also uses `@[uplc_contextual_rule]`. Its proof follows the original left-to-right argument evaluation, including arguments that fail or diverge. The final argument takes both executions into the same body with the same binder correspondence. See `UplcOptimizer/ForceDelay.lean`.

The delayed `ifThenElse` rule removes the outer force and one delay from each arm when both arm bodies are constants, lambdas, or delays. Evaluating these immediate forms produces values without running lambda or delay bodies. The proof follows evaluation of the condition, then relates selection of the same arm or failure on a non-boolean condition. The optimizer tries this rule after local simplifications, including selection on a known boolean, and before fully forced builtin hoisting. See `UplcOptimizer/ForceIf.lean`.

For UPLC 1.1 and later, ApplyToCase packs three or more arguments into a constructor and applies the function through a case. One tagged rule accepts a syntactic lambda prefix with at least as many binders as arguments. The other accepts a fully forced `ifThenElse` with an arbitrary condition and immediate value arms. The rules run before builtin hoisting, while the literal conditional head is still visible. See `UplcOptimizer/ApplyToCase.lean`.

Use fully applied constructors and literals in the left-hand side and capture each data parameter once. Theorems can include decidable premises on those parameters. If a premise fails, the dispatcher tries the next candidate. Candidates are tried in deterministic Lean name order.

The root-only optimizer uses `@[uplc_rule]` for `CekJoin lhs rhs` theorems in `UplcOptimizer/LocalProofs.lean`. `def_uplc_rules myRules` and `certifiedRootWith myRules` provide the corresponding extension points.

## Test and benchmark

```sh
lake env lean Tests/TaggedRules.lean
lake env lean Tests/DeepBehavior.lean
lake env lean Tests/PolyBuiltin.lean
lake env lean Tests/ForceDelay.lean
lake env lean Tests/ForceIf.lean
lake env lean Tests/ApplyToCase.lean
python test_optimizer.py --aiken /path/to/aiken --bench
```

The harness checks both sides against Aiken's evaluator, covers strict error cases, and compares encoded bytes and execution units. It also reports Aiken shrink when it is available for the fixture.

Example results with Aiken 1.1.24. These fixtures isolate specific rewrites and use one input each.

| Fixture | Flat bytes before → after | CPU before → after | Memory before → after |
| --- | ---: | ---: | ---: |
| Identity and force/delay wrappers | 220 → 160 | 5,029,308 → 3,109,308 | 30,902 → 18,902 |
| Delayed branches | 111 → 10 | 3,530,043 → 229,308 | 14,417 → 902 |
| Known constructor cases with fields | 147 → 147 | 1,669,308 → 1,669,308 | 9,902 → 9,902 |

The wrapper fixture still contains calls to an identity lambda with a computing argument. The case fixture needs a rule that preserves evaluation of nonempty constructor fields. The previous handwritten pass optimized both fixtures to 10 bytes.
