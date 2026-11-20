# UPLC Thresher

Thresher optimizes Untyped Plutus Core written in any source language. It reads a textual UPLC program and emits another program with the same UPLC version. The optimizer and its checked rewrite rules are written in Lean 4.

## Run it

With [Elan](https://github.com/leanprover/elan) and Git installed:

```sh
lake build
lake env lean --run Main.lean input.uplc --stats > optimized.uplc
```

Use `--stats` for JSON on stderr with syntax node counts and rewrite counts. Node counts measure the AST. The benchmark encodes programs to measure Flat bytes.

The default profile traverses the entire AST. It cancels force/delay pairs, removes identity calls, folds integer arithmetic and comparisons on literals, simplifies known constructors and boolean branches, and inlines selected strict bindings with capture-avoiding substitution. It keeps unused arguments when evaluating them could fail, diverge, or emit a trace. The deep profile is covered by regression tests and independent evaluation.

## Run with a proof

```sh
lake env lean --run Main.lean input.uplc --certified-root > optimized.uplc
lake env lean --run Main.lean validator.uplc --literal-arity 1 > optimized.uplc
```

The certified profile applies four rules: force/delay cancellation, identity applied to a constant, addition of two integer literals, and case selection on a constructor without fields. The library returns the output term with a kernel-checked proof that the input and output CEK executions reach a common state. This implies preservation of exact halt values and errors, allowing different numbers of CEK steps.

With `--literal-arity N`, the pass enters exactly N leading lambdas. The proof covers every call supplying exactly N literal arguments, including Data constants. If the program has fewer leading lambdas, the pass returns the input. `--certified-root` operates at the program root.

The proof uses the pinned PlutusCoreBlaster CEK model. Its observations omit trace messages and execution budgets. The deep profile's recursion through arbitrary contexts still needs a compositional semantic proof. Both profiles currently use explicit rule tables in Lean.

## Test and benchmark

```sh
python test_optimizer.py --aiken /path/to/aiken --bench
```

The harness checks both sides against Aiken's evaluator, covers strict error cases, and compares encoded bytes and execution units. It also reports Aiken shrink when it is available for the fixture.

Example results with Aiken 1.1.24. These fixtures isolate specific rewrites and use one input each.

| Fixture | Flat bytes before → after | CPU before → after | Memory before → after |
| --- | ---: | ---: | ---: |
| Identity and force/delay wrappers | 220 → 10 | 5,029,308 → 229,308 | 30,902 → 902 |
| Delayed branches | 111 → 10 | 3,530,043 → 229,308 | 14,417 → 902 |
| Known constructor cases | 147 → 10 | 1,669,308 → 229,308 | 9,902 → 902 |

In a smoke check on 11 already-optimized CAPE Fibonacci and factorial scripts, Thresher produced no additional reductions. The table measures isolated rewrites on synthetic fixtures.
