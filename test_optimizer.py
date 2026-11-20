#!/usr/bin/env python3
"""Run UPLC optimizer integration tests and compare costs with Aiken."""

import argparse
import dataclasses
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


PROJECT = Path(__file__).resolve().parent
EVAL_FAILURE = re.compile(r"\bCosts\s*-+\s*cpu:\s*\d+\s*memory:\s*\d+", re.I)


class CheckFailure(Exception):
    pass


@dataclasses.dataclass(frozen=True)
class Case:
    name: str
    term: str
    observations: tuple[tuple[tuple[int, ...], int | None], ...]
    must_shrink: bool = False
    version: str = "1.1.0"
    literal_arity: int | None = None

    @property
    def program(self):
        return f"(program {self.version} {self.term})\n"


def shrink_wrappers(term, count):
    for index in range(count):
        term = f"(force (delay [(lam id{index} id{index}) {term}]))"
    return term


def select_delayed(term, alternative):
    return (
        "(force [[[(force (builtin ifThenElse)) (con bool True)] "
        f"(delay {term})] (delay {alternative})])"
    )


def regression_cases():
    division = "[[(builtin divideInteger) (con integer 12)] x]"
    return (
        Case("force-delay-root", "(force (delay (con integer 7)))", (((), 7),),
             must_shrink=True, version="1.0.0", literal_arity=0),
        Case("certified-literal-prefix", "(lam x (lam y (force (delay [[(builtin addInteger) x] y]))))",
             (((3, 4), 7), ((-2, 4), 2)), must_shrink=True, literal_arity=2),
        Case("strict-identity", f"(lam x [(lam y y) {division}])",
             (((2,), 6), ((0,), None)), must_shrink=True),
        Case("deep-wrappers", f"(lam x {shrink_wrappers(division, 24)})",
             (((3,), 4), ((0,), None)), must_shrink=True),
        Case("unused-error", "[(lam unused (con integer 7)) (error)]", (((), None),)),
        # The unselected argument is still evaluated in this upstream regression.
        Case("eager-if", "(lam x [[[(force (builtin ifThenElse)) (con bool True)] "
             f"(con integer 1)] {division}])", (((0,), None), ((1,), 1))),
        Case("delayed-if", f"(lam x {select_delayed('(con integer 7)', division)})",
             (((0,), 7), ((1,), 7))),
        Case("strict-unused-binding", f"(lam x [(lam unused (con integer 7)) {division}])",
             (((0,), None), ((1,), 7))),
        Case("strict-single-use", f"(lam x [(lam y [[(builtin addInteger) y] (con integer 3)]) {division}])",
             (((0,), None), ((2,), 9)), must_shrink=True),
        Case("strict-use-under-lambda", f"(lam x [(lam y (lam unused y)) {division}])",
             (((0,), None), ((2, 0), 6))),
        Case("strict-constructor-fields", f"(lam x (case (constr 0 (con integer 7) {division}) "
             "(lam a (lam b a))))", (((0,), None), ((1,), 7))),
        Case("capture-avoidance", "(lam outer [[(lam y (lam shadow [y (con integer 41)])) "
             "(lam ignored outer)] (con integer 99)])", (((13,), 13), ((-9,), -9))),
        Case("capture-safe-inlining", "(lam outer [[(lam y (lam shadow y)) outer] (con integer 99)])",
             (((13,), 13), ((-9,), -9)), must_shrink=True),
        Case("shadowed-argument", "(lam x [(lam x [(lam y y) x]) (con integer 2)])",
             (((13,), 2),)),
        Case("typed-list-constant", "[(force (builtin headList)) (con (list integer) [5, 6])]",
             (((), 5),)),
        Case("byte-string-constant", "[(builtin lengthOfByteString) (con bytestring #00117fff)]",
             (((), 4),)),
        Case("escaped-string-constant", r'[(builtin lengthOfByteString) [(builtin encodeUtf8) '
             r'(con string "a\\b\"c")]]', (((), 5),)),
        Case("data-constant", "[(builtin unIData) (con data (I -42))]", (((), -42),)),
    )


def benchmark_cases():
    arithmetic = "[[(builtin addInteger) x] (con integer 9)]"
    delayed = arithmetic
    for _ in range(15):
        delayed = select_delayed(delayed, "(error)")
    constructors = arithmetic
    for index in range(15):
        constructors = (f"(case (constr 0 (con integer {index}) (con integer 88)) "
                        f"(lam a{index} (lam b{index} {constructors})))")
    return (
        Case("wrappers-60", f"(lam x {shrink_wrappers(arithmetic, 60)})", (((4,), 13),)),
        Case("delayed-branches-15", f"(lam x {delayed})", (((4,), 13),)),
        Case("constructor-cases-15", f"(lam x {constructors})", (((4,), 13),)),
    )


def resolve_command(command):
    path = Path(command)
    if path.is_file():
        return str(path.resolve())
    found = shutil.which(command)
    if found is not None:
        return found
    raise CheckFailure(f"command not found: {command}")


def run(command, *, allow_failure=False):
    try:
        process = subprocess.run(command, cwd=PROJECT, text=True, encoding="utf-8",
                                 capture_output=True, timeout=60, check=False)
    except subprocess.TimeoutExpired as error:
        raise CheckFailure(f"execution timed out: {subprocess.list2cmdline(command)}") from error
    if process.returncode and not allow_failure:
        raise CheckFailure(f"command failed ({process.returncode}): "
                           f"{subprocess.list2cmdline(command)}\n{process.stdout}{process.stderr}")
    return process


def optimized_file(optimizer, case, original, target):
    flags = ["--stats"]
    profile = "deep"
    if case.literal_arity == 0:
        flags.append("--certified-root")
        profile = "certified-root"
    elif case.literal_arity is not None:
        flags.extend(("--literal-arity", str(case.literal_arity)))
        profile = "certified-prefix"
    result = run([*optimizer, str(original), *flags])
    try:
        stats = json.loads(result.stderr)
        before = stats["nodes_before"]
        after = stats["nodes_after"]
        for key in ("rewrites", "profile"):
            if key not in stats:
                raise KeyError(key)
    except (ValueError, KeyError, TypeError) as error:
        raise CheckFailure(f"{case.name}: invalid optimizer stats\n{result.stderr}") from error
    if type(before) is not int or type(after) is not int or min(before, after) < 1:
        raise CheckFailure(f"{case.name}: invalid AST counts: {before!r}, {after!r}")
    if stats["profile"] != profile:
        raise CheckFailure(f"{case.name}: expected profile {profile}, got {stats['profile']!r}")
    if case.must_shrink and after >= before:
        raise CheckFailure(f"{case.name}: expected smaller AST, got {before} -> {after}")
    if not result.stdout.lstrip().startswith(f"(program {case.version}"):
        raise CheckFailure(f"{case.name}: optimizer did not emit a program of version {case.version}")
    target.write_text(result.stdout, encoding="utf-8")
    return before, after


def evaluate(aiken, script, arguments, *, flat=False):
    rendered_arguments = [f"(con integer {value})" for value in arguments]
    flags = ["--flat"] if flat else []
    outcome = run([aiken, "uplc", "eval", *flags, str(script), *rendered_arguments],
                  allow_failure=True)
    if outcome.returncode:
        diagnostics = f"{outcome.stdout}\n{outcome.stderr}"
        if EVAL_FAILURE.search(diagnostics):
            return None
        raise CheckFailure(f"Aiken failed to load {script.name}:\n{diagnostics}")
    try:
        value = json.loads(outcome.stdout)
        return value["result"], value["cpu"], value["mem"]
    except (ValueError, KeyError, TypeError) as error:
        raise CheckFailure(f"Aiken returned invalid evaluation JSON for {script.name}:\n"
                           f"{outcome.stdout}{outcome.stderr}") from error


def check_expected(case, filename, arguments, actual, expected):
    want = None if expected is None else f"(con integer {expected})"
    observed = None if actual is None else actual[0]
    if observed != want:
        raise CheckFailure(f"{case.name} {filename.name} on {arguments}: "
                           f"expected {want or 'evaluation failure'}, got {observed!r}")


def encode(aiken, script):
    return bytes.fromhex(run([aiken, "uplc", "encode", "--hex", str(script)]).stdout)


def benchmark_aiken(aiken, case, source, optimized, scratch):
    original_flat = encode(aiken, source)
    optimized_flat = encode(aiken, optimized)
    reference_input = scratch / f"{case.name}.hex"
    reference_input.write_text(original_flat.hex(), encoding="ascii")
    shrink = run([aiken, "uplc", "shrink", "--hex", str(reference_input)], allow_failure=True)
    reference_flat = None
    reference_output = scratch / f"{case.name}-aiken.flat"
    if shrink.returncode:
        print(f"{case.name}: Aiken shrink baseline unavailable (exit {shrink.returncode})",
              file=sys.stderr)
    else:
        reference_flat = bytes.fromhex(shrink.stdout)
        reference_output.write_bytes(reference_flat)

    for arguments, expected in case.observations:
        before = evaluate(aiken, source, arguments)
        after = evaluate(aiken, optimized, arguments)
        check_expected(case, source, arguments, before, expected)
        check_expected(case, optimized, arguments, after, expected)
        if before is None or after is None:
            raise CheckFailure(f"{case.name}: benchmark needs a successful evaluation")
        reference = None
        if reference_flat is not None:
            reference = evaluate(aiken, reference_output, arguments, flat=True)
            check_expected(case, reference_output, arguments, reference, expected)
        sizes = (len(original_flat), len(optimized_flat),
                 None if reference_flat is None else len(reference_flat))
        cpu = (before[1], after[1], None if reference is None else reference[1])
        memory = (before[2], after[2], None if reference is None else reference[2])
        print(f"{case.name:<24} {format_comparison(sizes):>20} "
              f"{format_comparison(cpu):>32} {format_comparison(memory):>25}")


def format_comparison(values):
    original, optimized, reference = values
    baseline = "n/a" if reference is None else f"{reference:,}"
    return f"{original:,} -> {optimized:,} ({baseline})"


def run_suite(optimizer, aiken, benchmark, work_dir):
    with tempfile.TemporaryDirectory(prefix="uplc-optimizer-", dir=work_dir) as temporary:
        scratch = Path(temporary)
        for case in regression_cases():
            source = scratch / f"{case.name}.uplc"
            source.write_text(case.program, encoding="utf-8")
            optimized = scratch / f"{case.name}-opt.uplc"
            before, after = optimized_file(optimizer, case, source, optimized)
            if aiken:
                for arguments, expected in case.observations:
                    for script in (source, optimized):
                        result = evaluate(aiken, script, arguments)
                        check_expected(case, script, arguments, result, expected)
            print(f"PASS {case.name:<26} {before} -> {after} nodes")

        if benchmark:
            print("\nOriginal -> optimized (Aiken shrink)")
            print(f"{'Fixture':<24} {'Flat bytes':>20} {'CPU':>32} {'Memory':>25}")
            for case in benchmark_cases():
                source = scratch / f"{case.name}.uplc"
                source.write_text(case.program, encoding="utf-8")
                optimized = scratch / f"{case.name}-opt.uplc"
                optimized_file(optimizer, case, source, optimized)
                benchmark_aiken(aiken, case, source, optimized, scratch)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    launch = parser.add_mutually_exclusive_group()
    launch.add_argument("--optimizer", help="path to the compiled uplc_opt executable")
    launch.add_argument("--lean", help="path to lean, run Main.lean using the current LEAN_PATH")
    parser.add_argument("--aiken", default=shutil.which("aiken"), help="path to the Aiken CLI")
    parser.add_argument("--bench", action="store_true", help="measure Flat bytes, CPU and memory with Aiken")
    parser.add_argument("--work-dir", type=Path, help="parent directory for temporary test files")
    args = parser.parse_args()
    if args.bench and not args.aiken:
        parser.error("--bench requires Aiken on PATH or --aiken")

    try:
        if args.lean:
            optimizer = [resolve_command(args.lean), "--run", str(PROJECT / "Main.lean")]
        elif args.optimizer:
            optimizer = [resolve_command(args.optimizer)]
        else:
            optimizer = [resolve_command("lake"), "env", "lean", "--run", "Main.lean"]
        aiken = resolve_command(args.aiken) if args.aiken else None
        if aiken is None:
            print("Aiken unavailable. Running CLI and AST size checks.")
        work_dir = args.work_dir
        if work_dir is None and PROJECT.parent.name == "outputs":
            candidate = PROJECT.parent.parent / "work"
            if candidate.is_dir():
                work_dir = candidate
        run_suite(optimizer, aiken, args.bench, work_dir)
    except (CheckFailure, OSError, ValueError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
