"""Emit Lean-checkable exact finite variable-elimination traces.

The producer accepts one positive rational weight table per coordinate.  It
computes the exact dynamic-programming table for the product weight on the
full finite word carrier and emits a Lean declaration of
``ExactVariableEliminationCertificate``.  Lean rechecks the original value
on every complete word, every one-coordinate elimination equation, and the
final scalar sum.

This program is intentionally untrusted.  Parallel Python ``Fraction``
arithmetic only proposes literals; a producer bug causes the generated Lean
file to fail.  No ``native_decide``, ``sorry``, or new axiom is emitted.

Demo::

    python3 computations/finite_elimination_lean_certificate.py \
      --demo --jobs 16 --name exactProductEight --output generated.lean

Input schema::

    {"coordinate_weights": [["1", "2"], ["3/2", "4"]]}
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing
import os
import re
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Any, Iterable


DEMO_PAYLOAD: dict[str, Any] = {
    "coordinate_weights": [
        ["1", "2"],
        ["2", "1"],
        ["1", "3"],
        ["3", "2"],
        ["2", "5"],
        ["1", "4"],
        ["3", "1"],
        ["2", "3"],
    ]
}

_LEAN_IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")
_WORKER_BARRIER: Any = None
_WORKER_SYNCHRONIZED = False


def _fraction(value: Any) -> Fraction:
    if isinstance(value, bool):
        raise ValueError("Boolean values are not rational weights")
    try:
        result = Fraction(value)
    except (TypeError, ValueError, ZeroDivisionError) as error:
        raise ValueError(f"invalid rational weight: {value!r}") from error
    if result < 0:
        raise ValueError("coordinate weights must be nonnegative")
    return result


@dataclass(frozen=True)
class ProductEliminationInput:
    coordinate_weights: tuple[tuple[Fraction, ...], ...]

    @classmethod
    def from_json(cls, payload: dict[str, Any]) -> "ProductEliminationInput":
        if not isinstance(payload, dict):
            raise ValueError("the trace payload must be a JSON object")
        raw = payload.get("coordinate_weights")
        if not isinstance(raw, list) or not raw:
            raise ValueError("coordinate_weights must be a nonempty list")
        rows: list[tuple[Fraction, ...]] = []
        domain_size: int | None = None
        for index, raw_row in enumerate(raw):
            if not isinstance(raw_row, list) or not raw_row:
                raise ValueError(f"coordinate weight row {index} must be nonempty")
            row = tuple(_fraction(value) for value in raw_row)
            if domain_size is None:
                domain_size = len(row)
            elif len(row) != domain_size:
                raise ValueError("all coordinate weight rows must have equal length")
            rows.append(row)
        return cls(tuple(rows))

    @property
    def domain_size(self) -> int:
        return len(self.coordinate_weights[0])

    @property
    def variables(self) -> int:
        return len(self.coordinate_weights)

    @property
    def exact_sum(self) -> Fraction:
        result = Fraction(1)
        for row in self.coordinate_weights:
            result *= sum(row, Fraction(0))
        return result


@dataclass(frozen=True)
class ProductEliminationTrace:
    source: ProductEliminationInput
    stages: tuple[tuple[tuple[tuple[int, ...], Fraction], ...], ...]
    worker_pids: tuple[int, ...]

    @property
    def exact_sum(self) -> Fraction:
        return self.stages[0][0][1]

    def validates(self) -> bool:
        domain = self.source.domain_size
        variables = self.source.variables
        if len(self.stages) != variables + 1:
            return False
        maps = [dict(stage) for stage in self.stages]
        for remaining, stage in enumerate(self.stages):
            if tuple(word for word, _ in stage) != tuple(
                product(range(domain), repeat=remaining)
            ):
                return False
        for assignment, value in self.stages[variables]:
            expected = Fraction(1)
            for coordinate, label in enumerate(assignment):
                expected *= self.source.coordinate_weights[coordinate][label]
            if value != expected:
                return False
        for remaining in range(variables):
            for tail, value in self.stages[remaining]:
                if value != sum(
                    (maps[remaining + 1][(label,) + tail] for label in range(domain)),
                    Fraction(0),
                ):
                    return False
        return self.exact_sum == self.source.exact_sum


def _stage_entry(
    task: tuple[tuple[tuple[Fraction, ...], ...], int, tuple[int, ...]],
) -> tuple[int, int, tuple[int, ...], Fraction]:
    global _WORKER_SYNCHRONIZED
    if _WORKER_BARRIER is not None and not _WORKER_SYNCHRONIZED:
        _WORKER_BARRIER.wait(timeout=30)
        _WORKER_SYNCHRONIZED = True
    weights, remaining, tail = task
    eliminated = len(weights) - remaining
    value = Fraction(1)
    for row in weights[:eliminated]:
        value *= sum(row, Fraction(0))
    for row, label in zip(weights[eliminated:], tail, strict=True):
        value *= row[label]
    return os.getpid(), remaining, tail, value


def _initialize_worker(barrier: Any) -> None:
    global _WORKER_BARRIER, _WORKER_SYNCHRONIZED
    _WORKER_BARRIER = barrier
    _WORKER_SYNCHRONIZED = False


def compute_trace(
    source: ProductEliminationInput, *, jobs: int = 1
) -> ProductEliminationTrace:
    if jobs < 1:
        raise ValueError("jobs must be positive")
    tasks = [
        (source.coordinate_weights, remaining, tuple(tail))
        for remaining in range(source.variables + 1)
        for tail in product(range(source.domain_size), repeat=remaining)
    ]
    if jobs == 1:
        results = [_stage_entry(task) for task in tasks]
    else:
        context = multiprocessing.get_context("spawn")
        barrier = context.Barrier(jobs)
        with ProcessPoolExecutor(
            max_workers=jobs,
            mp_context=context,
            initializer=_initialize_worker,
            initargs=(barrier,),
        ) as pool:
            results = list(pool.map(_stage_entry, tasks, chunksize=1))
    stages: list[list[tuple[tuple[int, ...], Fraction]]] = [
        [] for _ in range(source.variables + 1)
    ]
    pids: set[int] = set()
    for pid, remaining, tail, value in results:
        pids.add(pid)
        stages[remaining].append((tail, value))
    trace = ProductEliminationTrace(
        source,
        tuple(tuple(stage) for stage in stages),
        tuple(sorted(pids)),
    )
    if not trace.validates():
        raise AssertionError("internally generated elimination trace is invalid")
    if jobs > 1 and len(trace.worker_pids) != jobs:
        raise AssertionError(
            f"requested {jobs} workers but observed {len(trace.worker_pids)}"
        )
    return trace


def _q_literal(value: Fraction) -> str:
    if value == 0:
        return "(0 : Q')"
    if value.denominator == 1:
        return f"Q'.ofNat {value.numerator}"
    return f"Q'.mkPos {value.numerator} {value.denominator} (by decide)"


def _list_literal(word: Iterable[int]) -> str:
    values = list(word)
    return "[" + ", ".join(str(value) for value in values) + "]"


def _or_pattern(count: int) -> str:
    return " | ".join("rfl" for _ in range(count))


def emit_lean(trace: ProductEliminationTrace, *, name: str) -> str:
    if not _LEAN_IDENTIFIER.fullmatch(name):
        raise ValueError("name must be a safe Lean identifier")
    if not trace.validates():
        raise ValueError("cannot emit an invalid trace")
    source = trace.source
    variables = source.variables
    domain = source.domain_size
    full_stage = trace.stages[variables]
    lines = [
        "/- Generated by computations/finite_elimination_lean_certificate.py.",
        "   The generator is untrusted; Lean rechecks the complete trace. -/",
        "import YMGap.Continuum.FiniteVariableEliminationCertificate",
        "",
        "namespace YMGap.Continuum.FiniteVariableEliminationCertificateExample",
        "",
        "open YMGap.Constructive",
        "open YMGap.Continuum.CayleyPruferInjection",
        "open YMGap.Continuum.FiniteVariableEliminationCertificate",
        "",
        'local infix:50 " ≈ " => Q\'.eqv',
        "",
        f"def {name}Value : List Nat → Q'",
    ]
    for word, value in full_stage:
        lines.append(f"  | {_list_literal(word)} => {_q_literal(value)}")
    lines.extend(["  | _ => 0", "", f"def {name}Table : Nat → List Nat → Q'"])
    lines.append(f"  | {variables}, assignment => {name}Value assignment")
    for remaining in range(variables - 1, -1, -1):
        for tail, value in trace.stages[remaining]:
            lines.append(
                f"  | {remaining}, {_list_literal(tail)} => {_q_literal(value)}"
            )
    lines.extend(
        [
            "  | _, _ => 0",
            "",
            f"def {name}Certificate :",
            f"    ExactVariableEliminationCertificate {domain} {variables} {name}Value where",
            f"  table := {name}Table",
            "  initial := by",
            "    intro assignment _hassignment",
            "    exact Q'.eqv_refl _",
            "  step := by",
            "    intro remaining hremaining tail htail",
        ]
    )
    cases = " ∨ ".join(f"remaining = {index}" for index in range(variables))
    lines.append(f"    have hcases : {cases} := by omega")
    lines.append(f"    rcases hcases with {_or_pattern(variables)}")
    for remaining in range(variables):
        words = [word for word, _ in trace.stages[remaining]]
        carrier = "[" + ", ".join(_list_literal(word) for word in words) + "]"
        lines.append(f"    · have hcarrier : allSeqs {domain} {remaining} = {carrier} := by decide")
        lines.append("      rw [hcarrier] at htail")
        lines.append("      simp at htail")
        if remaining == 0:
            lines.extend(["      subst tail", "      decide"])
        else:
            lines.append(f"      rcases htail with {_or_pattern(len(words))} <;> decide")
    lines.extend(
        [
            "",
            f"theorem {name}Sum :",
            f"    finiteAssignmentSum {domain} {variables} {name}Value ≈",
            f"      {_q_literal(trace.exact_sum)} := by",
            f"  exact {name}Certificate.assignmentSum_eqv_bottom",
            "",
            f"#print axioms {name}Sum",
            "",
            "end YMGap.Continuum.FiniteVariableEliminationCertificateExample",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    source_group = parser.add_mutually_exclusive_group(required=True)
    source_group.add_argument("--demo", action="store_true")
    source_group.add_argument("--input", type=Path)
    parser.add_argument("--name", default="exactProductEight")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    payload = DEMO_PAYLOAD if args.demo else json.loads(args.input.read_text())
    source = ProductEliminationInput.from_json(payload)
    trace = compute_trace(source, jobs=args.jobs)
    lean = emit_lean(trace, name=args.name)
    if args.output is None:
        print(lean, end="")
    else:
        args.output.write_text(lean)
    digest = hashlib.sha256(lean.encode()).hexdigest()
    print(
        f"trace_sha256={digest} workers_used={len(trace.worker_pids)} "
        f"sum={trace.exact_sum}",
        file=os.sys.stderr,
    )


if __name__ == "__main__":
    main()
