"""Exact sparse elimination scout for the BF4 cutoff-two vacuum column.

At half-extent zero the lower carrier has 24 face variables and 48 local
link factors.  Each variable takes the doubled-spin values 0, 1, 2.  This
module mirrors the production corrected-slab geometry, evaluates the exact
SU(2) invariant multiplicities, and contracts the finite factor graph at a
fixed rational heat coordinate.

The Python result is *not* trusted by Lean.  It is the producer-side scout
for a compact sparse-factor certificate; a later Lean module must recheck
the geometry, local tables, elimination equations, and final scalar.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing
import os
import random
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Any, Iterable

from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.exact_haar_network import invariant_multiplicity
from computations.general_cutoff_coherence_scout import slab_link_incidence


CUTOFF = 2
DOMAIN = (0, 1, 2)
EXPECTED_LOWER_FACE_IDS = (
    0, 1, 3, 9, 10, 12, 18, 19, 21, 27, 28, 30,
    36, 37, 39, 45, 46, 48, 54, 55, 57, 63, 64, 66,
)
EXPECTED_ACTIVE_LINK_SCOPES = (
    (0, 1), (0, 2), (0, 6, 7), (0, 12, 14),
    (1, 2), (1, 3, 4), (1, 13, 14), (2, 3, 5),
    (2, 7, 8), (3, 7, 9, 10), (3, 14, 15, 17), (4, 5),
    (4,), (4, 16, 17), (5,), (5, 10, 11),
    (6, 8), (6,), (6, 18, 20), (7, 14, 19, 20),
    (8, 9, 11), (8,), (9,), (9, 20, 21, 23),
    (10,), (10, 17, 22, 23), (11,), (11,),
    (12, 13), (12, 18, 19), (12,), (13, 15, 16),
    (13,), (15, 19, 21, 22), (15,), (16,),
    (16,), (17,), (18,), (18,), (19,), (20,),
    (21,), (21,), (22,), (22,), (23,), (23,),
)
EXPECTED_MULTIPLICITY_TABLES = (
    (1,),
    (1, 0, 0),
    (1, 0, 0, 0, 1, 0, 0, 0, 1),
    (1, 0, 0, 0, 1, 0, 0, 0, 1,
     0, 1, 0, 1, 0, 1, 0, 1, 0,
     0, 0, 1, 0, 1, 0, 1, 0, 1),
    (1, 0, 0, 0, 1, 0, 0, 0, 1,
     0, 1, 0, 1, 0, 1, 0, 1, 0,
     0, 0, 1, 0, 1, 0, 1, 0, 1,
     0, 1, 0, 1, 0, 1, 0, 1, 0,
     1, 0, 1, 0, 2, 0, 1, 0, 2,
     0, 1, 0, 1, 0, 2, 0, 2, 0,
     0, 0, 1, 0, 1, 0, 1, 0, 1,
     0, 1, 0, 1, 0, 2, 0, 2, 0,
     1, 0, 1, 0, 2, 0, 1, 0, 3),
)

_WORKER_BARRIER: Any = None
_WORKER_SYNCHRONIZED = False


def _q(value: str | int | Fraction) -> Fraction:
    return value if isinstance(value, Fraction) else Fraction(value)


def coeff_w(w: Fraction, spin: int) -> Fraction:
    """Production heat coefficient ``(spin+1) w^(spin(spin+2))``."""

    if spin < 0:
        raise ValueError("spin label must be nonnegative")
    return Fraction(spin + 1) * w ** (spin * (spin + 2))


@dataclass(frozen=True)
class Factor:
    scope: tuple[int, ...]
    table: tuple[Fraction, ...]

    def __post_init__(self) -> None:
        if tuple(sorted(set(self.scope))) != self.scope:
            raise ValueError("factor scope must be sorted and duplicate-free")
        if len(self.table) != len(DOMAIN) ** len(self.scope):
            raise ValueError("factor table has the wrong cardinality")

    def value(self, environment: dict[int, int]) -> Fraction:
        index = 0
        for variable in self.scope:
            index = len(DOMAIN) * index + environment[variable]
        return self.table[index]


@dataclass(frozen=True)
class EliminationStep:
    variable: int
    bucket_scopes: tuple[tuple[int, ...], ...]
    result: Factor


@dataclass(frozen=True)
class CutoffTwoVacuumColumnTrace:
    coupling: Fraction
    lower_face_ids: tuple[int, ...]
    active_link_scopes: tuple[tuple[int, ...], ...]
    order: tuple[int, ...]
    induced_width: int
    steps: tuple[EliminationStep, ...]
    final_scalars: tuple[Fraction, ...]
    exact_sum: Fraction
    worker_pids: tuple[int, ...]

    def digest_payload(self) -> dict[str, Any]:
        return {
            "coupling": str(self.coupling),
            "lower_face_ids": self.lower_face_ids,
            "active_link_scopes": self.active_link_scopes,
            "order": self.order,
            "induced_width": self.induced_width,
            "steps": [
                {
                    "variable": step.variable,
                    "bucket_scopes": step.bucket_scopes,
                    "result_scope": step.result.scope,
                    "result_table": [str(value) for value in step.result.table],
                }
                for step in self.steps
            ],
            "final_scalars": [str(value) for value in self.final_scalars],
            "exact_sum": str(self.exact_sum),
        }

    @property
    def sha256(self) -> str:
        encoded = json.dumps(
            self.digest_payload(), sort_keys=True, separators=(",", ":")
        ).encode()
        return hashlib.sha256(encoded).hexdigest()

    def validates(self) -> bool:
        if self.lower_face_ids != EXPECTED_LOWER_FACE_IDS:
            return False
        if tuple(sorted(self.order)) != tuple(range(len(self.lower_face_ids))):
            return False
        if len(self.steps) != len(self.order):
            return False
        if tuple(step.variable for step in self.steps) != self.order:
            return False
        if max((len(step.result.scope) for step in self.steps), default=0) \
                != self.induced_width:
            return False
        final_product = Fraction(1)
        for scalar in self.final_scalars:
            final_product *= scalar
        return final_product == self.exact_sum


def lower_geometry() -> tuple[tuple[int, ...], tuple[tuple[int, ...], ...]]:
    plaquettes = boundary_complete_slab_plaquettes(1)
    lower_face_ids = tuple(
        index
        for index, (point, plane) in enumerate(plaquettes)
        if plane[1] < 3 and point[3] == 0
    )
    if lower_face_ids != EXPECTED_LOWER_FACE_IDS:
        raise AssertionError("Python corrected-slab lower-face order drifted")
    variable_of = {face_id: index for index, face_id in enumerate(lower_face_ids)}
    incidence = slab_link_incidence(1)
    lower_links = tuple(
        link
        for link in incidence
        if link[1] < 3 and link[0][3] == 0
    )
    if len(lower_links) != 48:
        raise AssertionError("expected 48 production lower links")
    active_scopes = tuple(
        tuple(
            sorted(
                variable_of[plaquettes.index(face)]
                for face in incidence[link]
                if plaquettes.index(face) in variable_of
            )
        )
        for link in lower_links
    )
    if active_scopes != EXPECTED_ACTIVE_LINK_SCOPES:
        raise AssertionError("Python corrected-slab lower-link scopes drifted")
    return lower_face_ids, active_scopes


def _factor_from_function(
    scope: Iterable[int], value: Any
) -> Factor:
    canonical_scope = tuple(sorted(set(scope)))
    table = tuple(
        _q(value(dict(zip(canonical_scope, labels, strict=True))))
        for labels in product(DOMAIN, repeat=len(canonical_scope))
    )
    return Factor(canonical_scope, table)


def physical_factors(coupling: Fraction) -> tuple[Factor, ...]:
    lower_face_ids, active_scopes = lower_geometry()
    actual_tables = tuple(
        tuple(
            invariant_multiplicity(labels)
            for labels in product(DOMAIN, repeat=arity)
        )
        for arity in range(5)
    )
    if actual_tables != EXPECTED_MULTIPLICITY_TABLES:
        raise AssertionError("local SU(2) multiplicity tables drifted")
    unary = tuple(
        _factor_from_function(
            (variable,),
            lambda environment, variable=variable:
                coeff_w(coupling, environment[variable]),
        )
        for variable in range(len(lower_face_ids))
    )
    links = tuple(
        _factor_from_function(
            scope,
            lambda environment, scope=scope:
                invariant_multiplicity(tuple(environment[var] for var in scope)),
        )
        for scope in active_scopes
    )
    return unary + links


def _induced_order(
    scopes: tuple[tuple[int, ...], ...], seed: int
) -> tuple[tuple[int, ...], int, int]:
    rng = random.Random(seed)
    remaining = set(variable for scope in scopes for variable in scope)
    work = [set(scope) for scope in scopes]
    order: list[int] = []
    width = 0
    total_entries = 0
    while remaining:
        candidates: list[tuple[int, int, float, int, set[int]]] = []
        for variable in remaining:
            bucket = [scope for scope in work if variable in scope]
            merged = set().union(*bucket) if bucket else {variable}
            following = merged - {variable}
            candidates.append(
                (len(following), len(bucket), rng.random(), variable, following)
            )
        _size, _bucket_count, _tie, variable, following = min(candidates)
        bucket = [scope for scope in work if variable in scope]
        work = [scope for scope in work if variable not in scope]
        work.append(following)
        remaining.remove(variable)
        order.append(variable)
        width = max(width, len(following))
        total_entries += len(DOMAIN) ** len(following)
    return tuple(order), width, total_entries


def _initialize_worker(barrier: Any) -> None:
    global _WORKER_BARRIER, _WORKER_SYNCHRONIZED
    _WORKER_BARRIER = barrier
    _WORKER_SYNCHRONIZED = False


def _synchronize_worker(_task: int) -> int:
    global _WORKER_SYNCHRONIZED
    if _WORKER_BARRIER is not None and not _WORKER_SYNCHRONIZED:
        _WORKER_BARRIER.wait(timeout=30)
        _WORKER_SYNCHRONIZED = True
    return os.getpid()


def _order_task(task: tuple[tuple[tuple[int, ...], ...], int]) -> (
    tuple[int, tuple[int, ...], int, int]
):
    scopes, seed = task
    order, width, total_entries = _induced_order(scopes, seed)
    return os.getpid(), order, width, total_entries


def _entry_task(
    task: tuple[
        tuple[Factor, ...], int, tuple[int, ...], tuple[int, ...]
    ]
) -> tuple[int, tuple[int, ...], Fraction]:
    bucket, variable, result_scope, labels = task
    environment = dict(zip(result_scope, labels, strict=True))
    total = Fraction(0)
    for spin in DOMAIN:
        environment[variable] = spin
        product_value = Fraction(1)
        for factor in bucket:
            product_value *= factor.value(environment)
        total += product_value
    return os.getpid(), labels, total


def _entry_batch_task(
    task: tuple[
        tuple[Factor, ...], int, tuple[int, ...],
        tuple[tuple[int, ...], ...],
    ]
) -> tuple[int, tuple[tuple[tuple[int, ...], Fraction], ...]]:
    bucket, variable, result_scope, assignments = task
    values = tuple(
        (labels, _entry_task((bucket, variable, result_scope, labels))[2])
        for labels in assignments
    )
    return os.getpid(), values


def _eliminate(
    factors: tuple[Factor, ...], variable: int,
    pool: ProcessPoolExecutor | None, jobs: int,
) -> tuple[tuple[Factor, ...], EliminationStep, set[int]]:
    bucket = tuple(factor for factor in factors if variable in factor.scope)
    outside = tuple(factor for factor in factors if variable not in factor.scope)
    if not bucket:
        bucket = (Factor((variable,), tuple(Fraction(1) for _ in DOMAIN)),)
    result_scope = tuple(
        sorted(
            set().union(*(set(factor.scope) for factor in bucket)) - {variable}
        )
    )
    assignments = tuple(product(DOMAIN, repeat=len(result_scope)))
    if pool is None:
        results = tuple(
            _entry_task((bucket, variable, result_scope, labels))
            for labels in assignments
        )
    else:
        batch_count = min(jobs, len(assignments))
        batches = tuple(
            tuple(assignments[index::batch_count])
            for index in range(batch_count)
        )
        batch_results = tuple(
            pool.map(
                _entry_batch_task,
                ((bucket, variable, result_scope, batch) for batch in batches),
                chunksize=1,
            )
        )
        results = tuple(
            (pid, labels, value)
            for pid, values in batch_results
            for labels, value in values
        )
    pids = {pid for pid, _labels, _value in results}
    by_assignment = {labels: value for _pid, labels, value in results}
    table = tuple(by_assignment[labels] for labels in assignments)
    result = Factor(result_scope, table)
    step = EliminationStep(
        variable,
        tuple(factor.scope for factor in bucket),
        result,
    )
    return outside + (result,), step, pids


def compute_cutoff_two_vacuum_column(
    coupling: Fraction = Fraction(1, 2), *, jobs: int = 1,
) -> CutoffTwoVacuumColumnTrace:
    if not 1 <= jobs <= 16:
        raise ValueError("jobs must lie in 1..16")
    lower_face_ids, active_scopes = lower_geometry()
    factors = physical_factors(coupling)
    all_pids: set[int] = set()
    context = multiprocessing.get_context("spawn")
    pool: ProcessPoolExecutor | None = None
    try:
        if jobs > 1:
            barrier = context.Barrier(jobs)
            pool = ProcessPoolExecutor(
                max_workers=jobs,
                mp_context=context,
                initializer=_initialize_worker,
                initargs=(barrier,),
            )
            warm_pids = tuple(pool.map(_synchronize_worker, range(jobs), chunksize=1))
            all_pids.update(warm_pids)
            if len(set(warm_pids)) != jobs:
                raise AssertionError("not every requested worker synchronized")
            order_results = tuple(
                pool.map(
                    _order_task,
                    ((tuple(factor.scope for factor in factors), seed)
                     for seed in range(jobs)),
                    chunksize=1,
                )
            )
            all_pids.update(pid for pid, _order, _width, _entries in order_results)
            _pid, order, width, _entries = min(
                order_results,
                key=lambda result: (result[2], result[3], result[1]),
            )
        else:
            order, width, _entries = _induced_order(
                tuple(factor.scope for factor in factors), 0
            )
        steps: list[EliminationStep] = []
        for variable in order:
            factors, step, pids = _eliminate(factors, variable, pool, jobs)
            steps.append(step)
            all_pids.update(pids)
    finally:
        if pool is not None:
            pool.shutdown()
    if any(factor.scope for factor in factors):
        raise AssertionError("elimination left non-scalar factors")
    exact_sum = Fraction(1)
    for factor in factors:
        exact_sum *= factor.table[0]
    trace = CutoffTwoVacuumColumnTrace(
        coupling,
        lower_face_ids,
        active_scopes,
        order,
        width,
        tuple(steps),
        tuple(factor.table[0] for factor in factors),
        exact_sum,
        tuple(sorted(all_pids)),
    )
    if not trace.validates():
        raise AssertionError("cutoff-two elimination trace failed validation")
    if jobs > 1 and len(trace.worker_pids) != jobs:
        raise AssertionError(
            f"requested {jobs} workers but observed {len(trace.worker_pids)}"
        )
    return trace


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coupling", default="1/2")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    trace = compute_cutoff_two_vacuum_column(
        Fraction(args.coupling), jobs=args.jobs
    )
    print(
        json.dumps(
            {
                "coupling": str(trace.coupling),
                "variables": len(trace.lower_face_ids),
                "link_factors": len(trace.active_link_scopes),
                "induced_width": trace.induced_width,
                "largest_table_entries": max(
                    len(step.result.table) for step in trace.steps
                ),
                "exact_sum": str(trace.exact_sum),
                "trace_sha256": trace.sha256,
                "workers_used": len(trace.worker_pids),
                "order": trace.order,
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
