"""Exact sparse scout for the cutoff-two BF4 cube Gram diagonal.

The lower-cube half amplitude restricts the 24 fixed-interface variables to
12 labels in ``{0, 2}`` and 12 labels equal to zero.  This module multiplies
that support mask by the genuine fixed-interface heat factors and temporal-
link SU(2) invariant multiplicities, then contracts the resulting 44-factor
graph exactly.  The source half-amplitude contributes an additional squared
heat factor ``(1/4096)^2``.

The result is untrusted producer output.  Lean must independently check the
geometry, local tables, elimination equations, and final rational.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from fractions import Fraction

from computations.bf4_cutoff_two_cube_boundary_row import (
    EXPECTED_ACTIVE_FIXED_FACE_IDS,
    EXPECTED_FIXED_FACE_IDS,
)
from computations.bf4_cutoff_two_vacuum_column import (
    EliminationStep,
    Factor,
    _eliminate,
    _factor_from_function,
    _induced_order,
    _initialize_worker,
    _order_task,
    _synchronize_worker,
    coeff_w,
)
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.exact_haar_network import invariant_multiplicity
from computations.general_cutoff_coherence_scout import slab_link_incidence


DOMAIN = (0, 1, 2)


@dataclass(frozen=True)
class CubeGramDiagonalTrace:
    coupling: Fraction
    fixed_face_ids: tuple[int, ...]
    fixed_link_scopes: tuple[tuple[int, ...], ...]
    order: tuple[int, ...]
    induced_width: int
    steps: tuple[EliminationStep, ...]
    interface_sum: Fraction
    source_heat_factor: Fraction
    exact_diagonal: Fraction
    worker_pids: tuple[int, ...]

    def validates(self) -> bool:
        return (
            self.fixed_face_ids == EXPECTED_FIXED_FACE_IDS
            and len(self.fixed_link_scopes) == 20
            and tuple(sorted(self.order)) == tuple(range(24))
            and tuple(step.variable for step in self.steps) == self.order
            and self.induced_width <= 5
            and self.source_heat_factor == coeff_w(self.coupling, 1) ** 6
            and self.exact_diagonal
            == self.source_heat_factor ** 2 * self.interface_sum
        )


def fixed_geometry() -> tuple[
    tuple[int, ...], tuple[tuple[int, ...], ...]
]:
    plaquettes = boundary_complete_slab_plaquettes(1)
    fixed_face_ids = tuple(
        index
        for index, (point, plane) in enumerate(plaquettes)
        if plane[1] == 3 and point[3] == 0
    )
    if fixed_face_ids != EXPECTED_FIXED_FACE_IDS:
        raise AssertionError("Python fixed-interface order drifted")
    variable_of = {
        face_id: variable for variable, face_id in enumerate(fixed_face_ids)
    }
    incidence = slab_link_incidence(1)
    fixed_links = tuple(
        link for link in incidence if link[1] == 3 and link[0][3] == 0
    )
    scopes = tuple(
        tuple(
            sorted(
                variable_of[plaquettes.index(face)]
                for face in incidence[link]
                if plaquettes.index(face) in variable_of
            )
        )
        for link in fixed_links
    )
    if len(scopes) != 20 or any(len(scope) > 6 for scope in scopes):
        raise AssertionError("Python fixed-link geometry drifted")
    return fixed_face_ids, scopes


def diagonal_factors(coupling: Fraction) -> tuple[Factor, ...]:
    fixed_face_ids, fixed_link_scopes = fixed_geometry()
    active = set(EXPECTED_ACTIVE_FIXED_FACE_IDS)
    unary = tuple(
        _factor_from_function(
            (variable,),
            lambda environment, variable=variable, face_id=face_id:
                coeff_w(coupling, environment[variable])
                * (
                    1
                    if (
                        face_id in active
                        and environment[variable] in (0, 2)
                    )
                    or (
                        face_id not in active
                        and environment[variable] == 0
                    )
                    else 0
                ),
        )
        for variable, face_id in enumerate(fixed_face_ids)
    )
    links = tuple(
        _factor_from_function(
            scope,
            lambda environment, scope=scope:
                invariant_multiplicity(
                    tuple(environment[variable] for variable in scope)
                ),
        )
        for scope in fixed_link_scopes
    )
    return unary + links


def compute_cube_gram_diagonal(
    coupling: Fraction = Fraction(1, 2), *, jobs: int = 1,
) -> CubeGramDiagonalTrace:
    if not 1 <= jobs <= 16:
        raise ValueError("jobs must lie in 1..16")
    fixed_face_ids, fixed_link_scopes = fixed_geometry()
    factors = diagonal_factors(coupling)
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
    interface_sum = Fraction(1)
    for factor in factors:
        interface_sum *= factor.table[0]
    source_heat_factor = coeff_w(coupling, 1) ** 6
    trace = CubeGramDiagonalTrace(
        coupling=coupling,
        fixed_face_ids=fixed_face_ids,
        fixed_link_scopes=fixed_link_scopes,
        order=order,
        induced_width=width,
        steps=tuple(steps),
        interface_sum=interface_sum,
        source_heat_factor=source_heat_factor,
        exact_diagonal=source_heat_factor ** 2 * interface_sum,
        worker_pids=tuple(sorted(all_pids)),
    )
    if not trace.validates():
        raise AssertionError("cutoff-two cube Gram diagonal trace failed")
    if jobs > 1 and len(trace.worker_pids) != jobs:
        raise AssertionError(
            f"requested {jobs} workers but observed {len(trace.worker_pids)}"
        )
    return trace


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coupling", default="1/2")
    parser.add_argument("--jobs", type=int, default=1)
    arguments = parser.parse_args()
    trace = compute_cube_gram_diagonal(
        Fraction(arguments.coupling), jobs=arguments.jobs
    )
    print(json.dumps({
        "exact_diagonal": str(trace.exact_diagonal),
        "fixed_link_factors": len(trace.fixed_link_scopes),
        "induced_width": trace.induced_width,
        "interface_sum": str(trace.interface_sum),
        "order": trace.order,
        "source_heat_factor": str(trace.source_heat_factor),
        "workers_used": len(trace.worker_pids),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
