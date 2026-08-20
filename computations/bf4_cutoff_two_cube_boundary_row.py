"""Exact parallel scout for the BF4 cutoff-two lower-cube boundary row.

The source is the six-face fundamental-spin surface

    (0, 1, 3, 9, 19, 39),

and the 24 fixed-interface labels range over ``0, 1, 2``.  Each production
lower link meets at most one fixed-interface face, so the boundary factor
graph is unary.  The twelve links on the cube carry the table ``(1, 0, 1)``;
the other twelve fixed-interface links carry ``(1, 0, 0)``.  Thus precisely
``2^12`` boundary words have nonzero link product.

This program is a certificate scout, not a trusted proof.  Lean separately
recomputes the geometry, local SU(2) multiplicities, factor equations, and
the final contraction from production definitions.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing
import os
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

from computations.bf4_cutoff_two_vacuum_column import coeff_w
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.exact_haar_network import invariant_multiplicity
from computations.general_cutoff_coherence_scout import slab_link_incidence


CUTOFF = 2
DOMAIN = (0, 1, 2)
CUBE_FACE_IDS = (0, 1, 3, 9, 19, 39)
EXPECTED_FIXED_FACE_IDS = (
    2, 4, 5, 11, 13, 14, 20, 22, 23, 29, 31, 32,
    38, 40, 41, 47, 49, 50, 56, 58, 59, 65, 67, 68,
)
EXPECTED_ACTIVE_FIXED_FACE_IDS = (
    2, 4, 5, 11, 13, 20, 23, 29, 40, 41, 49, 59,
)

_WORKER_BARRIER: Any = None
_WORKER_SYNCHRONIZED = False


@dataclass(frozen=True)
class CubeBoundaryRowScout:
    coupling: Fraction
    fixed_face_ids: tuple[int, ...]
    active_fixed_face_ids: tuple[int, ...]
    local_tables: tuple[tuple[int, tuple[int, int, int]], ...]
    scalar_link_values: tuple[int, ...]
    nonzero_boundary_words: int
    source_heat_factor: Fraction
    exact_row_mass: Fraction
    worker_pids: tuple[int, ...]

    def validates(self) -> bool:
        expected_tables = tuple(
            (
                face_id,
                (1, 0, 1)
                if face_id in EXPECTED_ACTIVE_FIXED_FACE_IDS
                else (1, 0, 0),
            )
            for face_id in EXPECTED_FIXED_FACE_IDS
        )
        return (
            self.fixed_face_ids == EXPECTED_FIXED_FACE_IDS
            and self.active_fixed_face_ids == EXPECTED_ACTIVE_FIXED_FACE_IDS
            and tuple(sorted(self.local_tables)) == expected_tables
            and all(value == 1 for value in self.scalar_link_values)
            and self.nonzero_boundary_words == 2 ** 12
            and self.source_heat_factor == coeff_w(self.coupling, 1) ** 6
            and self.exact_row_mass
            == self.source_heat_factor * self.nonzero_boundary_words
        )


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


def _link_task(
    task: tuple[
        tuple[tuple[int, ...], tuple[tuple[int, ...], tuple[int, int]]],
        tuple[int, ...],
        tuple[int, ...],
    ]
) -> tuple[int, int | None, tuple[int, int, int] | int]:
    (link, _unused_plane), fixed_face_ids, cube_face_ids = task
    plaquettes = boundary_complete_slab_plaquettes(1)
    incidence = slab_link_incidence(1)[link]
    incident_ids = tuple(plaquettes.index(face) for face in incidence)
    fixed = tuple(face_id for face_id in incident_ids if face_id in fixed_face_ids)
    constants = tuple(1 for face_id in incident_ids if face_id in cube_face_ids)
    if len(fixed) > 1:
        raise AssertionError("a lower link met more than one fixed face")
    if not fixed:
        return os.getpid(), None, invariant_multiplicity(constants)
    table = tuple(
        invariant_multiplicity(constants + (label,)) for label in DOMAIN
    )
    return os.getpid(), fixed[0], table  # type: ignore[return-value]


def compute_cube_boundary_row(
    coupling: Fraction = Fraction(1, 2), *, jobs: int = 1,
) -> CubeBoundaryRowScout:
    if not 1 <= jobs <= 16:
        raise ValueError("jobs must lie in 1..16")
    plaquettes = boundary_complete_slab_plaquettes(1)
    fixed_face_ids = tuple(
        index
        for index, (point, plane) in enumerate(plaquettes)
        if plane[1] == 3 and point[3] == 0
    )
    if fixed_face_ids != EXPECTED_FIXED_FACE_IDS:
        raise AssertionError("Python fixed-interface order drifted")
    incidence = slab_link_incidence(1)
    lower_links = tuple(
        link for link in incidence if link[1] < 3 and link[0][3] == 0
    )
    tasks = tuple(
        ((link, ((0, 0, 0, 0), (0, 1))), fixed_face_ids, CUBE_FACE_IDS)
        for link in lower_links
    )
    worker_pids: set[int] = set()
    if jobs == 1:
        results = tuple(_link_task(task) for task in tasks)
    else:
        context = multiprocessing.get_context("spawn")
        barrier = context.Barrier(jobs)
        with ProcessPoolExecutor(
            max_workers=jobs,
            mp_context=context,
            initializer=_initialize_worker,
            initargs=(barrier,),
        ) as pool:
            warm_pids = tuple(pool.map(_synchronize_worker, range(jobs), chunksize=1))
            worker_pids.update(warm_pids)
            if len(set(warm_pids)) != jobs:
                raise AssertionError("not every requested worker synchronized")
            results = tuple(pool.map(_link_task, tasks, chunksize=1))
    worker_pids.update(pid for pid, _face_id, _value in results)
    local_tables = tuple(
        (face_id, value)
        for _pid, face_id, value in results
        if face_id is not None
    )
    scalar_values = tuple(
        value
        for _pid, face_id, value in results
        if face_id is None
    )
    active = tuple(
        sorted(face_id for face_id, table in local_tables if table == (1, 0, 1))
    )
    nonzero_words = 1
    for _face_id, table in local_tables:
        nonzero_words *= sum(value != 0 for value in table)
    source_heat_factor = coeff_w(coupling, 1) ** 6
    scout = CubeBoundaryRowScout(
        coupling=coupling,
        fixed_face_ids=fixed_face_ids,
        active_fixed_face_ids=active,
        local_tables=local_tables,
        scalar_link_values=scalar_values,  # type: ignore[arg-type]
        nonzero_boundary_words=nonzero_words,
        source_heat_factor=source_heat_factor,
        exact_row_mass=source_heat_factor * nonzero_words,
        worker_pids=tuple(sorted(worker_pids)),
    )
    if not scout.validates():
        raise AssertionError("cutoff-two cube boundary row scout failed validation")
    if jobs > 1 and len(scout.worker_pids) != jobs:
        raise AssertionError(
            f"requested {jobs} workers but observed {len(scout.worker_pids)}"
        )
    return scout


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coupling", default="1/2")
    parser.add_argument("--jobs", type=int, default=1)
    arguments = parser.parse_args()
    scout = compute_cube_boundary_row(
        Fraction(arguments.coupling), jobs=arguments.jobs
    )
    print(json.dumps({
        "active_fixed_face_ids": scout.active_fixed_face_ids,
        "exact_row_mass": str(scout.exact_row_mass),
        "fixed_variables": len(scout.fixed_face_ids),
        "nonzero_boundary_words": scout.nonzero_boundary_words,
        "source_heat_factor": str(scout.source_heat_factor),
        "workers_used": len(scout.worker_pids),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
