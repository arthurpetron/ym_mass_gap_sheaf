"""Search for an explicit fourth cutoff-two BF4 Krylov state.

The source is the fundamental six-face lower cube.  Its exact Lean boundary
row is supported on 4096 words: twelve active fixed faces may carry 0 or 2
and all other fixed faces carry 0.  For each selected supported boundary this
scout solves the lower-link SU(2) invariant constraints for another lower
state.  A common positive boundary term proposes a positive physical Gram
edge from the cube to that state.

This producer is not trusted.  Any returned state and boundary must be
rechecked from the production definitions by Lean.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing
import os
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from itertools import combinations, product

from computations.bf4_cutoff_two_cube_boundary_row import (
    CUBE_FACE_IDS,
    EXPECTED_ACTIVE_FIXED_FACE_IDS,
    EXPECTED_FIXED_FACE_IDS,
)
from computations.bf4_cutoff_two_vacuum_column import (
    DOMAIN,
    EXPECTED_LOWER_FACE_IDS,
)
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.exact_haar_network import invariant_multiplicity
from computations.general_cutoff_coherence_scout import slab_link_incidence


@dataclass(frozen=True)
class LinkConstraint:
    lower_variables: tuple[int, ...]
    fixed_face_ids: tuple[int, ...]


@dataclass(frozen=True)
class EdgeCandidate:
    boundary_twos: tuple[int, ...]
    target_nonzero: tuple[tuple[int, int], ...]
    target_labels: tuple[int, ...]
    worker_pid: int


def lower_link_constraints() -> tuple[LinkConstraint, ...]:
    plaquettes = boundary_complete_slab_plaquettes(1)
    incidence = slab_link_incidence(1)
    variable_of = {
        face_id: variable
        for variable, face_id in enumerate(EXPECTED_LOWER_FACE_IDS)
    }
    lower_links = tuple(
        link for link in incidence if link[1] < 3 and link[0][3] == 0
    )
    constraints: list[LinkConstraint] = []
    for link in lower_links:
        incident_ids = tuple(
            plaquettes.index(face) for face in incidence[link]
        )
        lower = tuple(sorted(
            variable_of[face_id]
            for face_id in incident_ids
            if face_id in variable_of
        ))
        fixed = tuple(
            face_id
            for face_id in incident_ids
            if face_id in EXPECTED_FIXED_FACE_IDS
        )
        recognized = set(EXPECTED_LOWER_FACE_IDS) | set(EXPECTED_FIXED_FACE_IDS)
        if any(face_id not in recognized for face_id in incident_ids):
            raise AssertionError("lower link met a face outside lower/fixed sets")
        constraints.append(LinkConstraint(lower, fixed))
    if len(constraints) != 48:
        raise AssertionError("expected 48 lower-link constraints")
    return tuple(constraints)


def _compatible(
    labels: tuple[int, ...],
    boundary: dict[int, int],
    constraints: tuple[LinkConstraint, ...],
) -> bool:
    return all(
        invariant_multiplicity(
            tuple(labels[var] for var in constraint.lower_variables)
            + tuple(boundary[face_id] for face_id in constraint.fixed_face_ids)
        )
        > 0
        for constraint in constraints
    )


def _find_target_with_excluded(
    boundary_twos: tuple[int, ...],
    excluded_labels: tuple[tuple[int, ...], ...],
) -> EdgeCandidate | None:
    constraints = lower_link_constraints()
    boundary = {face_id: 0 for face_id in EXPECTED_FIXED_FACE_IDS}
    for face_id in boundary_twos:
        boundary[face_id] = 2

    cube = tuple(
        1 if face_id in CUBE_FACE_IDS else 0
        for face_id in EXPECTED_LOWER_FACE_IDS
    )
    excluded = set(excluded_labels)
    if not _compatible(cube, boundary, constraints):
        raise AssertionError("selected word left the proved cube support")

    incident: list[list[int]] = [[] for _ in EXPECTED_LOWER_FACE_IDS]
    for constraint_index, constraint in enumerate(constraints):
        for variable in constraint.lower_variables:
            incident[variable].append(constraint_index)
    order = tuple(
        sorted(
            range(len(EXPECTED_LOWER_FACE_IDS)),
            key=lambda variable: (-len(incident[variable]), variable),
        )
    )
    assignment: dict[int, int] = {}

    def feasible(constraint: LinkConstraint) -> bool:
        known = tuple(
            assignment[var]
            for var in constraint.lower_variables
            if var in assignment
        )
        missing = sum(
            var not in assignment for var in constraint.lower_variables
        )
        fixed = tuple(boundary[face_id] for face_id in constraint.fixed_face_ids)
        return any(
            invariant_multiplicity(known + completion + fixed) > 0
            for completion in product(DOMAIN, repeat=missing)
        )

    def search(depth: int) -> tuple[int, ...] | None:
        if depth == len(order):
            labels = tuple(
                assignment[variable]
                for variable in range(len(EXPECTED_LOWER_FACE_IDS))
            )
            if labels in excluded:
                return None
            return labels if _compatible(labels, boundary, constraints) else None
        variable = order[depth]
        for label in DOMAIN:
            assignment[variable] = label
            if all(feasible(constraints[index]) for index in incident[variable]):
                found = search(depth + 1)
                if found is not None:
                    return found
        del assignment[variable]
        return None

    target = search(0)
    if target is None:
        return None
    if not _compatible(target, boundary, constraints):
        raise AssertionError("returned target failed its lower-link constraints")
    nonzero = tuple(
        (face_id, target[variable])
        for variable, face_id in enumerate(EXPECTED_LOWER_FACE_IDS)
        if target[variable] != 0
    )
    return EdgeCandidate(boundary_twos, nonzero, target, os.getpid())


def _seed_three_labels() -> tuple[tuple[int, ...], ...]:
    cube = tuple(
        1 if face_id in CUBE_FACE_IDS else 0
        for face_id in EXPECTED_LOWER_FACE_IDS
    )
    return (
        (0,) * len(EXPECTED_LOWER_FACE_IDS),
        cube,
        tuple(2 * label for label in cube),
    )


def _seed_five_labels() -> tuple[tuple[int, ...], ...]:
    single = tuple(
        2 if face_id == 1 else 0
        for face_id in EXPECTED_LOWER_FACE_IDS
    )
    punctured = tuple(
        2 if face_id in (0, 3, 9, 19, 39) else 0
        for face_id in EXPECTED_LOWER_FACE_IDS
    )
    return _seed_three_labels() + (single, punctured)


def _find_target(boundary_twos: tuple[int, ...]) -> EdgeCandidate | None:
    return _find_target_with_excluded(boundary_twos, _seed_three_labels())


def _find_target_after_five(
    boundary_twos: tuple[int, ...],
) -> EdgeCandidate | None:
    return _find_target_with_excluded(boundary_twos, _seed_five_labels())


def enumerate_compatible_targets(
    boundary_twos: tuple[int, ...], *, limit: int = 10000,
) -> tuple[tuple[tuple[int, int], ...], ...]:
    """Enumerate lower states compatible with one cube-supported boundary."""
    constraints = lower_link_constraints()
    boundary = {face_id: 0 for face_id in EXPECTED_FIXED_FACE_IDS}
    for face_id in boundary_twos:
        if face_id not in EXPECTED_FIXED_FACE_IDS:
            raise ValueError(f"face {face_id} is not a fixed-interface face")
        boundary[face_id] = 2
    incident: list[list[int]] = [[] for _ in EXPECTED_LOWER_FACE_IDS]
    for constraint_index, constraint in enumerate(constraints):
        for variable in constraint.lower_variables:
            incident[variable].append(constraint_index)
    order = tuple(
        sorted(
            range(len(EXPECTED_LOWER_FACE_IDS)),
            key=lambda variable: (-len(incident[variable]), variable),
        )
    )
    assignment: dict[int, int] = {}
    results: list[tuple[tuple[int, int], ...]] = []

    def feasible(constraint: LinkConstraint) -> bool:
        known = tuple(
            assignment[var]
            for var in constraint.lower_variables
            if var in assignment
        )
        missing = sum(
            var not in assignment for var in constraint.lower_variables
        )
        fixed = tuple(boundary[face_id] for face_id in constraint.fixed_face_ids)
        return any(
            invariant_multiplicity(known + completion + fixed) > 0
            for completion in product(DOMAIN, repeat=missing)
        )

    def search(depth: int) -> None:
        if len(results) >= limit:
            return
        if depth == len(order):
            labels = tuple(
                assignment[variable]
                for variable in range(len(EXPECTED_LOWER_FACE_IDS))
            )
            if _compatible(labels, boundary, constraints):
                results.append(tuple(
                    (face_id, labels[variable])
                    for variable, face_id in enumerate(EXPECTED_LOWER_FACE_IDS)
                    if labels[variable] != 0
                ))
            return
        variable = order[depth]
        for label in DOMAIN:
            assignment[variable] = label
            if all(feasible(constraints[index]) for index in incident[variable]):
                search(depth + 1)
        del assignment[variable]

    search(0)
    return tuple(sorted(
        results,
        key=lambda target: (len(target), sum(label for _face, label in target), target),
    ))


def candidate_boundaries(max_twos: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        selection
        for count in range(1, max_twos + 1)
        for selection in combinations(EXPECTED_ACTIVE_FIXED_FACE_IDS, count)
    )


def punctured_boundary_support() -> tuple[tuple[int, ...], ...]:
    mandatory = (2, 5, 11, 41)
    optional = (4, 13, 20, 23, 29, 40, 49, 59)
    return tuple(
        tuple(sorted(mandatory + selection))
        for count in range(len(optional) + 1)
        for selection in combinations(optional, count)
    )


def search_candidates(*, jobs: int, max_twos: int) -> tuple[EdgeCandidate, ...]:
    boundaries = candidate_boundaries(max_twos)
    if jobs == 1:
        results = tuple(_find_target(boundary) for boundary in boundaries)
    else:
        context = multiprocessing.get_context("spawn")
        with ProcessPoolExecutor(max_workers=jobs, mp_context=context) as pool:
            results = tuple(pool.map(_find_target, boundaries, chunksize=1))
    candidates = tuple(candidate for candidate in results if candidate is not None)
    return tuple(
        sorted(
            candidates,
            key=lambda candidate: (
                len(candidate.target_nonzero),
                sum(label for _face, label in candidate.target_nonzero),
                candidate.boundary_twos,
                candidate.target_labels,
            ),
        )
    )


def search_punctured_layer(*, jobs: int) -> tuple[EdgeCandidate, ...]:
    boundaries = punctured_boundary_support()
    if jobs == 1:
        results = tuple(_find_target_after_five(boundary) for boundary in boundaries)
    else:
        context = multiprocessing.get_context("spawn")
        with ProcessPoolExecutor(max_workers=jobs, mp_context=context) as pool:
            results = tuple(pool.map(
                _find_target_after_five, boundaries, chunksize=1
            ))
    candidates = tuple(candidate for candidate in results if candidate is not None)
    return tuple(sorted(
        candidates,
        key=lambda candidate: (
            len(candidate.target_nonzero),
            sum(label for _face, label in candidate.target_nonzero),
            candidate.boundary_twos,
            candidate.target_labels,
        ),
    ))


def _classify_boundary_for_65_sector(
    boundary_twos: tuple[int, ...],
) -> tuple[int, tuple[int, ...], int, tuple[tuple[tuple[int, int], ...], ...]]:
    targets = enumerate_compatible_targets(boundary_twos, limit=1000)
    cube_sparse = tuple((face_id, 1) for face_id in CUBE_FACE_IDS)

    def in_sector(target: tuple[tuple[int, int], ...]) -> bool:
        return target == cube_sparse or all(
            face_id in CUBE_FACE_IDS and label == 2
            for face_id, label in target
        )

    outside = tuple(target for target in targets if not in_sector(target))
    return os.getpid(), boundary_twos, len(targets), outside


def classify_65_sector(*, jobs: int) -> dict[str, object]:
    boundaries = ((),) + candidate_boundaries(12)
    if jobs == 1:
        results = tuple(
            _classify_boundary_for_65_sector(boundary)
            for boundary in boundaries
        )
    else:
        context = multiprocessing.get_context("spawn")
        with ProcessPoolExecutor(max_workers=jobs, mp_context=context) as pool:
            results = tuple(pool.map(
                _classify_boundary_for_65_sector, boundaries, chunksize=1
            ))
    outside = tuple(
        (boundary, target)
        for _pid, boundary, _count, targets in results
        for target in targets
    )
    return {
        "boundary_words_checked": len(results),
        "compatible_pairs_checked": sum(count for _pid, _boundary, count, _ in results),
        "max_targets_per_boundary": max(count for _pid, _boundary, count, _ in results),
        "outside_targets": outside,
        "workers_observed": len({pid for pid, _boundary, _count, _ in results}),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=min(16, os.cpu_count() or 1))
    parser.add_argument("--max-boundary-twos", type=int, default=2)
    parser.add_argument("--show", type=int, default=5)
    parser.add_argument("--enumerate-boundary-twos", nargs="*", type=int)
    parser.add_argument("--target-limit", type=int, default=10000)
    parser.add_argument("--punctured-layer", action="store_true")
    parser.add_argument("--classify-65-sector", action="store_true")
    arguments = parser.parse_args()
    if not 1 <= arguments.jobs <= 16:
        raise ValueError("jobs must lie in 1..16")
    if arguments.enumerate_boundary_twos is not None:
        targets = enumerate_compatible_targets(
            tuple(arguments.enumerate_boundary_twos),
            limit=arguments.target_limit,
        )
        print(json.dumps({
            "boundary_twos": arguments.enumerate_boundary_twos,
            "compatible_targets": len(targets),
            "targets": targets[:arguments.show],
            "limit_reached": len(targets) == arguments.target_limit,
        }, sort_keys=True))
        return
    if arguments.punctured_layer:
        candidates = search_punctured_layer(jobs=arguments.jobs)
        print(json.dumps({
            "boundary_words_searched": len(punctured_boundary_support()),
            "candidates_found": len(candidates),
            "workers_observed": len({candidate.worker_pid for candidate in candidates}),
            "best": [
                {
                    "boundary_twos": candidate.boundary_twos,
                    "target_nonzero": candidate.target_nonzero,
                }
                for candidate in candidates[:arguments.show]
            ],
        }, sort_keys=True))
        return
    if arguments.classify_65_sector:
        print(json.dumps(classify_65_sector(jobs=arguments.jobs), sort_keys=True))
        return
    candidates = search_candidates(
        jobs=arguments.jobs,
        max_twos=arguments.max_boundary_twos,
    )
    print(json.dumps({
        "boundary_words_searched": len(candidate_boundaries(
            arguments.max_boundary_twos
        )),
        "candidates_found": len(candidates),
        "workers_observed": len({candidate.worker_pid for candidate in candidates}),
        "best": [
            {
                "boundary_twos": candidate.boundary_twos,
                "target_nonzero": candidate.target_nonzero,
            }
            for candidate in candidates[:arguments.show]
        ],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
