"""Scout local source-support containment for the cutoff-two 65-state sector.

For every doubled-spin subset of the six distinguished cube faces, every
production lower link, and every ternary assignment of the incident fixed
faces, check the implication

    subset link multiplicity > 0  ==>  fundamental-cube multiplicity > 0.

This multiprocessing computation is an untrusted producer.  Its output is
only a design check for the later Lean certificate, which must recompute each
finite implication in the kernel.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing
import os
from concurrent.futures import ProcessPoolExecutor
from itertools import product

from computations.bf4_cutoff_two_cube_boundary_row import CUBE_FACE_IDS
from computations.bf4_cutoff_two_krylov_edge_scout import (
    LinkConstraint,
    lower_link_constraints,
)
from computations.bf4_cutoff_two_vacuum_column import EXPECTED_LOWER_FACE_IDS
from computations.exact_haar_network import invariant_multiplicity


def _lower_labels(mask: int, *, doubled: bool) -> tuple[int, ...]:
    selected = {
        face_id
        for bit, face_id in enumerate(CUBE_FACE_IDS)
        if mask & (1 << bit)
    }
    label = 2 if doubled else 1
    support = selected if doubled else set(CUBE_FACE_IDS)
    return tuple(
        label if face_id in support else 0
        for face_id in EXPECTED_LOWER_FACE_IDS
    )


def _incident_word(
    lower: tuple[int, ...],
    fixed: tuple[int, ...],
    constraint: LinkConstraint,
) -> tuple[int, ...]:
    return tuple(lower[index] for index in constraint.lower_variables) + fixed


def _check_mask(mask: int) -> dict[str, object]:
    constraints = lower_link_constraints()
    subset = _lower_labels(mask, doubled=True)
    cube = _lower_labels(mask, doubled=False)
    implications = 0
    positive_subset_words = 0
    counterexamples: list[dict[str, object]] = []
    max_fixed_arity = 0
    for link_index, constraint in enumerate(constraints):
        max_fixed_arity = max(max_fixed_arity, len(constraint.fixed_face_ids))
        for fixed in product((0, 1, 2), repeat=len(constraint.fixed_face_ids)):
            implications += 1
            subset_multiplicity = invariant_multiplicity(
                _incident_word(subset, fixed, constraint)
            )
            if subset_multiplicity <= 0:
                continue
            positive_subset_words += 1
            cube_multiplicity = invariant_multiplicity(
                _incident_word(cube, fixed, constraint)
            )
            if cube_multiplicity <= 0:
                counterexamples.append({
                    "link_index": link_index,
                    "lower_variables": constraint.lower_variables,
                    "fixed_face_ids": constraint.fixed_face_ids,
                    "fixed_labels": fixed,
                    "subset_word": _incident_word(subset, fixed, constraint),
                    "cube_word": _incident_word(cube, fixed, constraint),
                })
    return {
        "mask": mask,
        "pid": os.getpid(),
        "implications": implications,
        "positive_subset_words": positive_subset_words,
        "max_fixed_arity": max_fixed_arity,
        "counterexamples": counterexamples,
    }


def check_all(*, jobs: int) -> dict[str, object]:
    masks = tuple(range(64))
    if jobs == 1:
        results = tuple(_check_mask(mask) for mask in masks)
    else:
        context = multiprocessing.get_context("spawn")
        with ProcessPoolExecutor(max_workers=jobs, mp_context=context) as pool:
            results = tuple(pool.map(_check_mask, masks, chunksize=1))
    counterexamples = tuple(
        {"mask": result["mask"], **counterexample}
        for result in results
        for counterexample in result["counterexamples"]
    )
    return {
        "masks_checked": len(results),
        "links_per_mask": len(lower_link_constraints()),
        "local_implications_checked": sum(
            int(result["implications"]) for result in results
        ),
        "positive_subset_words": sum(
            int(result["positive_subset_words"]) for result in results
        ),
        "max_fixed_arity": max(
            int(result["max_fixed_arity"]) for result in results
        ),
        "workers_observed": len({int(result["pid"]) for result in results}),
        "counterexample_count": len(counterexamples),
        "first_counterexamples": counterexamples[:10],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=min(16, os.cpu_count() or 1))
    arguments = parser.parse_args()
    if not 1 <= arguments.jobs <= 16:
        raise ValueError("jobs must lie in 1..16")
    print(json.dumps(check_all(jobs=arguments.jobs), sort_keys=True))


if __name__ == "__main__":
    main()
