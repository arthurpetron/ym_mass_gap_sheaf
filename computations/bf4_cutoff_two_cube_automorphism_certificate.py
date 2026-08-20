"""Exact finite data for spatial cube automorphisms of the BF4 factor graph.

The signed permutation group of the three spatial axes has order 48.  This
producer derives its actions directly on the corrected-slab plaquettes and
links, then checks that every induced permutation preserves

* the 24 fixed-interface coordinates;
* the 20 fixed-link scopes;
* the 48 lower-link constraints for every one of the 65 sector states; and
* the six distinguished lower-cube faces.

The output is untrusted certificate data.  Lean consumes explicit coordinate
and factor permutations and independently checks every bounded local factor
equation against the production definitions.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing
import os
from concurrent.futures import ProcessPoolExecutor
from itertools import permutations, product

import networkx as nx

from computations.bf4_cutoff_two_65_sector_spectrum_scout import sector_states
from computations.bf4_cutoff_two_cube_boundary_row import (
    CUBE_FACE_IDS,
    EXPECTED_FIXED_FACE_IDS,
)
from computations.bf4_cutoff_two_cube_gram_diagonal import fixed_geometry
from computations.bf4_cutoff_two_krylov_edge_scout import lower_link_constraints
from computations.bf4_cutoff_two_vacuum_column import EXPECTED_LOWER_FACE_IDS
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import Link4, Plaquette4
from computations.exact_haar_network import invariant_multiplicity
from computations.general_cutoff_coherence_scout import slab_link_incidence


AxisPermutation = tuple[int, int, int]
AxisFlips = tuple[int, int, int]


def transform_plaquette(
    plaquette: Plaquette4,
    axis_permutation: AxisPermutation,
    flips: AxisFlips,
) -> Plaquette4:
    """Apply a signed spatial permutation to a positive plaquette."""

    vertex, plane = plaquette
    target_vertex = [0, 0, 0, vertex[3]]
    for source_axis in range(3):
        target_axis = axis_permutation[source_axis]
        if flips[source_axis]:
            # A reflected positive interval has base 1 - (base + 1).
            target_vertex[target_axis] = (
                -vertex[source_axis]
                if source_axis in plane
                else 1 - vertex[source_axis]
            )
        else:
            target_vertex[target_axis] = vertex[source_axis]
    target_plane = tuple(sorted(
        axis_permutation[axis] if axis < 3 else 3
        for axis in plane
    ))
    return tuple(target_vertex), target_plane  # type: ignore[return-value]


def transform_link(
    link: Link4,
    axis_permutation: AxisPermutation,
    flips: AxisFlips,
) -> Link4:
    """Apply the same signed permutation to a positive oriented link."""

    vertex, direction = link
    target_vertex = [0, 0, 0, vertex[3]]
    for source_axis in range(3):
        target_axis = axis_permutation[source_axis]
        if flips[source_axis]:
            target_vertex[target_axis] = (
                -vertex[source_axis]
                if direction == source_axis
                else 1 - vertex[source_axis]
            )
        else:
            target_vertex[target_axis] = vertex[source_axis]
    target_direction = (
        axis_permutation[direction] if direction < 3 else direction
    )
    return tuple(target_vertex), target_direction  # type: ignore[return-value]


def _ordered_links(direction: int) -> tuple[Link4, ...]:
    incidence = slab_link_incidence(1)
    if direction == 3:
        return tuple(
            link for link in incidence
            if link[1] == 3 and link[0][3] == 0
        )
    return tuple(
        link for link in incidence
        if link[1] < 3 and link[0][3] == 0
    )


def _cube_position_action(
    axis_permutation: AxisPermutation,
    flips: AxisFlips,
) -> tuple[int, ...]:
    """Action on the six face positions, grouped into opposite pairs."""

    opposite_pairs = ((0, 3), (1, 4), (2, 5))
    image = [0] * 6
    for axis, pair in enumerate(opposite_pairs):
        target_pair = opposite_pairs[axis_permutation[axis]]
        for side, source_position in enumerate(pair):
            image[source_position] = target_pair[side ^ flips[axis]]
    return tuple(image)


def _sector_state_action(cube_action: tuple[int, ...]) -> tuple[int, ...]:
    answer = [0]
    for source_mask in range(64):
        target_mask = 0
        for source_position, target_position in enumerate(cube_action):
            if source_mask & (1 << source_position):
                target_mask |= 1 << target_position
        answer.append(target_mask + 1)
    return tuple(answer)


def _source_factor_table(
    state: tuple[int, ...], constraint_index: int,
) -> tuple[int, ...]:
    constraint = lower_link_constraints()[constraint_index]
    lower = tuple(state[index] for index in constraint.lower_variables)
    if not constraint.fixed_face_ids:
        return (invariant_multiplicity(lower),)
    return tuple(
        invariant_multiplicity(lower + (boundary_spin,))
        for boundary_spin in range(3)
    )


def _factor_graph_action(
    state_permutation: tuple[int, ...],
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """Find one colored factor-graph isomorphism implementing the state action."""

    _fixed_ids, fixed_scopes = fixed_geometry()
    constraints = lower_link_constraints()
    states = sector_states()
    variable_of = {
        face_id: variable
        for variable, face_id in enumerate(EXPECTED_FIXED_FACE_IDS)
    }

    source_graph = nx.Graph()
    target_graph = nx.Graph()
    source_signatures = tuple(
        tuple(_source_factor_table(state, factor_index) for state in states)
        for factor_index in range(48)
    )
    target_signatures = tuple(
        tuple(
            _source_factor_table(states[state_permutation[state_index]],
                                 factor_index)
            for state_index in range(65)
        )
        for factor_index in range(48)
    )
    source_unary_at: list[list[tuple[tuple[int, ...], ...]]] = [
        [] for _ in range(24)
    ]
    target_unary_at: list[list[tuple[tuple[int, ...], ...]]] = [
        [] for _ in range(24)
    ]
    for factor_index, constraint in enumerate(constraints):
        if constraint.fixed_face_ids:
            variable = variable_of[constraint.fixed_face_ids[0]]
            source_unary_at[variable].append(source_signatures[factor_index])
            target_unary_at[variable].append(target_signatures[factor_index])
    for variable in range(24):
        node = ("v", variable)
        source_graph.add_node(node, color=(
            "variable", tuple(sorted(source_unary_at[variable]))
        ))
        target_graph.add_node(node, color=(
            "variable", tuple(sorted(target_unary_at[variable]))
        ))
    for factor_index, scope in enumerate(fixed_scopes):
        node = ("f", factor_index)
        color = ("fixed", len(scope))
        source_graph.add_node(node, color=color)
        target_graph.add_node(node, color=color)
        for variable in scope:
            source_graph.add_edge(node, ("v", variable))
            target_graph.add_edge(node, ("v", variable))
    matcher = nx.algorithms.isomorphism.GraphMatcher(
        source_graph,
        target_graph,
        node_match=nx.algorithms.isomorphism.categorical_node_match(
            "color", None
        ),
    )
    coordinate_actions = {
        tuple(mapping[("v", index)][1] for index in range(24))
        for mapping in matcher.isomorphisms_iter()
    }
    if not coordinate_actions:
        raise AssertionError("cube action has no colored factor-graph lift")
    fixed_coordinate_permutation = min(coordinate_actions)

    def mapped_scope(scope: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(sorted(fixed_coordinate_permutation[index]
                            for index in scope))

    fixed_link_permutation_list: list[int] = []
    unused_fixed = set(range(20))
    for scope in fixed_scopes:
        target_index = min(
            index for index in unused_fixed
            if fixed_scopes[index] == mapped_scope(scope)
        )
        fixed_link_permutation_list.append(target_index)
        unused_fixed.remove(target_index)

    lower_scopes = tuple(
        tuple(variable_of[face_id] for face_id in constraint.fixed_face_ids)
        for constraint in constraints
    )
    lower_link_permutation_list: list[int] = []
    unused_lower = set(range(48))
    for source_index, scope in enumerate(lower_scopes):
        target_index = min(
            index for index in unused_lower
            if lower_scopes[index] == mapped_scope(scope)
            and target_signatures[index] == source_signatures[source_index]
        )
        lower_link_permutation_list.append(target_index)
        unused_lower.remove(target_index)
    fixed_link_permutation = tuple(fixed_link_permutation_list)
    lower_link_permutation = tuple(lower_link_permutation_list)
    return (
        fixed_coordinate_permutation,
        fixed_link_permutation,
        lower_link_permutation,
    )


def action_data(
    axis_permutation: AxisPermutation,
    flips: AxisFlips,
) -> dict[str, object]:
    cube_position_permutation = _cube_position_action(
        axis_permutation, flips
    )
    state_permutation = _sector_state_action(cube_position_permutation)
    (
        fixed_coordinate_permutation,
        fixed_link_permutation,
        lower_link_permutation,
    ) = _factor_graph_action(state_permutation)
    if sorted(fixed_link_permutation) != list(range(20)):
        raise AssertionError("fixed-link action is not a permutation")
    if sorted(lower_link_permutation) != list(range(48)):
        raise AssertionError("lower-link action is not a permutation")

    _fixed_ids, fixed_scopes = fixed_geometry()
    for source_index, target_index in enumerate(fixed_link_permutation):
        mapped_scope = tuple(sorted(
            fixed_coordinate_permutation[index]
            for index in fixed_scopes[source_index]
        ))
        if mapped_scope != fixed_scopes[target_index]:
            raise AssertionError("fixed-link scope transport failed")

    constraints = lower_link_constraints()
    states = sector_states()

    fixed_variable_of = {
        face_id: variable
        for variable, face_id in enumerate(EXPECTED_FIXED_FACE_IDS)
    }
    for state_index, source_state in enumerate(states):
        target_state = states[state_permutation[state_index]]
        for source_link, target_link in enumerate(lower_link_permutation):
            source_constraint = constraints[source_link]
            target_constraint = constraints[target_link]
            source_lower = tuple(
                source_state[index]
                for index in source_constraint.lower_variables
            )
            target_lower = tuple(
                target_state[index]
                for index in target_constraint.lower_variables
            )
            mapped_fixed = tuple(sorted(
                fixed_coordinate_permutation[fixed_variable_of[face_id]]
                for face_id in source_constraint.fixed_face_ids
            ))
            target_fixed = tuple(sorted(
                fixed_variable_of[face_id]
                for face_id in target_constraint.fixed_face_ids
            ))
            if mapped_fixed != target_fixed:
                raise AssertionError("lower-link fixed scope transport failed")
            for boundary_spin in range(3):
                source_spins = source_lower + (
                    (boundary_spin,) if source_constraint.fixed_face_ids else ()
                )
                target_spins = target_lower + (
                    (boundary_spin,) if target_constraint.fixed_face_ids else ()
                )
                if invariant_multiplicity(source_spins) != invariant_multiplicity(
                    target_spins
                ):
                    raise AssertionError("lower-link local table transport failed")

    return {
        "axis_permutation": axis_permutation,
        "flips": flips,
        "fixed_face_ids": EXPECTED_FIXED_FACE_IDS,
        "fixed_coordinate_permutation": fixed_coordinate_permutation,
        "fixed_link_permutation": fixed_link_permutation,
        "lower_link_permutation": lower_link_permutation,
        "cube_position_permutation": cube_position_permutation,
        "state_permutation": state_permutation,
    }


def _action_task(
    specification: tuple[AxisPermutation, AxisFlips],
) -> tuple[int, tuple[AxisPermutation, AxisFlips], dict[str, object] | None]:
    try:
        action = action_data(*specification)
    except AssertionError:
        action = None
    return os.getpid(), specification, action


def all_actions(
    *, jobs: int = 1,
) -> tuple[tuple[dict[str, object], ...], tuple[tuple[AxisPermutation, AxisFlips], ...], int]:
    specifications = tuple(
        (axis_permutation, flips)
        for axis_permutation in permutations(range(3))
        for flips in product((0, 1), repeat=3)
    )
    if not 1 <= jobs <= 16:
        raise ValueError("jobs must lie in 1..16")
    if jobs == 1:
        results = tuple(_action_task(specification)
                        for specification in specifications)
    else:
        context = multiprocessing.get_context("spawn")
        with ProcessPoolExecutor(max_workers=jobs, mp_context=context) as pool:
            results = tuple(pool.map(_action_task, specifications, chunksize=1))
    actions = tuple(action for _pid, _specification, action in results
                    if action is not None)
    failures = tuple(specification
                     for _pid, specification, action in results
                     if action is None)
    signatures = {
        (action["fixed_coordinate_permutation"], action["state_permutation"])
        for action in actions
    }
    if len(signatures) != len(actions):
        raise AssertionError("distinct lifted actions acquired duplicate signatures")
    workers_observed = len({pid for pid, _specification, _action in results})
    if jobs > 1 and workers_observed != jobs:
        raise AssertionError("not every requested worker was observed")
    return actions, failures, workers_observed


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--action",
        choices=("axis-swap-01", "all-summary"),
        default="axis-swap-01",
    )
    parser.add_argument("--jobs", type=int, default=1)
    arguments = parser.parse_args()
    if arguments.action == "axis-swap-01":
        answer = action_data((1, 0, 2), (0, 0, 0))
    else:
        actions, failures, workers_observed = all_actions(jobs=arguments.jobs)
        answer = {
            "requested_cube_actions": 48,
            "pointwise_factor_graph_lifts": len(actions),
            "non_pointwise_actions": len(failures),
            "failed_specifications": failures,
            "distinct_fixed_actions": len({
                action["fixed_coordinate_permutation"] for action in actions
            }),
            "distinct_sector_actions": len({
                action["state_permutation"] for action in actions
            }),
            "all_local_factor_checks": True,
            "workers_observed": workers_observed,
        }
    print(json.dumps(answer, sort_keys=True))


if __name__ == "__main__":
    main()
