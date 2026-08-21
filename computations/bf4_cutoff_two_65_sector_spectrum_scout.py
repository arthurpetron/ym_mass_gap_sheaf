"""Exact scout for the cutoff-two 65-state physical conditional block.

The sector order matches Lean:

* the fundamental cube first;
* then the Cartesian binary enumeration of the six cube-face labels, doubled
  from ``0/1`` to ``0/2``.

For each unordered pair, this program contracts the genuine fixed-interface
factor graph exactly over ``Fraction``.  Row-normalizing the symmetric raw
kernel gives the physical conditional Markov block; a floating symmetric
similarity transform is used only to scout its eigenvalues.

This program is untrusted.  Exact entries, row sums, and any eventual spectral
certificate must be regenerated and checked by Lean.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing
import os
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from itertools import permutations, product
from collections import defaultdict

import numpy as np

from computations.bf4_cutoff_two_cube_boundary_row import (
    CUBE_FACE_IDS,
    EXPECTED_FIXED_FACE_IDS,
)
from computations.bf4_cutoff_two_cube_gram_diagonal import fixed_geometry
from computations.bf4_cutoff_two_krylov_edge_scout import (
    LinkConstraint,
    lower_link_constraints,
)
from computations.bf4_cutoff_two_vacuum_column import (
    DOMAIN,
    EXPECTED_LOWER_FACE_IDS,
    Factor,
    _eliminate,
    _factor_from_function,
    _induced_order,
    coeff_w,
)
from computations.exact_haar_network import invariant_multiplicity


def sector_states() -> tuple[tuple[int, ...], ...]:
    cube = tuple(
        1 if face_id in CUBE_FACE_IDS else 0
        for face_id in EXPECTED_LOWER_FACE_IDS
    )
    doubled = tuple(
        tuple(
            2 * bits[CUBE_FACE_IDS.index(face_id)]
            if face_id in CUBE_FACE_IDS else 0
            for face_id in EXPECTED_LOWER_FACE_IDS
        )
        for bits in product((0, 1), repeat=len(CUBE_FACE_IDS))
    )
    states = (cube,) + doubled
    if len(states) != 65 or len(set(states)) != 65:
        raise AssertionError("sector enumeration is not 65 distinct states")
    return states


def _boundary_heat_factors(coupling: Fraction) -> tuple[Factor, ...]:
    return tuple(
        _factor_from_function(
            (variable,),
            lambda environment, variable=variable:
                coeff_w(coupling, environment[variable]),
        )
        for variable in range(len(EXPECTED_FIXED_FACE_IDS))
    )


def _fixed_link_factors() -> tuple[Factor, ...]:
    _fixed_face_ids, fixed_link_scopes = fixed_geometry()
    return tuple(
        _factor_from_function(
            scope,
            lambda environment, scope=scope:
                invariant_multiplicity(
                    tuple(environment[variable] for variable in scope)
                ),
        )
        for scope in fixed_link_scopes
    )


def _source_link_factors(labels: tuple[int, ...]) -> tuple[Factor, ...]:
    variable_of_fixed = {
        face_id: variable
        for variable, face_id in enumerate(EXPECTED_FIXED_FACE_IDS)
    }
    factors: list[Factor] = []
    for constraint in lower_link_constraints():
        lower = tuple(labels[index] for index in constraint.lower_variables)
        fixed = constraint.fixed_face_ids
        if not fixed:
            factors.append(Factor((), (Fraction(invariant_multiplicity(lower)),)))
        elif len(fixed) == 1:
            variable = variable_of_fixed[fixed[0]]
            factors.append(Factor(
                (variable,),
                tuple(Fraction(invariant_multiplicity(lower + (spin,)))
                      for spin in DOMAIN),
            ))
        else:
            raise AssertionError("production lower-link scope is not unary")
    if len(factors) != 48:
        raise AssertionError("expected 48 production lower-link factors")
    return tuple(factors)


def _lower_heat_factor(coupling: Fraction, labels: tuple[int, ...]) -> Fraction:
    answer = Fraction(1)
    for label in labels:
        answer *= coeff_w(coupling, label)
    return answer


def _common_factors(coupling: Fraction) -> tuple[Factor, ...]:
    return _boundary_heat_factors(coupling) + _fixed_link_factors()


def _elimination_order(coupling: Fraction) -> tuple[tuple[int, ...], int]:
    states = sector_states()
    factors = (
        _common_factors(coupling)
        + _source_link_factors(states[0])
        + _source_link_factors(states[0])
    )
    order, width, _entries = _induced_order(
        tuple(factor.scope for factor in factors), 0
    )
    if tuple(sorted(order)) != tuple(range(24)):
        raise AssertionError("elimination order omitted a fixed variable")
    return order, width


def _kernel_entry(
    coupling: Fraction,
    left: tuple[int, ...],
    right: tuple[int, ...],
    order: tuple[int, ...],
) -> Fraction:
    factors = (
        _common_factors(coupling)
        + _source_link_factors(left)
        + _source_link_factors(right)
    )
    for variable in order:
        factors, _step, _pids = _eliminate(factors, variable, None, 1)
    if any(factor.scope for factor in factors):
        raise AssertionError("entry contraction left a non-scalar factor")
    interface_sum = Fraction(1)
    for factor in factors:
        interface_sum *= factor.table[0]
    return (
        _lower_heat_factor(coupling, left)
        * _lower_heat_factor(coupling, right)
        * interface_sum
    )


def _entry_task(
    task: tuple[str, int, int, tuple[int, ...]],
) -> tuple[int, int, int, Fraction]:
    coupling_text, left_index, right_index, order = task
    coupling = Fraction(coupling_text)
    states = sector_states()
    value = _kernel_entry(
        coupling, states[left_index], states[right_index], order
    )
    return os.getpid(), left_index, right_index, value


def _exact_generalized_eigenvalue(
    kernel: list[list[Fraction]],
    row_sums: tuple[Fraction, ...],
    vector: tuple[int, ...],
) -> Fraction | None:
    action = tuple(
        sum((kernel[row][column] * vector[column]
             for column in range(len(vector))), Fraction(0))
        for row in range(len(vector))
    )
    candidate: Fraction | None = None
    for row, coordinate in enumerate(vector):
        denominator = row_sums[row] * coordinate
        if denominator == 0:
            if action[row] != 0:
                return None
            continue
        ratio = action[row] / denominator
        if candidate is None:
            candidate = ratio
        elif ratio != candidate:
            return None
    return candidate


def _walsh_eigenvalue_summary(
    kernel: list[list[Fraction]],
    row_sums: tuple[Fraction, ...],
) -> dict[str, object]:
    by_degree: dict[int, list[Fraction | None]] = defaultdict(list)
    for selector in range(1, 64):
        degree = selector.bit_count()
        vector = (0,) + tuple(
            -1 if (selector & mask).bit_count() % 2 else 1
            for mask in range(64)
        )
        by_degree[degree].append(
            _exact_generalized_eigenvalue(kernel, row_sums, vector)
        )
    answer: dict[str, object] = {}
    for degree in range(1, 7):
        values = by_degree[degree]
        exact = tuple(value for value in values if value is not None)
        answer[str(degree)] = {
            "vectors": len(values),
            "exact_eigenvectors": len(exact),
            "eigenvalues": sorted({str(value) for value in exact}),
        }
    return answer


def _permutation_invariance_summary(
    kernel: list[list[Fraction]],
    row_sums: tuple[Fraction, ...],
) -> dict[str, int]:
    classes: dict[tuple[object, ...], set[Fraction]] = defaultdict(set)
    for left in range(65):
        for right in range(65):
            value = kernel[left][right] / row_sums[left]
            if left == 0 and right == 0:
                key: tuple[object, ...] = ("cube", "cube")
            elif left == 0:
                key = ("cube", (right - 1).bit_count())
            elif right == 0:
                key = ((left - 1).bit_count(), "cube")
            else:
                left_mask = left - 1
                right_mask = right - 1
                key = (
                    left_mask.bit_count(),
                    right_mask.bit_count(),
                    (left_mask & right_mask).bit_count(),
                )
            classes[key].add(value)
    return {
        "orbit_keys": len(classes),
        "max_distinct_values_per_s6_key": max(map(len, classes.values())),
        "keys_with_multiple_values": sum(len(values) > 1
                                          for values in classes.values()),
    }


def _cube_automorphism_summary(
    kernel: list[list[Fraction]],
) -> dict[str, int | bool]:
    """Audit the 48 permutations preserving the cube's opposite-face pairs."""

    # Positions refer to the binary mask order induced by CUBE_FACE_IDS.
    opposite_pairs = ((0, 3), (1, 4), (2, 5))
    actions: list[tuple[int, ...]] = []
    for axis_permutation in permutations(range(3)):
        for flips in product((0, 1), repeat=3):
            image = [0] * 6
            for axis, pair in enumerate(opposite_pairs):
                target_pair = opposite_pairs[axis_permutation[axis]]
                for side, source_position in enumerate(pair):
                    image[source_position] = target_pair[side ^ flips[axis]]
            actions.append(tuple(image))
    if len(actions) != 48 or len(set(actions)) != 48:
        raise AssertionError("cube automorphism construction is not order 48")

    def act_state(index: int, action: tuple[int, ...]) -> int:
        if index == 0:
            return 0
        source_mask = index - 1
        target_mask = 0
        for source_position, target_position in enumerate(action):
            if source_mask & (1 << source_position):
                target_mask |= 1 << target_position
        return target_mask + 1

    invariant = all(
        kernel[left][right]
        == kernel[act_state(left, action)][act_state(right, action)]
        for action in actions
        for left in range(65)
        for right in range(65)
    )
    unseen = {(left, right)
              for left in range(65) for right in range(left, 65)}
    representatives: list[tuple[int, int]] = []
    while unseen:
        representative = min(unseen)
        orbit = {
            tuple(sorted((
                act_state(representative[0], action),
                act_state(representative[1], action),
            )))
            for action in actions
        }
        unseen.difference_update(orbit)
        representatives.append(representative)
    return {
        "actions": len(actions),
        "raw_kernel_invariant": invariant,
        "unordered_pair_orbits": len(representatives),
        "nonzero_representative_orbits": sum(
            kernel[left][right] != 0 for left, right in representatives
        ),
    }


def _rank_mod_prime(matrix: list[list[Fraction]], prime: int) -> int:
    """Return the rank after reducing a rational matrix modulo ``prime``."""
    reduced = [
        [
            (entry.numerator % prime)
            * pow(entry.denominator % prime, -1, prime)
            % prime
            for entry in row
        ]
        for row in matrix
    ]
    rows = len(reduced)
    columns = len(reduced[0]) if reduced else 0
    pivot_row = 0
    for column in range(columns):
        pivot = next(
            (row for row in range(pivot_row, rows)
             if reduced[row][column] != 0),
            None,
        )
        if pivot is None:
            continue
        reduced[pivot_row], reduced[pivot] = reduced[pivot], reduced[pivot_row]
        inverse = pow(reduced[pivot_row][column], -1, prime)
        reduced[pivot_row] = [value * inverse % prime
                              for value in reduced[pivot_row]]
        for row in range(rows):
            if row == pivot_row:
                continue
            coefficient = reduced[row][column]
            if coefficient:
                reduced[row] = [
                    (left - coefficient * right) % prime
                    for left, right in zip(reduced[row], reduced[pivot_row])
                ]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def _target_eigenvalue_summary(
    kernel: list[list[Fraction]],
    row_sums: tuple[Fraction, ...],
    target: Fraction,
) -> dict[str, object]:
    pencil = [
        [
            kernel[row][column]
            - (target * row_sums[row] if row == column else 0)
            for column in range(len(kernel))
        ]
        for row in range(len(kernel))
    ]
    primes = (1_000_000_007, 1_000_000_009, 1_000_000_021)
    ranks = {str(prime): _rank_mod_prime(pencil, prime) for prime in primes}
    return {
        "target": str(target),
        "modular_ranks": ranks,
        "modular_nullities": {
            prime: len(kernel) - rank for prime, rank in ranks.items()
        },
    }


def _mean_zero_restriction(
    kernel: list[list[Fraction]],
    row_sums: tuple[Fraction, ...],
    target: Fraction,
) -> list[list[Fraction]]:
    """Restrict ``target * D - K`` to the ``D``-mean-zero hyperplane."""
    return _mean_zero_signed_restriction(
        kernel, row_sums, target, kernel_sign=Fraction(-1)
    )


def _mean_zero_signed_restriction(
    kernel: list[list[Fraction]],
    row_sums: tuple[Fraction, ...],
    target: Fraction,
    *,
    kernel_sign: Fraction,
) -> list[list[Fraction]]:
    """Restrict ``target * D + kernel_sign * K`` to weighted mean zero."""
    size = len(kernel)
    pencil = [
        [
            (target * row_sums[row] if row == column else Fraction(0))
            + kernel_sign * kernel[row][column]
            for column in range(size)
        ]
        for row in range(size)
    ]
    d0 = row_sums[0]
    return [
        [
            pencil[i][j]
            - row_sums[j] * pencil[i][0] / d0
            - row_sums[i] * pencil[0][j] / d0
            + row_sums[i] * row_sums[j] * pencil[0][0] / (d0 * d0)
            for j in range(1, size)
        ]
        for i in range(1, size)
    ]


def _rank_one_penalized_matrix(
    kernel: list[list[Fraction]],
    row_sums: tuple[Fraction, ...],
    target: Fraction,
    penalty: Fraction,
) -> list[list[Fraction]]:
    """Return ``target D - K + penalty * d d^T`` exactly."""
    size = len(kernel)
    return [
        [
            (target * row_sums[row] if row == column else Fraction(0))
            - kernel[row][column]
            + penalty * row_sums[row] * row_sums[column]
            for column in range(size)
        ]
        for row in range(size)
    ]


def _symbolic_pair_batch_scope_summary(
    coupling: Fraction, order: tuple[int, ...]
) -> dict[str, object]:
    """Scope-only estimate keeping two 65-valued state indices symbolic."""
    left_state = 24
    right_state = 25
    scopes = [factor.scope for factor in _common_factors(coupling)]
    scopes += [tuple(sorted(factor.scope + (left_state,)))
               for factor in _source_link_factors(sector_states()[0])]
    scopes += [tuple(sorted(factor.scope + (right_state,)))
               for factor in _source_link_factors(sector_states()[0])]
    maximum_scope = 0
    maximum_entries = 0
    step_summaries: list[dict[str, int]] = []
    for variable in order:
        bucket = [scope for scope in scopes if variable in scope]
        outside = [scope for scope in scopes if variable not in scope]
        union = set().union(*map(set, bucket)) if bucket else {variable}
        result = tuple(sorted(union - {variable}))
        scope_entries = 1
        for coordinate in result:
            scope_entries *= 65 if coordinate in (left_state, right_state) else 3
        maximum_scope = max(maximum_scope, len(result))
        maximum_entries = max(maximum_entries, scope_entries)
        step_summaries.append({
            "variable": variable,
            "result_scope": len(result),
            "result_entries": scope_entries,
        })
        scopes = outside + [result]
    return {
        "maximum_result_scope": maximum_scope,
        "maximum_dense_result_entries": maximum_entries,
        "terminal_scopes": [list(scope) for scope in scopes],
        "steps": step_summaries,
    }


def _exact_ldl_summary(matrix: list[list[Fraction]]) -> dict[str, object]:
    """Compute and exactly recheck an unpivoted rational LDL factorization."""
    size = len(matrix)
    lower = [[Fraction(0) for _ in range(size)] for _ in range(size)]
    diagonal: list[Fraction] = []
    for column in range(size):
        lower[column][column] = Fraction(1)
        pivot = matrix[column][column] - sum(
            (lower[column][k] * lower[column][k] * diagonal[k]
             for k in range(column)),
            Fraction(0),
        )
        if pivot == 0:
            raise AssertionError(f"zero LDL pivot at column {column}")
        diagonal.append(pivot)
        for row in range(column + 1, size):
            residual = matrix[row][column] - sum(
                (lower[row][k] * lower[column][k] * diagonal[k]
                 for k in range(column)),
                Fraction(0),
            )
            lower[row][column] = residual / pivot
    for row in range(size):
        for column in range(size):
            reconstructed = sum(
                (lower[row][k] * diagonal[k] * lower[column][k]
                 for k in range(size)),
                Fraction(0),
            )
            if reconstructed != matrix[row][column]:
                raise AssertionError("exact LDL reconstruction failed")
    entries = diagonal + [
        lower[row][column]
        for row in range(size)
        for column in range(row)
    ]
    return {
        "dimension": size,
        "positive_pivots": sum(pivot > 0 for pivot in diagonal),
        "negative_pivots": sum(pivot < 0 for pivot in diagonal),
        "zero_pivots": sum(pivot == 0 for pivot in diagonal),
        "min_pivot_float": min(map(float, diagonal)),
        "max_numerator_bits": max(abs(entry.numerator).bit_length()
                                  for entry in entries),
        "max_denominator_bits": max(entry.denominator.bit_length()
                                    for entry in entries),
        "exact_reconstruction": True,
    }


def compute(*, coupling: Fraction, jobs: int) -> dict[str, object]:
    if not 1 <= jobs <= 16:
        raise ValueError("jobs must lie in 1..16")
    states = sector_states()
    order, width = _elimination_order(coupling)
    pairs = tuple(
        (str(coupling), left, right, order)
        for left in range(len(states))
        for right in range(left, len(states))
    )
    if jobs == 1:
        results = tuple(_entry_task(task) for task in pairs)
    else:
        context = multiprocessing.get_context("spawn")
        with ProcessPoolExecutor(max_workers=jobs, mp_context=context) as pool:
            results = tuple(pool.map(_entry_task, pairs, chunksize=1))

    kernel = [[Fraction(0) for _ in states] for _ in states]
    for _pid, left, right, value in results:
        kernel[left][right] = value
        kernel[right][left] = value
    if any(kernel[i][j] != kernel[j][i]
           for i in range(65) for j in range(65)):
        raise AssertionError("raw kernel lost exact symmetry")
    row_sums = tuple(sum(row, Fraction(0)) for row in kernel)
    if any(row_sum <= 0 for row_sum in row_sums):
        raise AssertionError("a sector row has nonpositive mass")

    symmetric_similarity = np.array([
        [float(kernel[i][j]) / np.sqrt(float(row_sums[i] * row_sums[j]))
         for j in range(65)]
        for i in range(65)
    ], dtype=np.float64)
    eigenvalues = np.linalg.eigvalsh(symmetric_similarity)
    eigenvalues.sort()
    descending = tuple(float(value) for value in eigenvalues[::-1])
    second = descending[1]
    upper_sixteenth = _mean_zero_signed_restriction(
        kernel, row_sums, Fraction(1, 16), kernel_sign=Fraction(-1)
    )
    lower_sixteenth = _mean_zero_signed_restriction(
        kernel, row_sums, Fraction(1, 16), kernel_sign=Fraction(1)
    )
    negative_upper_diagonals = tuple(
        (index + 1, upper_sixteenth[index][index])
        for index in range(len(upper_sixteenth))
        if upper_sixteenth[index][index] < 0
    )
    unordered_values = [kernel[left][right]
                        for left in range(65)
                        for right in range(left, 65)]
    return {
        "states": len(states),
        "unordered_entries": len(results),
        "nonzero_entries": sum(value != 0 for row in kernel for value in row),
        "unordered_nonzero_entries": sum(value != 0 for value in unordered_values),
        "distinct_unordered_entry_values": len(set(unordered_values)),
        "distinct_nonzero_unordered_entry_values":
            len({value for value in unordered_values if value != 0}),
        "distinct_row_sums": len(set(row_sums)),
        "elimination_width": width,
        "elimination_order": order,
        "workers_observed": len({pid for pid, _i, _j, _value in results}),
        "min_row_sum": str(min(row_sums)),
        "max_row_sum": str(max(row_sums)),
        "numerical_rank": int(np.linalg.matrix_rank(symmetric_similarity)),
        "largest_eigenvalues": descending[:12],
        "smallest_eigenvalue": descending[-1],
        "second_eigenvalue": second,
        "spectral_gap": 1.0 - second,
        "top_eigenvalue_error": abs(descending[0] - 1.0),
        "walsh_exact": _walsh_eigenvalue_summary(kernel, row_sums),
        "s6_invariance": _permutation_invariance_summary(kernel, row_sums),
        "cube_automorphisms": _cube_automorphism_summary(kernel),
        "target_48_over_49": _target_eigenvalue_summary(
            kernel, row_sums, Fraction(48, 49)
        ),
        "mean_zero_ldl_49_over_50": _exact_ldl_summary(
            _mean_zero_restriction(kernel, row_sums, Fraction(49, 50))
        ),
        "mean_zero_upper_1_over_16": {
            "ldl": _exact_ldl_summary(upper_sixteenth),
            "negative_coordinate_diagonals": [
                {"sector_index": index, "value": str(value)}
                for index, value in negative_upper_diagonals
            ],
        },
        "mean_zero_lower_1_over_16":
            _exact_ldl_summary(lower_sixteenth),
        "rank_one_penalized_ldl_49_over_50": _exact_ldl_summary(
            _rank_one_penalized_matrix(
                kernel, row_sums, Fraction(49, 50), Fraction(1)
            )
        ),
        "symbolic_pair_batch_scopes":
            _symbolic_pair_batch_scope_summary(coupling, order),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coupling", default="1/2")
    parser.add_argument("--jobs", type=int, default=min(16, os.cpu_count() or 1))
    arguments = parser.parse_args()
    print(json.dumps(
        compute(coupling=Fraction(arguments.coupling), jobs=arguments.jobs),
        sort_keys=True,
    ))


if __name__ == "__main__":
    main()
