"""Exact Gram survey for binary surfaces on the four-cube boundary.

For a closed binary face surface ``S``, let

``O_S(g) = product_{f in S} chi_1(hol_f(g))``.

This module constructs the exact rational matrix

``G[S,T] = integral O_S(g) O_T(g) dg``

for all 128 GF(2)-closed surfaces in the boundary two-skeleton of the unit
four-cube.  Hyperoctahedral symmetry reduces its 8,256 unordered entries to
118 orbit representatives.  Intersecting representatives are evaluated by
the complete ``chi_1**2 = chi_0 + chi_2`` fusion sum; no amplitude lookup
table is used.

The diagonal has a useful closed form.  On one connected surface component,
the duplicate-strand expansion has only the all-zero and all-spin-one
channels, and hence contributes ``1 + 3**(chi - F)``.  Components factor.
This avoids an otherwise unnecessary ``2**16`` channel expansion for a
Clifford torus.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import Literal, TypeAlias, cast

from computations.exact_haar_network import GaugeFixedComplex
from computations.hypercube4d_survey import (
    Face,
    FaceMeta,
    hypercube,
    kernel_basis,
    mask_orbits,
    pair_orbits,
    surface_cell_counts,
    surface_pair_fusion_value,
    surfaces,
    symmetry_maps,
)

RationalMatrix: TypeAlias = tuple[tuple[Fraction, ...], ...]
PairKind: TypeAlias = Literal["diagonal", "disjoint", "intersecting"]


@dataclass(frozen=True)
class PairOrbitRecord:
    """One exact unordered-pair orbit under four-cube symmetry."""

    representative: tuple[int, int]
    size: int
    kind: PairKind
    value: Fraction


@dataclass(frozen=True)
class SurfaceGramSurvey:
    """Complete exact data for the 128 by 128 surface Gram matrix."""

    surface_masks: tuple[int, ...]
    surface_orbits: tuple[tuple[int, ...], ...]
    pair_orbits: tuple[PairOrbitRecord, ...]
    matrix: RationalMatrix

    @property
    def distinct_entries(self) -> tuple[Fraction, ...]:
        """Return the increasing exact entry spectrum."""

        return tuple(sorted({value for row in self.matrix for value in row}))

    @property
    def unordered_entry_multiplicities(self) -> Counter[Fraction]:
        """Count values on the upper triangle, diagonal included."""

        return Counter(record.value for record in self.pair_orbits for _ in range(record.size))


def _surface_component_masks(
    complex_: GaugeFixedComplex,
    faces: tuple[Face, ...],
    mask: int,
) -> tuple[int, ...]:
    """Split a binary surface into edge-connected face components."""

    if mask < 0 or mask >> len(faces):
        raise ValueError("surface mask leaves the supplied face set")
    face_edges = tuple({edge for edge, _orientation in face} for face in faces)
    remaining = {index for index in range(len(faces)) if (mask >> index) & 1}
    components: list[int] = []
    while remaining:
        seed = min(remaining)
        remaining.remove(seed)
        stack = [seed]
        component = 0
        while stack:
            face_index = stack.pop()
            component |= 1 << face_index
            adjacent = {other for other in remaining if face_edges[face_index] & face_edges[other]}
            remaining.difference_update(adjacent)
            stack.extend(sorted(adjacent, reverse=True))
        components.append(component)
    return tuple(sorted(components))


def surface_diagonal_value(
    complex_: GaugeFixedComplex,
    faces: tuple[Face, ...],
    mask: int,
) -> Fraction:
    """Evaluate ``integral O_S**2`` by the componentwise 2D formula."""

    value = Fraction(1)
    for component in _surface_component_masks(complex_, faces, mask):
        _vertices, _edges, face_count, euler = surface_cell_counts(
            complex_,
            faces,
            component,
        )
        value *= Fraction(1) + Fraction(3) ** (euler - face_count)
    return value


def binary_surface_pair_value(
    complex_: GaugeFixedComplex,
    faces: tuple[Face, ...],
    meta: tuple[FaceMeta, ...],
    left: int,
    right: int,
) -> tuple[PairKind, Fraction]:
    """Evaluate one binary-surface pair by the cheapest exact route."""

    if left == right:
        return "diagonal", surface_diagonal_value(complex_, faces, left)
    if (left & right) == 0:
        _vertices, _edges, face_count, euler = surface_cell_counts(
            complex_,
            faces,
            left | right,
        )
        return "disjoint", Fraction(2) ** (euler - face_count)
    return "intersecting", surface_pair_fusion_value(meta, left, right)


@cache
def build_surface_gram_survey() -> SurfaceGramSurvey:
    """Construct and cache the complete exact 128-surface Gram survey."""

    complex_, face_list, meta_list = hypercube()
    faces = tuple(face_list)
    meta = tuple(meta_list)
    surface_masks = tuple(surfaces(kernel_basis(complex_, faces)))
    maps = symmetry_maps(meta)
    surface_orbit_rows = tuple(mask_orbits(surface_masks, maps))
    unordered_pair_orbits = pair_orbits(
        surface_masks,
        maps,
        distinct_only=False,
    )

    records: list[PairOrbitRecord] = []
    pair_values: dict[tuple[int, int], Fraction] = {}
    for orbit in unordered_pair_orbits:
        representative = orbit[0]
        kind, value = binary_surface_pair_value(
            complex_,
            faces,
            meta,
            *representative,
        )
        records.append(
            PairOrbitRecord(
                representative=representative,
                size=len(orbit),
                kind=kind,
                value=value,
            )
        )
        for pair in orbit:
            pair_values[pair] = value

    matrix = tuple(
        tuple(
            pair_values[cast(tuple[int, int], tuple(sorted((left, right))))]
            for right in surface_masks
        )
        for left in surface_masks
    )
    return SurfaceGramSurvey(
        surface_masks=surface_masks,
        surface_orbits=surface_orbit_rows,
        pair_orbits=tuple(records),
        matrix=matrix,
    )


def surface_orbit_block_counts(survey: SurfaceGramSurvey) -> tuple[tuple[int, ...], ...]:
    """Count pair orbitals in each of the 45 surface-orbit blocks."""

    orbit_index = {
        mask: index for index, orbit in enumerate(survey.surface_orbits) for mask in orbit
    }
    size = len(survey.surface_orbits)
    counts = [[0] * size for _ in range(size)]
    for record in survey.pair_orbits:
        left, right = record.representative
        row, column = sorted((orbit_index[left], orbit_index[right]))
        counts[row][column] += 1
        if row != column:
            counts[column][row] += 1
    return tuple(tuple(row) for row in counts)


def surface_orbit_quotient(survey: SurfaceGramSurvey) -> RationalMatrix:
    """Return the exact nine-orbit equitable quotient of the Gram matrix.

    Entry ``(i,j)`` is the sum of ``G[S,T]`` over all ``T`` in orbit ``j``
    for any fixed ``S`` in orbit ``i``.
    """

    mask_index = {mask: index for index, mask in enumerate(survey.surface_masks)}
    return tuple(
        tuple(
            sum(
                (
                    survey.matrix[mask_index[left_orbit[0]]][mask_index[right]]
                    for right in right_orbit
                ),
                start=Fraction(0),
            )
            for right_orbit in survey.surface_orbits
        )
        for left_orbit in survey.surface_orbits
    )


def diagonal_dominance_residuals(
    matrix: RationalMatrix,
) -> tuple[Fraction, ...]:
    """Return ``G[i,i] - sum_(j != i) |G[i,j]|`` exactly.

    Positive residuals certify positive definiteness by strict diagonal
    dominance.  When all entries are nonnegative, they also give an explicit
    completely-positive factorization:

    ``G = sum_i r_i e_i e_i^T
           + sum_(i<j) G[i,j] (e_i + e_j) (e_i + e_j)^T``.

    Equivalently, one may put ``sqrt(r_i)`` and ``sqrt(G[i,j])`` in separate
    nonnegative feature coordinates.  The squared coordinates are rational,
    so the certificate itself uses exact arithmetic.
    """

    if any(len(row) != len(matrix) for row in matrix):
        raise ValueError("diagonal dominance requires a square matrix")
    return tuple(
        row[index]
        - sum(
            (abs(value) for column, value in enumerate(row) if column != index),
            start=Fraction(0),
        )
        for index, row in enumerate(matrix)
    )


def centered_covariance_matrix(survey: SurfaceGramSurvey) -> RationalMatrix:
    """Gram matrix of ``O_S - integral O_S`` for all 128 surfaces."""

    means = survey.matrix[0]
    return tuple(
        tuple(
            survey.matrix[row][column] - means[row] * means[column]
            for column in range(len(survey.matrix))
        )
        for row in range(len(survey.matrix))
    )


def modular_rank_and_determinant(
    matrix: RationalMatrix,
    prime: int,
) -> tuple[int, int]:
    """Return rank and determinant after exact reduction modulo ``prime``.

    A nonzero determinant is an exact nonsingularity certificate for the
    rational matrix, provided no input denominator is divisible by ``prime``.
    The caller supplies the prime; the modest primality side condition is not
    re-proved here.
    """

    if prime <= 2:
        raise ValueError("an odd prime modulus is required")
    if any(len(row) != len(matrix) for row in matrix):
        raise ValueError("rank certificate requires a square matrix")

    reduced: list[list[int]] = []
    for matrix_row in matrix:
        reduced_row: list[int] = []
        for value in matrix_row:
            denominator = value.denominator % prime
            if denominator == 0:
                raise ValueError("matrix denominator is not invertible modulo the prime")
            reduced_row.append((value.numerator % prime) * pow(denominator, -1, prime) % prime)
        reduced.append(reduced_row)

    dimension = len(reduced)
    rank = 0
    determinant = 1
    for column in range(dimension):
        pivot = next(
            (row_index for row_index in range(rank, dimension) if reduced[row_index][column]),
            None,
        )
        if pivot is None:
            continue
        if pivot != rank:
            reduced[rank], reduced[pivot] = reduced[pivot], reduced[rank]
            determinant = -determinant
        pivot_value = reduced[rank][column]
        determinant = determinant * pivot_value % prime
        inverse = pow(pivot_value, -1, prime)
        for row_index in range(rank + 1, dimension):
            coefficient = reduced[row_index][column] * inverse % prime
            if coefficient:
                reduced[row_index] = [
                    (entry - coefficient * pivot_entry) % prime
                    for entry, pivot_entry in zip(
                        reduced[row_index],
                        reduced[rank],
                        strict=True,
                    )
                ]
        rank += 1
        if rank == dimension:
            break
    if rank != dimension:
        determinant = 0
    return rank, determinant % prime
