"""Regression pins for exact 4D hypercube dual-amplitude probes.

The 4-cube boundary has 16 vertices, 32 edges, and 24 plaquettes, with every
edge trivalent.  Its parity-admissible binary spin assignments are precisely
the closed surfaces modulo two.  The kernel has dimension seven: the eight
3-cell boundaries obey one relation.

Every binary surface amplitude factors through two-dimensional Yang--Mills
on the surface,

``Z(surface, uniform spin n) = d_n ** (chi(surface) - face_count)``.

In particular, spheres give ``d ** (2 - face_count)`` and the three
coordinate Clifford tori give ``d ** -16``.  The exhaustive all-surface
version is pinned in ``test_hypercube4d_survey.py``; the complete
intersecting-pair interference and Gram pins live in the companion survey,
crossing-kernel, and surface-Gram tests.
"""

from collections import Counter
from collections.abc import Sequence
from fractions import Fraction
from typing import TypeAlias

from computations.exact_haar_network import (
    P_ONE,
    FaceMetadata,
    GaugeFixedComplex,
    OrientedPath,
    brick_complex,
    brick_complex_nd,
    chi,
)

Face: TypeAlias = list[tuple[int, int]]
Hypercube: TypeAlias = tuple[
    GaugeFixedComplex,
    list[Face],
    list[FaceMetadata],
]


def _hypercube() -> Hypercube:
    return brick_complex_nd((1, 1, 1, 1))


def _evaluate(
    complex_: GaugeFixedComplex,
    faces: list[Face],
    spins: list[int],
) -> dict[int, Fraction]:
    factors = [
        chi(spin, complex_.holonomy_of(face))
        for spin, face in zip(spins, faces, strict=True)
        if spin > 0
    ]
    if not factors:
        factors = [dict(P_ONE)]
    return complex_.contract_invariant(factors)


def _kernel_basis(
    complex_: GaugeFixedComplex,
    faces: Sequence[OrientedPath],
) -> list[int]:
    rows: list[int] = []
    for edge_index in range(len(complex_.edges)):
        row = 0
        for face_index, face in enumerate(faces):
            if any(edge == edge_index for edge, _orientation in face):
                row |= 1 << face_index
        rows.append(row)

    pivots: dict[int, int] = {}
    for row in rows:
        for pivot_column, pivot_row in pivots.items():
            if (row >> pivot_column) & 1:
                row ^= pivot_row
        if row:
            pivots[row.bit_length() - 1] = row

    free_columns = [column for column in range(len(faces)) if column not in pivots]
    basis: list[int] = []
    for free_column in free_columns:
        vector = 1 << free_column
        for pivot_column in sorted(pivots, reverse=True):
            if (pivots[pivot_column] & vector).bit_count() % 2:
                vector ^= 1 << pivot_column
        basis.append(vector)
    return basis


def test_hypercube_combinatorics() -> None:
    complex_, faces, _metadata = _hypercube()
    assert len(complex_.edges) == 32
    assert len(faces) == 24
    assert len(complex_.free) == 17

    valence: Counter[int] = Counter()
    for face in faces:
        for edge_index, _orientation in face:
            valence[edge_index] += 1
    assert Counter(valence.values()) == {3: 32}


def test_nd_builder_preserves_the_3d_brick_convention() -> None:
    old_complex, old_faces = brick_complex(1, 2, 1)
    nd_complex, nd_faces, metadata = brick_complex_nd((1, 2, 1))
    assert nd_complex.edges == old_complex.edges
    assert nd_complex.tree == old_complex.tree
    assert nd_complex.free == old_complex.free
    assert nd_faces == old_faces
    assert len(metadata) == len(nd_faces)


def test_kernel_is_seven_dimensional() -> None:
    complex_, faces, _metadata = _hypercube()
    assert len(_kernel_basis(complex_, faces)) == 7


def test_embedded_3cell_reproduces_3d_cube() -> None:
    complex_, faces, metadata = _hypercube()
    cell = [
        index
        for index, (point, first_direction, second_direction) in enumerate(metadata)
        if first_direction != 3 and second_direction != 3 and point[3] == 0
    ]
    assert len(cell) == 6
    for label, expected in (
        (1, Fraction(1, 16)),
        (2, Fraction(1, 81)),
    ):
        spins = [0] * len(faces)
        for index in cell:
            spins[index] = label
        assert _evaluate(complex_, faces, spins) == {0: expected}


def test_binary_surfaces_evaluate_by_2d_yang_mills() -> None:
    """Pin one representative at each binary-surface support size."""
    complex_, faces, _metadata = _hypercube()
    basis = _kernel_basis(complex_, faces)

    sizes: Counter[int] = Counter()
    vectors: list[int] = []
    for bits in range(2 ** len(basis)):
        vector = 0
        for index, basis_vector in enumerate(basis):
            if (bits >> index) & 1:
                vector ^= basis_vector
        vectors.append(vector)
        sizes[vector.bit_count()] += 1

    # Z = d^(chi-F): the support-16 representative is a Clifford torus.
    expected = {
        0: Fraction(1),
        6: Fraction(1, 16),
        10: Fraction(1, 256),
        12: Fraction(1, 1024),
        14: Fraction(1, 4096),
        16: Fraction(1, 65536),
    }
    assert set(sizes) == set(expected)
    assert sizes[16] >= 3

    checked_sizes: set[int] = set()
    for vector in vectors:
        support_size = vector.bit_count()
        if support_size in checked_sizes:
            continue
        spins = [(vector >> face_index) & 1 for face_index in range(len(faces))]
        assert _evaluate(complex_, faces, spins) == {0: expected[support_size]}
        checked_sizes.add(support_size)
        if checked_sizes == set(expected):
            break


def test_symmetry_maps_are_permutations() -> None:
    from computations.hypercube4d_survey import hypercube, symmetry_maps

    _complex, _faces, metadata = hypercube()
    maps = symmetry_maps(metadata)
    assert len(maps) == 384
    for symmetry in maps[:20] + maps[-20:]:
        assert sorted(symmetry) == list(range(24))
    assert maps[0] == list(range(24))


def test_survey_module_agrees_with_direct_evaluation() -> None:
    from computations.hypercube4d_survey import (
        evaluate_assignment,
        hypercube,
        kernel_basis,
        surfaces,
    )

    complex_, faces, _metadata = hypercube()
    basis = kernel_basis(complex_, faces)
    assert len(basis) == 7
    binary_surfaces = surfaces(basis)
    assert len(binary_surfaces) == 128
    sphere = next(vector for vector in binary_surfaces if vector.bit_count() == 6)
    spins = [(sphere >> index) & 1 for index in range(24)]
    assert evaluate_assignment(complex_, faces, spins) == {0: Fraction(1, 16)}
