"""Regression gates for the symmetry-reduced four-cube survey."""

from collections import Counter
from fractions import Fraction

from computations.hypercube4d_survey import (
    admissible_assignment_orbits,
    admissible_orbit_vertex_sign_census,
    binary_surface_pair_fusion_witness,
    decode_assignment,
    evaluate_assignment,
    evaluate_surface_pair,
    hypercube,
    intersecting_pair_vertex_sign_census,
    kernel_basis,
    locally_admissible_assignments,
    mask_orbits,
    pair_orbits,
    superposed_surface_assignment,
    surface_assignment,
    surface_betti_numbers_mod2,
    surface_cell_counts,
    surface_pair_fusion_expansion,
    surface_pair_fusion_value,
    surfaces,
    symmetry_maps,
    vertex_sixj_product,
    vertex_sixj_signs,
)


def test_hypercube_combinatorics_and_binary_kernel() -> None:
    complex_, faces, _meta = hypercube()
    assert (len(complex_.edges), len(faces), len(complex_.free)) == (32, 24, 17)
    valences = Counter(
        sum(edge == edge_index for face in faces for edge, _orientation in face)
        for edge_index in range(len(complex_.edges))
    )
    assert valences == {3: 32}

    basis = kernel_basis(complex_, faces)
    binary_surfaces = surfaces(basis)
    assert len(basis) == 7
    assert len(binary_surfaces) == 128
    assert Counter(mask.bit_count() for mask in binary_surfaces) == {
        0: 1,
        6: 8,
        10: 24,
        12: 44,
        14: 48,
        16: 3,
    }


def test_surface_symmetry_orbits_retain_euler_distinction() -> None:
    complex_, faces, meta = hypercube()
    binary_surfaces = surfaces(kernel_basis(complex_, faces))
    maps = symmetry_maps(meta)
    assert len(maps) == 384
    assert maps[0] == list(range(24))
    assert all(sorted(permutation) == list(range(24)) for permutation in maps)

    orbits = mask_orbits(binary_surfaces, maps)
    assert [(len(orbit), surface_cell_counts(complex_, faces, orbit[0])) for orbit in orbits] == [
        (1, (0, 0, 0, 0)),
        (8, (8, 12, 6, 2)),
        (24, (12, 20, 10, 2)),
        (32, (14, 24, 12, 2)),
        (8, (14, 24, 12, 2)),
        (4, (16, 24, 12, 4)),
        (24, (16, 28, 14, 2)),
        (24, (16, 28, 14, 2)),
        (3, (16, 32, 16, 0)),
    ]


def test_every_binary_surface_is_two_dimensional_yang_mills() -> None:
    complex_, faces, meta = hypercube()
    binary_surfaces = surfaces(kernel_basis(complex_, faces))
    torus_count = 0
    for mask in binary_surfaces:
        _vertices, _edges, face_count, euler = surface_cell_counts(
            complex_,
            faces,
            mask,
        )
        value = vertex_sixj_product(meta, surface_assignment(mask))
        assert value == Fraction(2) ** (euler - face_count)
        if face_count == 16:
            assert euler == 0
            assert value == Fraction(1, 65536)
            torus_count += 1
    assert torus_count == 3


def test_exact_embedded_cube_and_minimal_intersecting_pair() -> None:
    complex_, faces, meta = hypercube()
    binary_surfaces = surfaces(kernel_basis(complex_, faces))
    maps = symmetry_maps(meta)

    sphere = next(mask for mask in binary_surfaces if mask.bit_count() == 6)
    assert evaluate_assignment(
        complex_,
        faces,
        surface_assignment(sphere),
    ) == {0: Fraction(1, 16)}

    pair_representatives = sorted(
        (
            orbit[0]
            for orbit in pair_orbits(
                binary_surfaces[1:],
                maps,
                intersecting_only=True,
            )
        ),
        key=lambda pair: (
            pair[0].bit_count() + pair[1].bit_count(),
            (pair[0] & pair[1]).bit_count(),
            pair,
        ),
    )
    assert len(pair_representatives) == 100
    left, right = pair_representatives[0]
    assert (left.bit_count(), right.bit_count(), (left & right).bit_count()) == (
        6,
        6,
        1,
    )
    spins = superposed_surface_assignment(left, right)
    assert evaluate_assignment(complex_, faces, spins) == {0: Fraction(1, 256)}
    signs = vertex_sixj_signs(meta, spins)
    assert signs.count(-1) == 8
    assert signs.count(0) == 0


def test_complete_four_strand_pair_sum_is_positive_on_all_orbits() -> None:
    complex_, faces, meta = hypercube()
    binary_surfaces = surfaces(kernel_basis(complex_, faces))
    pair_representatives = [
        orbit[0]
        for orbit in pair_orbits(
            binary_surfaces[1:],
            symmetry_maps(meta),
            intersecting_only=True,
        )
    ]
    records: list[tuple[Fraction, int, int]] = []
    term_signs: Counter[int] = Counter()
    for left, right in pair_representatives:
        terms = [
            vertex_sixj_product(meta, spins) for spins in surface_pair_fusion_expansion(left, right)
        ]
        term_signs.update(0 if value == 0 else 1 if value > 0 else -1 for value in terms)
        records.append(
            (
                sum(terms, start=Fraction(0)),
                sum(value < 0 for value in terms),
                sum(value > 0 for value in terms),
            )
        )

    assert len(records) == 100
    assert all(total > 0 for total, _negative, _positive in records)
    assert min(total for total, _negative, _positive in records) == Fraction(
        1,
        16384,
    )
    assert term_signs == {0: 19548, 1: 696, -1: 108}
    assert Counter((negative, positive) for _total, negative, positive in records if negative) == {
        (4, 12): 3,
        (16, 48): 2,
        (64, 192): 1,
    }

    # Four negative fixed-face channels occur in this representative, but the
    # complete four-strand intertwiner sum is positive.
    left, right = 0x4AB33, 0x6BC6AD
    assert surface_pair_fusion_value(meta, left, right) == Fraction(31, 331776)
    assert evaluate_surface_pair(complex_, faces, left, right) == {0: Fraction(31, 331776)}


def test_physical_vertex_sixj_pair_census_has_even_negative_parity() -> None:
    complex_, faces, meta = hypercube()
    binary_surfaces = surfaces(kernel_basis(complex_, faces))
    census = intersecting_pair_vertex_sign_census(binary_surfaces[1:], meta)
    assert sum(census.values()) == 7997
    assert census == {
        (0, 0): 1485,
        (2, 0): 2456,
        (4, 0): 2372,
        (6, 0): 720,
        (8, 0): 820,
        (10, 0): 96,
        (12, 0): 48,
    }
    assert all(negative_count % 2 == 0 for negative_count, _zeros in census)


def test_full_cutoff_two_local_admissibility_frontier() -> None:
    complex_, faces, meta = hypercube()
    encodings = locally_admissible_assignments(complex_, faces)
    assert len(encodings) == 38151
    orbits = admissible_assignment_orbits(encodings, symmetry_maps(meta))
    assert len(orbits) == 369
    assert Counter(len(orbit) for orbit in orbits) == {
        1: 2,
        3: 3,
        4: 3,
        6: 2,
        8: 7,
        12: 7,
        16: 4,
        24: 45,
        32: 14,
        48: 58,
        64: 9,
        96: 114,
        192: 87,
        384: 14,
    }

    sign_census = admissible_orbit_vertex_sign_census(orbits, meta)
    assert sign_census == {
        (0, 0): 39,
        (1, 0): 1,
        (2, 0): 28,
        (3, 0): 8,
        (4, 0): 60,
        (5, 0): 15,
        (6, 0): 55,
        (7, 0): 7,
        (8, 0): 110,
        (9, 0): 2,
        (10, 0): 15,
        (12, 0): 19,
        (14, 0): 2,
        (16, 0): 8,
    }
    assert (
        sum(count for (negative_count, _zeros), count in sign_census.items() if negative_count % 2)
        == 33
    )

    classified = [
        (
            vertex_sixj_product(meta, decode_assignment(orbit[0])),
            len(orbit),
            orbit[0],
        )
        for orbit in orbits
    ]
    assert sum(size for value, size, _encoding in classified if value < 0) == 6704
    assert sum(size for value, size, _encoding in classified if value > 0) == 31447
    assert all(value != 0 for value, _size, _encoding in classified)
    negative_orbits = [(size, encoding) for value, size, encoding in classified if value < 0]
    assert len(negative_orbits) == 33
    assert min(sum(decode_assignment(encoding)) for _size, encoding in negative_orbits) == 20
    assert (48, (0x6F6D9E, 0x21)) in negative_orbits

    binary_surfaces = surfaces(kernel_basis(complex_, faces))
    reachable_negative_orbits = [
        (size, encoding)
        for size, encoding in negative_orbits
        if binary_surface_pair_fusion_witness(encoding, binary_surfaces) is not None
    ]
    assert reachable_negative_orbits == [
        (48, (0x6F6D9E, 0x21)),
        (96, (0x6F6D9E, 0x261)),
        (48, (0x6F6D9E, 0x108261)),
    ]
    assert sum(size for size, _encoding in reachable_negative_orbits) == 192

    for _size, (odd, twos) in reachable_negative_orbits:
        assert surface_betti_numbers_mod2(complex_, faces, odd) == (1, 2, 1)
        selected_planes = [
            (first, second)
            for face_index, (_point, first, second) in enumerate(meta)
            if (twos >> face_index) & 1
        ]
        plane_counts = {plane: selected_planes.count(plane) for plane in set(selected_planes)}
        assert len(plane_counts) == 2
        first_plane, second_plane = plane_counts
        assert set(first_plane).isdisjoint(second_plane)
        assert set(first_plane) | set(second_plane) == {0, 1, 2, 3}
        assert all(count % 2 == 1 for count in plane_counts.values())

    unreachable_negative_orbits = [
        (size, encoding)
        for size, encoding in negative_orbits
        if binary_surface_pair_fusion_witness(encoding, binary_surfaces) is None
    ]
    assert len(unreachable_negative_orbits) == 30
    assert {
        surface_cell_counts(complex_, faces, encoding[0])[3]
        for _size, encoding in unreachable_negative_orbits
    } == {2}


def test_smallest_cutoff_two_negative_amplitude_is_exact() -> None:
    """The universal nonnegativity conjecture fails on the unit four-cube."""

    complex_, faces, meta = hypercube()
    encoding = (0x6F6D9E, 0x21)
    spins = decode_assignment(encoding)
    assert (sum(spins), sum(spin > 0 for spin in spins)) == (20, 18)
    signs = vertex_sixj_signs(meta, spins)
    assert signs.count(-1) == 9
    assert signs.count(0) == 0
    expected = Fraction(-1, 196608)
    assert vertex_sixj_product(meta, spins) == expected
    assert evaluate_assignment(complex_, faces, spins) == {0: expected}
