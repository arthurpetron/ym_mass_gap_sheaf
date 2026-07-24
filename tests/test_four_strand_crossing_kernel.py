"""Regression gates for the local four-fundamental crossing kernel."""

from fractions import Fraction

from computations.four_strand_crossing_kernel import (
    CROSSING_WEIGHT,
    DIAGRAM_GRAM,
    DIAGRAM_GRAM_INVERSE,
    arf_unsigned_reconstruction,
    complete_bipartite_channel_parities,
    complete_bipartite_edges,
    complete_bipartite_partition,
    crossing_graph_weight,
    crossing_polarization,
    crossing_quadratic_refinement,
    explicit_complete_bipartite_partition,
    matrix_product,
    signed_spin_parity_partition,
    spin_parity_sector_partition,
    spin_structure_twisted_partition,
    trace_power,
)
from computations.hypercube4d_survey import (
    coordinate_clifford_torus_mask,
    edge_cycles_homologous_mod2,
    face_chain_boundary_mask,
    hypercube,
    overlap_boundary_homology_class,
    surface_betti_numbers_mod2,
    surface_cell_counts,
    surface_pair_fusion_expansion,
    torus_mod2_intersection,
    vertex_sixj_product,
)


def test_diagram_kernel_is_the_inverse_gram_projector_coefficient() -> None:
    assert matrix_product(DIAGRAM_GRAM, DIAGRAM_GRAM_INVERSE) == (
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(1)),
    )


def test_complete_bipartite_resummation_is_exact_and_positive() -> None:
    expected = {
        (2, 2): Fraction(496, 81),
        (2, 4): Fraction(117568, 6561),
        (4, 4): Fraction(1309692160, 43046721),
    }
    for sizes, value in expected.items():
        assert complete_bipartite_partition(*sizes) == value
        assert explicit_complete_bipartite_partition(*sizes) == value
        assert value > 0

    # K_2,2 is a four-cycle.  Its sum is a positive even transfer trace.
    assert complete_bipartite_partition(2, 2) == trace_power(CROSSING_WEIGHT, 4)


def test_signed_ledgers_are_an_exact_quadratic_refinement() -> None:
    for left_size, right_size in ((2, 2), (2, 4), (4, 4)):
        vertex_count = left_size + right_size
        edges = complete_bipartite_edges(left_size, right_size)
        for channel_mask in range(1 << vertex_count):
            value = crossing_graph_weight(channel_mask, vertex_count, edges)
            sign = -1 if value < 0 else 1
            assert sign == (
                -1
                if crossing_quadratic_refinement(
                    channel_mask,
                    left_size,
                    right_size,
                )
                else 1
            )

        for left_mask in range(1 << vertex_count):
            left_parities = complete_bipartite_channel_parities(
                left_mask,
                left_size,
                right_size,
            )
            for right_mask in range(1 << vertex_count):
                right_parities = complete_bipartite_channel_parities(
                    right_mask,
                    left_size,
                    right_size,
                )
                assert crossing_polarization(
                    left_mask,
                    right_mask,
                    left_size,
                    right_size,
                ) == torus_mod2_intersection(left_parities, right_parities)

    # The nonzero polarization cannot be removed by a linear channel
    # rephasing: q(e_L)=q(e_R)=0 but q(e_L+e_R)=1.
    assert crossing_quadratic_refinement(1, 2, 2) == 0
    assert crossing_quadratic_refinement(1 << 2, 2, 2) == 0
    assert crossing_quadratic_refinement((1 << 2) | 1, 2, 2) == 1


def test_spin_parity_sector_ledgers_resume_exactly() -> None:
    expected = {
        (2, 2): (
            Fraction(244, 81),
            Fraction(20, 9),
            Fraction(20, 9),
            Fraction(4, 3),
        ),
        (2, 4): (
            Fraction(59536, 6561),
            Fraction(6160, 729),
            Fraction(272, 81),
            Fraction(80, 27),
        ),
        (4, 4): (
            Fraction(664911424, 43046721),
            Fraction(5712448, 531441),
            Fraction(5712448, 531441),
            Fraction(128320, 19683),
        ),
    }
    for sizes, sectors in expected.items():
        assert spin_parity_sector_partition(*sizes) == sectors
        assert signed_spin_parity_partition(*sizes) == (
            sectors[0] + sectors[1] + sectors[2] - sectors[3]
        )
        assert signed_spin_parity_partition(*sizes) == complete_bipartite_partition(*sizes)


def test_four_spin_structures_give_the_exact_arf_transform() -> None:
    for sizes in ((2, 2), (2, 4), (4, 4)):
        sectors = spin_parity_sector_partition(*sizes)
        assert spin_structure_twisted_partition(*sizes, 0, 0) == (
            signed_spin_parity_partition(*sizes)
        )
        assert arf_unsigned_reconstruction(*sizes) == sum(
            sectors,
            start=Fraction(0),
        )

        for left_twist in (0, 1):
            for right_twist in (0, 1):
                signs = {
                    (-1)
                    ** (
                        left_parity * right_parity
                        + left_twist * left_parity
                        + right_twist * right_parity
                    )
                    for left_parity in (0, 1)
                    for right_parity in (0, 1)
                }
                assert signs == {-1, 1}


def test_six_signed_four_cube_orbits_have_complete_bipartite_ledgers() -> None:
    complex_, faces, meta = hypercube()
    representatives = (
        (0x4AB33, 0x6BC6AD, 2, 2),
        (0xCEB66, 0x6386F8, 2, 2),
        (0x1CEFC0, 0x73825E, 2, 2),
        (0x25BAF3, 0x4AD76D, 2, 4),
        (0x2DFAA6, 0x9B2DCB, 2, 4),
        (0x6F6D9E, 0xB6D76D, 4, 4),
    )
    baseline = Fraction(1, 2**16)

    for left, right, left_size, right_size in representatives:
        _vertices, _edges, face_count, euler = surface_cell_counts(
            complex_,
            faces,
            left ^ right,
        )
        assert (face_count, euler) == (16, 0)

        overlap_planes = [
            (first, second)
            for face, (_point, first, second) in enumerate(meta)
            if ((left & right) >> face) & 1
        ]
        plane_counts = {plane: overlap_planes.count(plane) for plane in set(overlap_planes)}
        assert sorted(plane_counts.values()) == sorted((left_size, right_size))
        assert len(plane_counts) == 2
        first_plane, second_plane = plane_counts
        assert set(first_plane).isdisjoint(second_plane)
        assert set(first_plane) | set(second_plane) == {0, 1, 2, 3}
        assert left ^ right == coordinate_clifford_torus_mask(
            meta,
            first_plane,
            second_plane,
        )
        assert surface_betti_numbers_mod2(
            complex_,
            faces,
            left ^ right,
        ) == (1, 2, 1)

        overlap_indices = [
            face_index for face_index in range(len(meta)) if ((left & right) >> face_index) & 1
        ]
        first_family = [
            face_index
            for face_index in overlap_indices
            if overlap_boundary_homology_class(
                meta[face_index],
                first_plane,
                second_plane,
            )
            == (1, 0)
        ]
        second_family = [
            face_index
            for face_index in overlap_indices
            if overlap_boundary_homology_class(
                meta[face_index],
                first_plane,
                second_plane,
            )
            == (0, 1)
        ]
        assert sorted((len(first_family), len(second_family))) == sorted((left_size, right_size))

        torus_edges = {
            edge
            for face_index, face in enumerate(faces)
            if ((left ^ right) >> face_index) & 1
            for edge, _orientation in face
        }

        def boundary_vertices(face_index: int) -> set[int]:
            return {
                vertex
                for edge, _orientation in faces[face_index]
                for vertex in complex_.edges[edge]
            }

        for face_index in overlap_indices:
            assert {edge for edge, _orientation in faces[face_index]} <= torus_edges
        for first_face in first_family:
            for second_face in second_family:
                assert len(boundary_vertices(first_face) & boundary_vertices(second_face)) == 1

        ordered_overlap = first_family + second_family
        basis_cycles = (
            face_chain_boundary_mask(faces, 1 << first_family[0]),
            face_chain_boundary_mask(faces, 1 << second_family[0]),
        )
        for channel_mask in range(1 << len(ordered_overlap)):
            selected_faces = sum(
                1 << face_index
                for position, face_index in enumerate(ordered_overlap)
                if (channel_mask >> position) & 1
            )
            selected_boundary = face_chain_boundary_mask(faces, selected_faces)
            homology_class = complete_bipartite_channel_parities(
                channel_mask,
                len(first_family),
                len(second_family),
            )
            reference_cycle = (basis_cycles[0] if homology_class[0] else 0) ^ (
                basis_cycles[1] if homology_class[1] else 0
            )
            assert edge_cycles_homologous_mod2(
                faces,
                left ^ right,
                selected_boundary,
                reference_cycle,
            )
            assert (
                crossing_quadratic_refinement(
                    channel_mask,
                    len(first_family),
                    len(second_family),
                )
                == homology_class[0] * homology_class[1]
            )

        resolved = tuple(
            vertex_sixj_product(meta, spins) for spins in surface_pair_fusion_expansion(left, right)
        )
        edges = complete_bipartite_edges(left_size, right_size)
        predicted = tuple(
            baseline * crossing_graph_weight(mask, left_size + right_size, edges)
            for mask in range(1 << (left_size + right_size))
        )

        # The overlap-face enumeration can differ from the canonical
        # bipartition order, but the complete weighted ledgers agree.
        assert sorted(resolved) == sorted(predicted)
        assert sum(resolved, start=Fraction(0)) == (
            baseline * complete_bipartite_partition(left_size, right_size)
        )
