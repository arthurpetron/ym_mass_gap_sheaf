"""Regression gates for the first relative spin-structure gluing."""

from collections import Counter
from fractions import Fraction

from computations.dual_spin_gluing import (
    BRANCHED_INTERFACE_EDGE,
    BRANCHED_OVERLAP,
    BRANCHED_PAIR_LEFT,
    BRANCHED_PAIR_RIGHT,
    BRANCHED_SELECTION,
    BRANCHED_TORUS,
    GLUED_OVERLAP,
    GLUED_PAIR_LEFT,
    GLUED_PAIR_RIGHT,
    GLUED_TORUS,
    admissible_raw_channel_masks,
    build_two_cell_spin_gluing,
    cap_selection_face_mask,
    cap_selection_raw_mask,
    channel_edge_invariant_multiplicities,
    glued_channel_homology_parities,
    glued_channel_weight,
    glued_partition,
    permute_face_mask,
    raw_channel_face_mask,
    raw_channel_interface_defect,
    raw_channel_is_admissible,
    relative_boundary_defect,
    spanning_two_cell_tori,
    transverse_axis_maps,
    two_cell_brick,
)
from computations.hypercube4d_survey import (
    edge_cycles_homologous_mod2,
    face_chain_boundary_mask,
    surface_betti_numbers_mod2,
)
from computations.interior_link4d_probe import evaluate_active_assignment


def test_spanning_tori_split_into_two_cylinders() -> None:
    complex_, faces, meta = two_cell_brick()
    certificate = build_two_cell_spin_gluing()
    assert (len(complex_.edges), len(faces)) == (52, 42)
    assert spanning_two_cell_tori() == certificate.spanning_tori
    assert len(certificate.spanning_tori) == 3
    assert GLUED_TORUS == GLUED_PAIR_LEFT ^ GLUED_PAIR_RIGHT
    assert GLUED_OVERLAP == GLUED_PAIR_LEFT & GLUED_PAIR_RIGHT
    assert GLUED_TORUS in certificate.spanning_tori
    assert GLUED_TORUS & certificate.interface_face_mask == 0
    assert surface_betti_numbers_mod2(complex_, faces, GLUED_TORUS) == (1, 2, 1)
    assert tuple(patch.bit_count() for patch in certificate.patch_masks) == (12, 12)
    assert all(
        surface_betti_numbers_mod2(complex_, faces, patch) == (1, 1, 0)
        for patch in certificate.patch_masks
    )
    maps = transverse_axis_maps(meta)
    assert {permute_face_mask(GLUED_TORUS, permutation) for permutation in maps} == set(
        certificate.spanning_tori
    )
    assert all(
        permute_face_mask(certificate.interface_face_mask, permutation)
        == certificate.interface_face_mask
        for permutation in maps
    )


def test_relative_cap_boundaries_glue_and_form_k22() -> None:
    _complex, faces, _meta = two_cell_brick()
    certificate = build_two_cell_spin_gluing()
    assert tuple(cap.bit_count() for cap in certificate.cap_masks) == (2, 2, 1, 1)
    assert certificate.homology_families == ((0, 1), (2, 3))
    assert certificate.crossing_edges == ((0, 2), (0, 3), (1, 2), (1, 3))

    surface_edges = 0
    for face_index, face in enumerate(faces):
        if (certificate.surface >> face_index) & 1:
            for edge, _orientation in face:
                surface_edges |= 1 << edge

    for strip in certificate.cap_masks[:2]:
        halves = (
            strip & certificate.cell_face_masks[0],
            strip & certificate.cell_face_masks[1],
        )
        assert tuple(half.bit_count() for half in halves) == (1, 1)
        defects = tuple(face_chain_boundary_mask(faces, half) & ~surface_edges for half in halves)
        assert defects[0] == defects[1] != 0
        assert defects[0] & ~certificate.interface_edge_mask == 0
        assert face_chain_boundary_mask(faces, strip) & ~surface_edges == 0

    for cap in certificate.cap_masks[2:]:
        assert cap.bit_count() == 1
        assert face_chain_boundary_mask(faces, cap) & ~surface_edges == 0


def test_edge_admissibility_is_exactly_relative_defect_cancellation() -> None:
    admissible = admissible_raw_channel_masks()
    zero_defect = tuple(mask for mask in range(64) if raw_channel_interface_defect(mask) == 0)
    cap_unions = tuple(sorted(cap_selection_raw_mask(selection) for selection in range(16)))
    assert len(admissible) == 16
    assert admissible == zero_defect
    assert admissible == cap_unions
    assert all(raw_channel_is_admissible(mask) for mask in admissible)
    assert all(not raw_channel_is_admissible(mask) for mask in set(range(64)) - set(admissible))


def test_glued_sign_factors_through_global_boundary_homology() -> None:
    _complex, faces, _meta = two_cell_brick()
    certificate = build_two_cell_spin_gluing()
    basis_cycles = tuple(
        face_chain_boundary_mask(faces, certificate.cap_masks[family[0]])
        for family in certificate.homology_families
    )
    for selection in range(16):
        selected_boundary = face_chain_boundary_mask(
            faces,
            cap_selection_face_mask(selection),
        )
        parities = glued_channel_homology_parities(selection)
        reference = (basis_cycles[0] if parities[0] else 0) ^ (
            basis_cycles[1] if parities[1] else 0
        )
        assert edge_cycles_homologous_mod2(
            faces,
            certificate.surface,
            selected_boundary,
            reference,
        )
        value = glued_channel_weight(selection)
        assert (value < 0) == (parities == (1, 1))


def test_subdivision_weight_and_complete_partition_are_exact() -> None:
    expected_census = Counter(
        {
            Fraction(1, 16777216): 4,
            Fraction(-1, 150994944): 4,
            Fraction(1, 50331648): 2,
            Fraction(1, 1358954496): 2,
            Fraction(1, 452984832): 2,
            Fraction(1, 150994944): 1,
            Fraction(1, 12230590464): 1,
        }
    )
    assert Counter(glued_channel_weight(selection) for selection in range(16)) == expected_census
    assert glued_partition() == Fraction(101, 382205952)
    assert glued_partition() / Fraction(1, 2**24) == Fraction(3232, 729)
    assert glued_partition() > 0


def test_direct_haar_pins_for_one_relative_cap_and_both_crossings() -> None:
    complex_, faces, _meta = two_cell_brick()
    # The deterministic cap order puts a two-face spanning strip first and
    # the two one-face caps last.  These seven cases test its subdivision
    # factor and zero, one, or two crossings by the generic exact integrator.
    for cap_selection in (0, 4, 8, 12, 1, 5, 9, 13):
        selected_faces = cap_selection_face_mask(cap_selection)
        spins = [
            1 if (GLUED_TORUS >> face_index) & 1 else 2 if (selected_faces >> face_index) & 1 else 0
            for face_index in range(len(faces))
        ]
        assert evaluate_active_assignment(complex_, faces, spins) == glued_channel_weight(
            cap_selection
        )

    # Every admissible raw selection is literally one of the cap unions.
    assert {raw_channel_face_mask(mask) for mask in admissible_raw_channel_masks()} == {
        cap_selection_face_mask(selection) for selection in range(16)
    }


def test_interface_branch_is_the_first_obstruction_to_plain_mod2_gluing() -> None:
    complex_, faces, _meta = two_cell_brick()
    certificate = build_two_cell_spin_gluing()
    assert BRANCHED_TORUS == BRANCHED_PAIR_LEFT ^ BRANCHED_PAIR_RIGHT
    assert BRANCHED_OVERLAP == BRANCHED_PAIR_LEFT & BRANCHED_PAIR_RIGHT
    assert BRANCHED_SELECTION & ~BRANCHED_OVERLAP == 0
    assert surface_betti_numbers_mod2(complex_, faces, BRANCHED_TORUS) == (1, 2, 1)
    assert (BRANCHED_TORUS & certificate.interface_face_mask).bit_count() == 2

    defect = relative_boundary_defect(BRANCHED_TORUS, BRANCHED_SELECTION)
    assert defect == 1 << BRANCHED_INTERFACE_EDGE
    assert defect & ~certificate.interface_edge_mask == 0

    multiplicities = channel_edge_invariant_multiplicities(
        BRANCHED_TORUS,
        BRANCHED_SELECTION,
    )
    assert all(multiplicity > 0 for multiplicity in multiplicities)
    assert multiplicities[BRANCHED_INTERFACE_EDGE] == 1

    incident_selected = [
        face_index
        for face_index, face in enumerate(faces)
        if (BRANCHED_SELECTION >> face_index) & 1
        and any(edge == BRANCHED_INTERFACE_EDGE for edge, _orientation in face)
    ]
    assert len(incident_selected) == 3

    spins = [
        1
        if (BRANCHED_TORUS >> face_index) & 1
        else 2
        if (BRANCHED_SELECTION >> face_index) & 1
        else 0
        for face_index in range(len(faces))
    ]
    assert evaluate_active_assignment(complex_, faces, spins) == Fraction(1, 18874368)
