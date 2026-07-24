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
    branched_admissible_raw_channel_masks,
    branched_channel_census,
    branched_partition,
    branched_raw_channel_face_mask,
    build_two_cell_spin_gluing,
    cap_selection_face_mask,
    cap_selection_raw_mask,
    channel_edge_invariant_multiplicities,
    decorated_interface_carrier,
    glued_channel_homology_parities,
    glued_channel_weight,
    glued_partition,
    invariant_fusion_paths,
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
    evaluate_surface_pair,
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


def test_decorated_carrier_retains_branch_and_intertwiner_basis() -> None:
    carrier = decorated_interface_carrier(BRANCHED_TORUS, BRANCHED_SELECTION)
    branch = next(packet for packet in carrier if packet.edge == BRANCHED_INTERFACE_EDGE)
    assert branch.relative_defect
    assert tuple(strand.label for strand in branch.strands) == (2, 2, 2)
    assert branch.fusion_paths == ((2, 2, 0),)
    assert branch.invariant_dimension == 1

    four_valent_selection = branched_raw_channel_face_mask(0x1D)
    four_valent = next(
        packet
        for packet in decorated_interface_carrier(BRANCHED_TORUS, four_valent_selection)
        if packet.edge == BRANCHED_INTERFACE_EDGE
    )
    assert not four_valent.relative_defect
    assert tuple(strand.label for strand in four_valent.strands) == (2, 2, 2, 2)
    assert four_valent.fusion_paths == (
        (2, 0, 2, 0),
        (2, 2, 2, 0),
        (2, 4, 2, 0),
    )
    assert four_valent.invariant_dimension == 3

    assert len(invariant_fusion_paths((1, 1, 2, 2))) == 2


def test_decorated_carrier_matches_every_local_edge_invariant() -> None:
    for channel_mask in branched_admissible_raw_channel_masks():
        selected = branched_raw_channel_face_mask(channel_mask)
        multiplicities = channel_edge_invariant_multiplicities(BRANCHED_TORUS, selected)
        carrier = decorated_interface_carrier(BRANCHED_TORUS, selected)
        assert all(packet.invariant_dimension == multiplicities[packet.edge] for packet in carrier)
        assert all(packet.invariant_dimension > 0 for packet in carrier)


def test_branched_overlap_ledger_is_complete_exact_and_positive() -> None:
    admissible = branched_admissible_raw_channel_masks()
    assert admissible == (
        0x00,
        0x02,
        0x05,
        0x07,
        0x09,
        0x0B,
        0x0C,
        0x0D,
        0x0E,
        0x0F,
        0x11,
        0x13,
        0x14,
        0x15,
        0x16,
        0x17,
        0x18,
        0x19,
        0x1A,
        0x1B,
        0x1C,
        0x1D,
        0x1E,
        0x1F,
    )
    census = branched_channel_census()
    assert tuple(channel for channel, _value in census) == admissible
    assert all(value > 0 for _channel, value in census)
    assert Counter(value for _channel, value in census) == Counter(
        {
            Fraction(1, 18874368): 8,
            Fraction(7, 113246208): 2,
            Fraction(1, 12582912): 12,
            Fraction(1, 4194304): 2,
        }
    )
    assert branched_partition() == Fraction(7, 3538944)

    complex_, faces, _meta = two_cell_brick()
    assert evaluate_surface_pair(
        complex_,
        faces,
        BRANCHED_PAIR_LEFT,
        BRANCHED_PAIR_RIGHT,
    ) == {0: branched_partition()}


def test_branched_obstruction_fills_one_transverse_symmetry_orbit() -> None:
    _complex, _faces, meta = two_cell_brick()
    triples = {
        (
            permute_face_mask(BRANCHED_TORUS, permutation),
            permute_face_mask(BRANCHED_OVERLAP, permutation),
            permute_face_mask(BRANCHED_SELECTION, permutation),
        )
        for permutation in transverse_axis_maps(meta)
    }
    assert len(triples) == 6
    for surface, overlap, selected in triples:
        assert selected & ~overlap == 0
        carrier = decorated_interface_carrier(surface, selected)
        branches = [
            packet
            for packet in carrier
            if packet.relative_defect
            and tuple(strand.label for strand in packet.strands) == (2, 2, 2)
        ]
        assert len(branches) == 1
        assert branches[0].invariant_dimension == 1
