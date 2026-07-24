"""Exact regression gates for the BF2.1 reflection-positive carrier."""

from collections import Counter
from fractions import Fraction

import pytest

from computations.general_reflection_cut_carrier import (
    bf21_certificate,
    binary_cut_vertex_bases,
    binary_reflected_gram_blocks,
    binary_reflection_carrier_census,
    binary_reflection_cut_carrier,
    diagonal_congruence,
    exact_ldlt,
    glue_binary_half_states,
    kraus_pushforward,
    rational_quadratic_form,
)
from computations.hypercube4d_surface_gram import build_surface_gram_survey


def test_complete_binary_half_carrier_and_cut_signatures() -> None:
    carrier = binary_reflection_cut_carrier()

    assert carrier.lower_face_ids == (0, 1, 3, 9, 13, 18)
    assert carrier.temporal_face_ids == (2, 4, 5, 10, 11, 14, 15, 17, 19, 20, 22, 23)
    assert carrier.lower_cube_boundary_mask == 0x4220B
    assert len(carrier.signatures) == 32
    assert len(carrier.states) == 64
    assert Counter(len(states) for states in carrier.states_by_signature) == {2: 32}
    assert Counter(signature.edge_count for signature in carrier.signatures) == {
        0: 1,
        4: 6,
        6: 16,
        8: 9,
    }
    assert Counter(signature.loop_lengths for signature in carrier.signatures) == {
        (): 1,
        (4,): 6,
        (4, 4): 3,
        (6,): 16,
        (8,): 6,
    }
    assert {
        states[0].lower_patch_mask ^ states[1].lower_patch_mask
        for states in carrier.states_by_signature
    } == {carrier.lower_cube_boundary_mask}

    square = next(signature for signature in carrier.signatures if signature.loop_lengths == (4,))
    bases = binary_cut_vertex_bases((square.face_mask, square.face_mask))
    assert len(bases) == 4
    assert all(len(basis.legs) == 4 for basis in bases)
    assert all(basis.dimension == 2 for basis in bases)
    assert all(len(basis.fusion_paths) == 2 for basis in bases)


def test_half_gluing_is_a_bijection_onto_all_closed_binary_surfaces() -> None:
    carrier = binary_reflection_cut_carrier()
    survey = build_surface_gram_survey()
    glued = tuple(
        glue_binary_half_states(lower, reflected)
        for states in carrier.states_by_signature
        for lower in states
        for reflected in states
    )

    assert len(glued) == len(set(glued)) == 128
    assert set(glued) == set(survey.surface_masks)

    with pytest.raises(ValueError, match="one boundary block"):
        glue_binary_half_states(
            carrier.states_by_signature[0][0],
            carrier.states_by_signature[1][0],
        )


def test_every_one_strand_reflection_block_has_an_exact_sos() -> None:
    single_blocks, _double_blocks = binary_reflected_gram_blocks()

    assert len(single_blocks) == 32
    assert all(block.validates() for block in single_blocks)
    assert Counter(block.ldlt.rank for block in single_blocks) == {1: 32}
    assert all(
        block.matrix[0][0] * block.matrix[1][1] == block.matrix[0][1] ** 2
        for block in single_blocks
    )
    assert len({block.matrix for block in single_blocks}) == 9


def test_every_two_strand_coherent_boundary_block_is_psd() -> None:
    _single_blocks, double_blocks = binary_reflected_gram_blocks()

    assert len(double_blocks) == 528
    assert all(block.validates() for block in double_blocks)
    assert all(
        all(path.output == 0 for basis in block.cut_vertex_bases for path in basis.fusion_paths)
        for block in double_blocks
    )
    assert Counter(block.ldlt.rank for block in double_blocks) == {
        1: 35,
        2: 271,
        3: 165,
        4: 57,
    }
    assert len({block.matrix for block in double_blocks}) == 124
    assert min(
        pivot
        for block in double_blocks
        for pivot in block.ldlt.diagonal
        if pivot > 0
    ) == Fraction(25, 726073632)


def test_positive_half_weights_preserve_the_exact_gram_cone() -> None:
    _single_blocks, double_blocks = binary_reflected_gram_blocks()
    block = next(candidate for candidate in double_blocks if candidate.ldlt.rank == 4)
    weights = (Fraction(1), Fraction(2), Fraction(3), Fraction(5))
    weighted = diagonal_congruence(block.matrix, weights)
    factor = exact_ldlt(weighted)

    assert factor.reconstructs(weighted)
    assert factor.is_psd
    assert factor.rank == 4
    with pytest.raises(ValueError, match="nonnegative"):
        diagonal_congruence(block.matrix, (Fraction(1), Fraction(2), Fraction(3), Fraction(-1)))


def test_exact_kraus_pushforward_preserves_the_gram_cone() -> None:
    _single_blocks, double_blocks = binary_reflected_gram_blocks()
    block = next(candidate for candidate in double_blocks if candidate.ldlt.rank == 4)
    kraus = (
        (
            (Fraction(1), Fraction(0), Fraction(1, 2), Fraction(0)),
            (Fraction(0), Fraction(1), Fraction(0), Fraction(1, 3)),
        ),
        (
            (Fraction(0), Fraction(1, 5), Fraction(0), Fraction(1)),
            (Fraction(1, 7), Fraction(0), Fraction(1), Fraction(0)),
        ),
    )
    coarse = kraus_pushforward(block.matrix, kraus)
    factor = exact_ldlt(coarse)
    vector = (Fraction(2), Fraction(-3))
    pulled_values = tuple(
        tuple(
            sum(
                (operator[row][column] * vector[row] for row in range(2)),
                start=Fraction(0),
            )
            for column in range(4)
        )
        for operator in kraus
    )

    assert factor.reconstructs(coarse)
    assert factor.is_psd
    assert rational_quadratic_form(coarse, vector) == sum(
        (rational_quadratic_form(block.matrix, pulled) for pulled in pulled_values),
        start=Fraction(0),
    )


def test_bf21_closes_by_the_enlarged_reflected_gram_route() -> None:
    census = binary_reflection_carrier_census()
    certificate = bf21_certificate()

    assert census.validates()
    assert census.gluing_is_bijective
    assert census.two_strand_invariant_dimension_census == (
        (1, 35),
        (4, 36),
        (8, 48),
        (16, 156),
        (32, 48),
        (64, 160),
        (256, 45),
    )
    assert census.negative_block_count == 0
    assert certificate.validates()
    assert certificate.exit_kind == "general-reflected-gram-psd-cone"
    assert certificate.entrywise_dp_status == "open"
    assert certificate.next_gate == "BF3.1-whole-corrected-slab-kraus-kernel"
