"""Regression pins for the BF1.6 spacing-changing Haar block."""

from fractions import Fraction

from computations.reflection_cut_haar_block import (
    bf16_certificate,
    half_surface_block_pushforward,
)


def test_two_by_two_half_surface_block_has_exact_coarse_modes() -> None:
    pushforward = half_surface_block_pushforward()
    assert pushforward.validates()
    assert pushforward.corrected_slab_extent == 3
    assert pushforward.corrected_slab_half == 1
    assert pushforward.fine_face_ids == (0, 84, 336, 420)
    assert pushforward.reflected_fine_face_ids == (18, 102, 354, 438)
    assert pushforward.spacing_factor == 2
    assert pushforward.coarse_modes == (
        (0, {0: Fraction(1)}),
        (1, {12: Fraction(2)}),
        (2, {32: Fraction(3)}),
    )
    assert pushforward.coarse_intertwiner_transport == ((0, 0), (1, 1), (2, 2))


def test_block_mass_and_outside_carrier_remainder_are_literal() -> None:
    pushforward = half_surface_block_pushforward()
    assert pushforward.haar_total_mass == {0: Fraction(1)}
    assert pushforward.identity_mass == {
        0: Fraction(1),
        12: Fraction(4),
        32: Fraction(9),
    }
    assert pushforward.remainder_outside_carrier == ()


def test_bf16_closes_on_the_selected_finite_sector() -> None:
    certificate = bf16_certificate()
    assert certificate.validates()
    assert certificate.exit_kind == "positive-finite-selected-sector"
