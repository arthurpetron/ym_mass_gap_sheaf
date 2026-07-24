"""Regression pins for the exact corrected-slab Haar network."""

from fractions import Fraction

from computations.corrected_slab_haar_network import (
    corrected_slab_edge_multiplicities,
    corrected_slab_fixed_face_dual_term,
    corrected_slab_haar_complex,
    embedded_negative_channel_surface_pair,
    embedded_negative_hypercube_assignment,
    evaluate_corrected_slab_assignment,
    evaluate_corrected_slab_surface_pair,
)
from computations.hypercube4d_survey import exact_constant


def test_extent_one_corrected_slab_geometry() -> None:
    complex_, faces, plaquettes = corrected_slab_haar_complex(1)
    assert len(faces) == len(plaquettes) == 72
    assert len(complex_.edges) == 116
    assert len(complex_.tree) + len(complex_.free) == len(complex_.edges)


def test_negative_hypercube_channel_embeds_in_corrected_slab() -> None:
    spins = embedded_negative_hypercube_assignment()
    assert len(spins) == 72
    assert (sum(spins), sum(spin > 0 for spin in spins)) == (20, 18)
    assert exact_constant(
        evaluate_corrected_slab_assignment(1, spins)
    ) == Fraction(-1, 196608)
    multiplicities = corrected_slab_edge_multiplicities(1, spins)
    assert set(multiplicities) == {1}


def test_heat_weight_preserves_the_exact_negative_sign() -> None:
    spins = embedded_negative_hypercube_assignment()
    value = corrected_slab_fixed_face_dual_term(
        1, 2, Fraction(1, 2), spins
    )
    assert value < 0
    assert value == -Fraction(1, 196608) * (
        Fraction(2) * Fraction(1, 2) ** 3
    ) ** 16 * (
        Fraction(3) * Fraction(1, 2) ** 8
    ) ** 2


def test_complete_surface_pair_resums_negative_channels_positively() -> None:
    left, right = embedded_negative_channel_surface_pair()
    assert exact_constant(
        evaluate_corrected_slab_surface_pair(1, left, right)
    ) == Fraction(31, 331776)
    negative_spins = embedded_negative_hypercube_assignment()
    overlap = left & right
    odd = left ^ right
    selected_twos = sum(
        1 << face_index
        for face_index, spin in enumerate(negative_spins)
        if spin == 2
    )
    assert all(
        spin == (
            2 if (selected_twos >> face_index) & 1
            else 1 if (odd >> face_index) & 1
            else 0
        )
        for face_index, spin in enumerate(negative_spins)
    )
    assert selected_twos & ~overlap == 0
