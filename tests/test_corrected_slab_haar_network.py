"""Regression pins for the exact corrected-slab Haar network."""

from fractions import Fraction

from computations.corrected_slab_haar_network import (
    corrected_slab_edge_multiplicities,
    corrected_slab_fixed_face_dual_term,
    corrected_slab_haar_complex,
    embedded_negative_hypercube_assignment,
    evaluate_corrected_slab_assignment,
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
