"""Pins for the kappa-system: support law, fermionic realization."""

from fractions import Fraction

from computations.kappa_system import (
    branch_edges,
    decomposable,
    grassmann_sign,
    kappa,
)
from computations.vertex_amplitude import amplitude, combo_spins, surface_masks


MIN_BRANCHED_NEGATIVE = (0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1,
                         2, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 2)


def test_minimal_branched_negative_moment_arbitrated():
    z = amplitude(MIN_BRANCHED_NEGATIVE)
    assert z == Fraction(-1, 196608)  # confirmed by raw moments
    assert kappa(MIN_BRANCHED_NEGATIVE) == 1
    assert not decomposable(MIN_BRANCHED_NEGATIVE)
    assert len(branch_edges(MIN_BRANCHED_NEGATIVE)) > 0


def test_decomposable_examples_positive_and_kappa_zero():
    surf = surface_masks()
    import itertools

    checked = 0
    for a, b in itertools.combinations(surf[:20], 2):
        spins = combo_spins([a, b])
        try:
            k = kappa(spins)
        except ValueError:
            continue
        assert decomposable(spins)
        assert k == 0
        assert amplitude(spins) > 0
        checked += 1
        if checked >= 10:
            break
    assert checked >= 5


def test_grassmann_realization_matches_kappa():
    surf = surface_masks()
    cases = [
        list(MIN_BRANCHED_NEGATIVE),
        combo_spins([surf[59], surf[93]]),
        combo_spins([surf[1], surf[10], surf[12]]),
        combo_spins([2707861, 3216742, 2201848]),
    ]
    for spins in cases:
        try:
            k = kappa(spins)
        except ValueError:
            continue
        assert grassmann_sign(spins) == (-1) ** k
