"""Regression pins for the dual positivity survival probes.

Every value below was computed by the exact integrator and is pinned as
an exact rational (or exact s-polynomial).  These are the headline
witnesses of notes/dual-positivity-survival.md; if any of them drifts,
the finding itself has drifted and the note must be re-derived.
"""

from fractions import Fraction

from computations.dual_positivity_survival import (
    double_cube_structured_table,
    rim_channel_activity,
    rim_channel_decomposition,
    single_cube_table,
    slab_value,
    wheel_sweep,
    wheel_value,
)
from computations.exact_haar_network import sign_on_unit_interval


# -- P0: single cube control ------------------------------------------------


def test_single_cube_control():
    tab = single_cube_table(2)
    assert tab == {
        (0, 0, 0, 0, 0, 0): Fraction(1),
        (1, 1, 1, 1, 1, 1): Fraction(1, 16),
        (2, 2, 2, 2, 2, 2): Fraction(1, 81),
    }
    # closed surface (sphere): bivalent edges force all-equal spins,
    # values are 1/d^{chi-driven power}; all positive.


# -- P1: double cube, small structured table --------------------------------


def test_double_cube_small_table():
    tab = double_cube_structured_table(1, 2)
    assert tab == {
        (0, 0, 0): Fraction(1),
        (0, 1, 1): Fraction(1, 16),
        (1, 0, 1): Fraction(1, 16),
        (1, 1, 0): Fraction(1, 256),
        (1, 1, 2): Fraction(1, 256),
    }
    # trivalent interior edges: (1,1,1) violates parity and vanishes;
    # every surviving amplitude is positive.


# -- P1b: slab spot values (unanchored circuit; not SOS-protected) ----------


def test_slab_spot_values():
    assert slab_value(1, (0, 0, 0, 0)) == {0: Fraction(1, 16384)}
    assert slab_value(1, (2, 2, 2, 2)) == {0: Fraction(7, 442368)}
    assert slab_value(2, (2, 2, 2, 2)) == {0: Fraction(1, 28697814)}
    # parity kills odd wall patterns against an outer shell of 1:
    assert slab_value(1, (1, 1, 1, 1)) == {}


# -- P2: wheel values --------------------------------------------------------


def test_wheel_hand_verified_values():
    # chain-reducible case, verified by hand via convolution + orthogonality
    assert wheel_value((0, 0, 1, 1), (0, 0, 1, 0)) == {0: Fraction(1, 2)}
    # symmetric spin-2 wheel
    assert wheel_value((2, 2, 2, 2), (2, 2, 2, 2)) == {0: Fraction(1, 54)}
    # all-ones wheel vanishes (odd parity at each X_i is fine — this zero
    # is a genuine selection, not a parity screen)
    assert wheel_value((1, 1, 1, 1), (1, 1, 1, 1)) == {}


def test_wheel_sweep_nonnegative_small():
    w = wheel_sweep(1)
    assert w, "sweep should be nonempty"
    assert all(v >= 0 for v in w.values()), {k: v for k, v in w.items() if v < 0}


# -- P3: positive-channel door test ------------------------------------------


def test_rim_channel_exact_polynomial():
    act = rim_channel_activity((1, 1, 1, 1))
    assert act == {
        0: Fraction(1, 4),
        16: Fraction(9, 2),
        24: Fraction(6),
        32: Fraction(21, 4),
    }
    assert sign_on_unit_interval(act) == "positive"


def test_rim_channel_ledger_is_termwise_positive():
    dec = rim_channel_decomposition((1, 1, 1, 1))
    flat = {j: list(sp.values())[0] for j, sp in dec.items()}
    assert all(v > 0 for v in flat.values()), flat
    # and the ledger resums exactly to the channel activity
    total = {}
    for sp in dec.values():
        for k, v in sp.items():
            total[k] = total.get(k, Fraction(0)) + v
    assert total == rim_channel_activity((1, 1, 1, 1))
