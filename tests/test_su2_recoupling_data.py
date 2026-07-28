"""Pins for the DP.1 recoupling data layer (moments -> squared 6j)."""

import itertools
from fractions import Fraction

from computations.su2_recoupling_data import (
    k4_value,
    sixj_squared_table,
    triads_ok,
    wigner_6j_squared,
)


def test_k4_literal_pins():
    # {1 1 1; 1 1 1} = 1/6  ->  K4(all 2) = 1/36
    assert k4_value((2, 2, 2, 2, 2, 2)) == Fraction(1, 36)
    # {1/2 1/2 0; 1/2 1/2 0} = -1/2  ->  square 1/4
    # slot map: (A,B,C,D,E,F) with Wigner {A/2 B/2 C/2; F/2 E/2 D/2}
    assert k4_value((1, 1, 0, 0, 1, 1)) == Fraction(1, 4)
    # triad-violating assignment is exactly zero
    assert k4_value((1, 0, 0, 0, 0, 0)) == Fraction(0)


def test_k4_matches_wigner_6j_squared_small():
    import sympy

    for spins in itertools.product(range(3), repeat=6):
        if not triads_ok(spins):
            continue
        k4 = k4_value(spins)
        lhs = sympy.Rational(k4.numerator, k4.denominator)
        assert sympy.simplify(lhs - wigner_6j_squared(spins)) == 0, spins


def test_table_is_positive_and_symmetric():
    tab = sixj_squared_table(2)
    assert all(v > 0 for v in tab.values())
    # tetrahedral symmetry spot-check: swapping the roles of two
    # vertices permutes edge labels; K4 must be invariant.  Vertices
    # 1<->2 swaps (B<->D, C<->E), fixes A, F.
    for (A, B, C, D, E, F), v in tab.items():
        assert tab.get((A, D, E, B, C, F)) == v, (A, B, C, D, E, F)
