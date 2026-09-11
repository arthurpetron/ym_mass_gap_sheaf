"""Pins for the certified middle-regime X_11 floor (work_plan §17h)."""
from fractions import Fraction as Frac

import pytest

from computations.sector_floor import (
    MIDDLE_GRID,
    certified_floor,
    diagonal_upper,
    lam_min,
)
from computations.sector_sos import assemble, det_poly, pev, sector_kernels


@pytest.fixture(scope="module")
def det():
    return det_poly(assemble(sector_kernels(1, 2)))


def test_grid_is_at_or_above_the_anchor_edge():
    """Every grid point must lie at or above 2^(-1/3), i.e. strictly
    outside the unconditional strong-coupling anchor window: this is the
    whole point of the statement."""
    for s in MIDDLE_GRID:
        assert 2 * s ** 3 >= 1, f"{s} is inside the anchor window"


def test_cutoff_condition_is_the_documented_one():
    for s in MIDDLE_GRID:
        lam = lam_min(s)
        assert 4 * s ** (2 * lam + 3) < 1
        assert 16 * s ** (4 * lam + 6) < 1
        if lam > 1:
            assert (4 * s ** (2 * (lam - 1) + 3) >= 1
                    or 16 * s ** (4 * (lam - 1) + 6) >= 1)


def test_floor_is_positive_on_the_whole_middle_grid(det):
    for s in MIDDLE_GRID:
        floor, dS, t00, t11, lam = certified_floor(s, det)
        assert dS > 0
        assert t00 > 0 and t11 > 0
        assert floor > 0
        # the inequality X_11 >= D/(T00 T11) needs sin^2 theta < 1
        assert floor < 1


def test_diagonal_bound_dominates_the_exact_sector_subsum(det):
    """The crude diagonal bound must exceed the exact cap<=1 sub-sum —
    a necessary (and non-trivial) consistency condition."""
    T = assemble(sector_kernels(1, 2))
    for s in (Frac(4, 5), Frac(9, 10)):
        lam = lam_min(s) + 2
        assert diagonal_upper(0, s, lam) > pev(T[(0, 0)], s)
        assert diagonal_upper(1, s, lam) > pev(T[(1, 1)], s)


def test_pinned_floor_at_the_anchor_edge(det):
    floor, dS, _t00, _t11, lam = certified_floor(Frac(4, 5), det)
    assert lam == 4
    assert dS == pev(det, Frac(4, 5))
    assert 5.9e-25 < float(floor) < 6.0e-25


def test_crude_cost_is_the_diagnosed_loss(det):
    """The honesty pin: the certified floor is 20+ orders below the
    reference ratio, and the gap is the crude diagonal domination."""
    T = assemble(sector_kernels(1, 2))
    s = Frac(4, 5)
    floor, dS, _a, _b, _l = certified_floor(s, det)
    ref = dS / (pev(T[(0, 0)], s) * pev(T[(1, 1)], s))
    assert ref / floor > Frac(10) ** 20
