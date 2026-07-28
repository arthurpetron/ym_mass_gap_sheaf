"""Pins for MD.2 — the exact U(1) theta-resummation (work_plan §16b).

The abelian owned-boundary slab kernel at M = infinity is the
quadratic-form theta series over the rank-4 cube-flip lattice; the
asymptotic one-step flow exponent is exact:

    E* = |u|^2 - (B^T u)^T A^{-1} (B^T u) = 4 - 1 = 3.

These pins freeze the lattice data, the quadratic form, the spectrum
of A, the tail-bound soundness (sandwich against truncated kernels),
and the ladder trend of the tau'/tau brackets toward E*.
"""

from fractions import Fraction

import pytest

from computations.u1_theta_kernel import (
    ALPHA,
    A_MAT,
    BETA,
    E_STAR,
    GAMMA,
    _check_spectrum,
    flow_windows,
    qform_data,
    qmin,
    tail_bound,
    theta_window,
)
from computations.dp6_u1_slab_blocking import kernel_entry_u1

Fr = Fraction


def test_lattice_gram_and_spectrum():
    # A = 6I - Adj(C4): each cube shares exactly one wall with each
    # cyclic neighbour; spectrum {4, 6, 6, 8} via exact charpoly
    assert A_MAT == [[6, -1, -1, 0], [-1, 6, 0, -1],
                     [-1, 0, 6, -1], [0, -1, -1, 6]]
    assert _check_spectrum()


def test_qmin_quadratic_form():
    # Qmin(n,m) = 3n^2 + 3m^2 + 2nm exactly, on a grid
    assert (ALPHA, BETA, GAMMA) == (Fr(3), Fr(3), Fr(2))
    for n in range(-3, 4):
        for m in range(-3, 4):
            assert qmin(n, m) == 3 * n * n + 3 * m * m + 2 * n * m


def test_e_star_closed_form():
    # E* = |u|^2 - (B^T u)^T A^{-1} (B^T u) = 4 - 1 = 3; the 2D disk
    # value 4 screened by exactly one unit through the flip lattice
    assert E_STAR == Fr(3)
    c0, b = qform_data(1, 0)
    assert c0 == 4 and b == [2, 2, 2, 2]


def test_linear_term_form():
    # b(n,m) = 2 (n - m) (1,1,1,1): B^T u = (1,1,1,1) = -B^T w
    for n in range(-2, 3):
        for m in range(-2, 3):
            _c0, b = qform_data(n, m)
            assert b == [2 * (n - m)] * 4


def test_theta_window_sandwiches_truncated_kernels():
    # T_M(s) increases monotonically to the theta value; the window
    # certifiably contains every truncation from above
    s = Fr(1, 2)
    for (n, m) in [(0, 0), (1, 0), (1, -1), (2, 2)]:
        lo, hi, _R = theta_window(n, m, s, Fr(1, 10 ** 30))
        prev = None
        for M in (3, 4, 5, 6):
            tm = sum(c * s ** p
                     for p, c in kernel_entry_u1(n, m, M).items())
            if prev is not None:
                assert tm >= prev
            prev = tm
            assert tm <= hi
        assert Fr(0) <= hi - prev <= Fr(1, 10 ** 6)


def test_tail_bound_is_sound_under_refinement():
    # enlarging R strictly tightens the certified window and windows
    # remain nested (soundness of the shell/geometric tail bound)
    s = Fr(3, 4)
    lo1, hi1, R1 = theta_window(1, 0, s, Fr(1, 10 ** 8))
    lo2, hi2, R2 = theta_window(1, 0, s, Fr(1, 10 ** 16))
    assert R2 >= R1
    assert lo1 <= lo2 <= hi2 <= hi1


def test_tau_ratio_trend_toward_e_star():
    # the pairwise tau'/tau brackets tighten onto each other and move
    # toward E* = 3 along the ladder (values pinned loosely; exact
    # windows live in the ledger)
    _v, r12 = flow_windows(2, Fr(1, 2))
    _v, r34 = flow_windows(2, Fr(3, 4))
    _v, r910 = flow_windows(2, Fr(9, 10))
    # s = 1/2: spread wide, pair01 = 3.652 (matches the converged
    # fixed-M measurement — cross-instrument agreement)
    assert 3.65 < r12["0,1"][0] <= r12["0,1"][1] < 3.66
    # s = 9/10: the three pairs collapse onto each other (limit
    # scheme covariance emerging) near 2.78
    vals = [r910[k][0] for k in ("0,1", "0,2", "1,2")]
    assert max(vals) - min(vals) < 0.01
    assert 2.7 < min(vals) <= max(vals) < 2.9
    # the approach to E* is NOT monotone: the ladder dips below 2.8
    # around s ~ 0.75-0.9 before rising toward 3 (the 99/100 rise is
    # pinned from the banked ledger in the test below)
    assert r34["0,1"][1] < r12["0,1"][0]


def test_banked_ladder_rises_to_e_star():
    # the banked run's s = 99/100 row: all three pairs coincide to
    # ~4 digits near 2.962, approaching E* = 3 as E* + O(tau)
    import json
    import os

    from computations.u1_theta_kernel import OUT_JSON

    if not os.path.exists(OUT_JSON):
        pytest.skip("ledger not generated in this checkout")
    D = json.load(open(OUT_JSON))
    rows = {r["s"]: r for r in D["rows"]}
    r99 = rows["99/100"]["tau_ratio_brackets"]
    vals = [r99[k][0] for k in ("0,1", "0,2", "1,2")]
    assert max(vals) - min(vals) < 0.001
    assert 2.95 < min(vals) <= max(vals) < 3.0
    r910 = rows["9/10"]["tau_ratio_brackets"]
    assert r910["0,1"][1] < r99["0,1"][0] < 3.0
