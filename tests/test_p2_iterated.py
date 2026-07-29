"""Pins for the P2 iterated-map windows (work_plan §17d)."""

from fractions import Fraction as F

from computations.p2_iterated import (
    gate_hk_semigroup,
    gate_qmin,
    qmin2_continuum,
    su2_t2_windows,
    u1_x1_ratio_window,
    u1_x2_ratio_window,
)


def test_structural_gates():
    assert gate_qmin()
    assert gate_hk_semigroup()


def test_continuum_two_step_form():
    """Qmin_2 = 3(n^2+m^2) - (n+m)^2/6; cross coefficient -1/3."""
    assert qmin2_continuum(1, 1) == F(16, 3)
    assert qmin2_continuum(0, 1) == F(17, 6)
    assert qmin2_continuum(0, 0) == 0
    cross = qmin2_continuum(1, 1) - 2 * qmin2_continuum(0, 1)
    assert cross == F(-1, 3)


def test_u1_sign_flip_certified():
    """At s = 1/2: one-step abelian cross certified NEGATIVE, the
    two-step certified POSITIVE (the Cauchy-Schwarz vacuity theorem,
    machine-checked on the exact theta kernel) — the mirror fence
    fires on the raw two-step sign."""
    s = F(1, 2)
    x1 = u1_x1_ratio_window(s)
    x2 = u1_x2_ratio_window(s)
    assert x1[1] < 1 < x2[0]


def test_su2_depth2_certified_at_half():
    """The first certified trajectory-level SU(2) statement: at
    s = 1/2 the two-step cross is positive and 6-7 orders below the
    one-step value 0.2584 (rank-one collapse), and its whole window
    sits below the abelian mirror's two-step value."""
    s = F(1, 2)
    t2w, ktail = su2_t2_windows(s)
    r_lo = t2w[(1, 1)][0] * t2w[(0, 0)][0] / (t2w[(0, 1)][1] ** 2)
    r_hi = t2w[(1, 1)][1] * t2w[(0, 0)][1] / (t2w[(0, 1)][0] ** 2)
    assert 1 < r_lo < r_hi
    # collapse scale: log-window inside (1e-9, 1e-5)
    assert 1 + F(1, 10 ** 9) < r_lo and r_hi < 1 + F(1, 10 ** 5)
    # magnitude separation vs the abelian mirror at the same s
    u1_2 = u1_x2_ratio_window(s)
    assert r_hi < u1_2[0]
    # truncation tail honest and small
    assert ktail < F(1, 10 ** 12)
