"""Pins for the P2 iterated-map windows (work_plan §17d + §17e:
the SOS/Lagrange layer, the entry-level OS Gram, and the certified
depth-2 sign on the CERT grid)."""

from fractions import Fraction as F

from computations.p2_iterated import (
    gate_hk_semigroup,
    gate_lagrange,
    gate_oscs_u1,
    gate_qmin,
    qmin2_continuum,
    su2_depth2_assembly,
    su2_t2_windows,
    u1_x1_ratio_window,
    u1_x2_ratio_window,
)


def test_structural_gates():
    assert gate_qmin()
    assert gate_hk_semigroup()


def test_lagrange_identity_exact():
    """det(Gram rows of T^2) = sum of squared one-step minors,
    replayed exactly on rationals through the minor code path."""
    assert gate_lagrange()


def test_oscs_entry_gram_conjugated_with_teeth():
    """The entry-level OS Gram holds in CONJUGATED form on the exact
    abelian lane, and the gate has teeth: the unconjugated form is
    refuted there (aligned charges cost more on the slab — B^T u =
    -B^T w).  On SU(2), self-conjugacy closes the gap."""
    assert gate_oscs_u1()


def test_depth2_sign_certified_at_11_20():
    """The §17d open residual, closed: the depth-2 sign at s = 11/20
    certified via the Lagrange SOS lower bound (leading minor = the
    certified one-step X11 object), with the OS-Gram-sharpened upper
    bound giving a two-sided magnitude window."""
    s = F(11, 20)
    asm = su2_depth2_assembly(s)
    assert asm["certified"] and asm["consistent"] and asm["oscs_ok"]
    r_lo, r_hi = asm["ratio"]
    assert 1 + F(2, 10 ** 7) < r_lo          # X2_lo > 2e-7
    assert r_hi < 1 + F(2, 10 ** 5)          # X2_hi < 2e-5
    # the SOS route alone certifies the sign (no diagonal landing
    # was needed):
    assert asm["sos"][0] > 1


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
