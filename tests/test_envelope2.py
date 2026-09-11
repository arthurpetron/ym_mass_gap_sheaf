"""Pins for the stage-two envelope lemma (work_plan §17b)."""

from fractions import Fraction as F

from computations.su2_envelope import envelope_theorem as thm1
from computations.su2_envelope2 import (
    SlabData,
    envelope_theorem2,
    g3_up,
    gate_cubic,
    gate_dynkin,
    gate_mirror,
    gate_repair,
    mirror_theorem,
    q_hat,
    sqrt_up,
)


def test_slab_data_exact():
    """The exact complex constants the sharpened budget consumes."""
    data = SlabData()
    # only the four >= 3-distinct-link faces carry any cubic
    carriers = [t for t in data.t3_f if t != 0]
    assert len(carriers) == 4
    # T3 certified window (rational upper bounds; pin the value range)
    assert F(50) < data.T3 < F(51)
    assert data.k4 == 1060
    for e in range(data.net.nl):
        assert data.c[e] ** 2 >= data.net.Ginv[e][e]


def test_stage_two_theorem():
    tau2, s_up2, k2, consts = envelope_theorem2()
    tau1, _s1, k1 = thm1()
    # the banked stage-two constants (regenerate ledger if these
    # move); the §17c ETA8 repair moved 2^-55 -> 2^-61, 2^-76 -> 2^-82
    assert tau2 == F(1, 2 ** 61)
    assert tau1 == F(1, 2 ** 82)
    assert k2 < k1                        # dominates repaired stage one
    assert k2 * tau2 * tau2 <= 3 < 6      # positivity margin
    assert consts["kappa"] == F(1, 9)
    assert 0 < s_up2 < 1


def test_mirror_separation():
    """|X_U1 + 8 tau| <= K_U1 tau^4 and the certified sign
    separation X_SU2 > 0 > X_U1 on the common interval."""
    k_u1, margin = mirror_theorem()
    tau2, _, k2, _ = envelope_theorem2()
    assert margin > 0
    assert k_u1 < F(10 ** 11)             # abelian lane is TINY
    assert k_u1 * tau2 ** 3 < 8           # X_U1 < 0 on all of (0, tau*]
    # SU(2) lower end positive at tau* (redundant with theorem margin)
    assert 6 * tau2 ** 2 + F(115, 6) * tau2 ** 3 - k2 * tau2 ** 4 > 0


def test_gates():
    data = SlabData()
    assert gate_cubic(data)
    assert gate_dynkin()
    assert gate_repair(data)
    assert gate_mirror(data)


def test_certified_bounds_shape():
    """Structural sanity of the certified elementary bounds."""
    assert sqrt_up(F(2)) ** 2 >= 2
    # g3_up is O(s0^3): at s0 = 1/100 it must be below 2e-6
    assert g3_up(F(1, 100)) < F(2, 10 ** 6)
    # q_hat tends to 9/4 from above as s0 -> 0 (2 s g3 ~ 2 s^4,
    # (s^2/2)^2 = s^4/4); the repair's cover 5/2 holds on its
    # asserted domain sigma <= 1/50 (NOT at 1/8, where q_hat ~ 2.74
    # — the domain assert in r0_choice is load-bearing)
    assert F(9, 4) < q_hat(F(1, 50)) < F(5, 2)
    assert q_hat(F(1, 8)) > F(5, 2)
