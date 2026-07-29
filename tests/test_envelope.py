"""Pins for the stage-one envelope lemma (work_plan §17-P1 / §16m)."""

from fractions import Fraction as F

from computations.su2_envelope import (
    X2, X3, envelope_theorem, exp_le_power, small_field_K, star_gate,
    x11_window,
)


def test_banked_series_provenance():
    """The eta^4/eta^6 coefficients are the banked §16f-16g rationals."""
    assert X2 == F(6) and X3 == F(115, 6)


def test_envelope_theorem_inhabited():
    tau, s_up, k_x = envelope_theorem()
    assert tau > 0 and k_x > 0
    # the monotone positivity margin: K_X tau*^2 strictly under 6
    assert k_x * tau * tau <= 3 < 6
    # the certified window is positive at tau* and at tau*/2, tau*/4
    for t in (tau, tau / 2, tau / 4):
        lo, hi, _ = x11_window(t)
        assert 0 < lo < hi
    # s* upper bound is a rational strictly below 1
    assert 0 < s_up < 1


def test_exp_le_power_soundness():
    """The domination lemma must accept a true instance and reject a
    false one."""
    # true and accepted: e^{-1/tau} <= tau^4/2 for tau <= 10^-6
    # (the check is a SUFFICIENT certificate — conservative by design,
    # so the accepted instance sits safely inside the true region)
    assert exp_le_power(F(1), F(1, 10 ** 6), 4, F(2))
    # false-shaped (fails the certified check): huge P at moderate tau
    assert not exp_le_power(F(1, 1000), F(1, 2), 4, F(10) ** 100)


def test_star_gate():
    """The remainder-scaling gate on the exactly-known fusion star."""
    assert star_gate(verbose=False)
