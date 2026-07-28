"""Pins for the Gaussian network dictionary and fusion structure
(work_plan §16e) — the first stage of the c_SU2 moment computation."""

from fractions import Fraction

from computations.gaussian_network_moments import (
    SIGMA_L,
    face_variance_classes,
    fusion_channels,
    fusion_mean_identity,
    fusion_variance,
    gate_duality,
    gate_loops_are_single_links,
    single_face_gate,
    u1_cross_ratio,
)

Fr = Fraction


def test_adapted_gauge_loops():
    assert gate_loops_are_single_links()


def test_legendre_duality_with_qmin():
    # the angle-picture loop covariance reproduces the flux-picture
    # quadratic form Qmin(n,m) = 3n^2 + 3m^2 + 2nm exactly
    assert gate_duality()
    assert SIGMA_L == [[Fr(3), Fr(1)], [Fr(1), Fr(3)]]


def test_face_variance_classes_exact():
    fv = face_variance_classes()
    assert set(fv["top"]) == {Fr(79, 96)}
    assert set(fv["bottom"]) == {Fr(79, 96)}
    assert set(fv["pwall"]) == {Fr(79, 96)}
    assert set(fv["iwall"]) == {Fr(17, 24)}


def test_fusion_mean_identity():
    # sum_J d_J (C(2J) - C(n) - C(m)) == 0: the trace-free identity
    # tr(J1.J2) = 0 — no linear cross slope for SU(2)
    assert fusion_mean_identity(6)


def test_fusion_channels_11():
    # n = m = 1: channels J = 0, 1 with delta in {-6, +2}
    assert fusion_channels(1, 1) == [(0, 1, -6), (2, 3, 2)]
    assert fusion_variance(1, 1) == Fr(12)
    assert fusion_variance(1, 2) == Fr(32)
    assert fusion_variance(2, 2) == Fr(256, 3)


def test_single_face_insertion_calculus():
    # e^tau E_flat[(sin phi/phi) chi_n] == d_n e^{-tau C(n)}: the gate
    # that pins every constant of the insertion calculus
    ok, worst = single_face_gate(25)
    assert ok, f"worst rel {worst}"


def test_u1_cross_ratio_matches_asymptote():
    # the abelian lane of the discriminating observable: X_11 -> -2tau
    import math
    for s, digits in ((Fr(9, 10), 4), (Fr(99, 100), 6)):
        tau = -math.log(float(s))
        _lo, _hi, x = u1_cross_ratio(s)
        assert abs(x - (-2 * tau)) < 10 ** (-digits)
        assert x < 0                     # abelian: negative, O(tau)
