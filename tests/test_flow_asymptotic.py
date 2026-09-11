"""Pins for the exact asymptotic flow curve (work_plan §16c).

E*_{ab}(s) = 3 + [log P_a - log P_b]/(tau (C(b)-C(a))) with
P_n(s) = sum_{|m|<=N} s^{2nm+4m^2}; expansion
E*(tau) = 3 - 4 tau + (112/5) tau^2 + O(tau^3), both coefficients
pair-independent.  Agreement with the certified theta windows is
pinned at s = 9/10 (curve within 2e-6 of the window)."""

from fractions import Fraction

from computations.flow_asymptotic import (
    basis_exponents,
    pair_coeffs,
    pair_curve,
    slack_bound,
    slope_closed_form,
    verify,
)

Fr = Fraction


def test_basis_polynomials():
    assert sorted(basis_exponents(0)) == [0, 4, 4, 16, 16]
    assert sorted(basis_exponents(1)) == [0, 2, 6, 12, 20]
    assert sorted(basis_exponents(2)) == [0, 0, 8, 8, 24]


def test_mean_law_gives_e_star():
    # equal means across n is exactly the E* = 3 law
    for n in (0, 1, 2):
        vals = basis_exponents(n)
        assert Fr(sum(vals), len(vals)) == 8


def test_slope_closed_form_and_pair_independence():
    assert slope_closed_form(1) == Fr(-4, 3)
    assert slope_closed_form(2) == Fr(-4)
    assert slope_closed_form(3) == Fr(-8)
    for (a, b) in ((0, 1), (0, 2), (1, 2)):
        c1, c2 = pair_coeffs(a, b)
        assert c1 == Fr(-4)
        assert c2 == Fr(112, 5)          # pair-independent through tau^2


def test_curve_matches_certified_windows_at_9_10():
    r = verify(Fr(9, 10))
    for key, e in r["pairs"].items():
        assert e["agree"], f"pair {key} disagrees"
        assert abs(e["diff"]) < 2e-6, f"pair {key}: {e['diff']}"


def test_slack_bound_positive_and_shrinking():
    s1 = slack_bound(Fr(9, 10))
    s2 = slack_bound(Fr(99, 100))
    assert 0 < s2 < s1


def test_expansion_predicts_99_100_row():
    # 3 - 4 tau + 112/5 tau^2 at tau = -log(99/100) lands within 3e-5
    # of the certified value 2.962042 (the tau^3 remainder)
    import math
    tau = -math.log(0.99)
    pred = 3 - 4 * tau + 22.4 * tau * tau
    assert abs(pred - pair_curve(0, 1, Fr(99, 100))) < 3e-5
