"""Pins for MD.1 — the observable-matched flow map (work_plan §16).

Everything asserted here is either a banked reproduction gate or an
exact-rational fact computed by computations/flow_matching.py.  The
headline pins encode the MD.1 finding: at s = 1/2 the SIGN of the
one-step coupling defect against the 2D rule is NOT scheme-covariant
across admissible matchings, and the SU(2)-below verdict of the M=1
legacy fit is carried by the truncation-suppressed spin-2 disk channel
(T[0,2] regains its 2D term 3 s^32 at M=2 and every pair moves ABOVE
the rule).  The group separation that survives is by MAGNITUDE, on
both definitions, with the separator (connected/located) observable
M-stable for both groups.
"""

from fractions import Fraction

import pytest

from computations.flow_matching import (
    build_u1,
    cas_su2,
    dim_su2,
    flowed_image,
    gate_g1_su2,
    gate_g1_u1,
    gram_su2,
    gram_u1,
    legacy_fit,
    load_su2_M1,
    load_su2_M2,
    pair_match,
    separator_match,
)

Fr = Fraction
S = Fr(1, 2)
S4 = S ** 4


@pytest.fixture(scope="module")
def su2_M1():
    return load_su2_M1()


@pytest.fixture(scope="module")
def su2_M2():
    T, win = load_su2_M2()
    return T, win


@pytest.fixture(scope="module")
def u1_M2():
    return build_u1(2, 2)


def test_gate_g1_su2_banked_floats(su2_M1):
    # legacy fit reproduces the banked DP.2 numbers to the digit
    gate_g1_su2(su2_M1)


def test_gate_g1_u1_banked_exact(u1_M2):
    # DP.6-U1 exact witnesses at M=2, s=1/2
    gate_g1_u1(u1_M2)


def test_su2_M1_pair01_exactly_above_2d_rule(su2_M1):
    # the (0,1)-pair observable is ABOVE the 2D rule already at M=1:
    # the legacy fit's below-verdict does not come from channel 1
    cand = [n for n in range(4) if su2_M1[(n, n)]]
    _idx, v = flowed_image(su2_M1, cand, S, dim_su2, cas_su2)
    pairs = pair_match(v, dim_su2, cas_su2)
    val = pairs["0,1"]["value_pow"]
    assert val == Fr(1467702248448, 6005899834403585)
    assert val > S4 ** 3          # ABOVE (exact)


def test_su2_M1_higher_pairs_below_by_truncation(su2_M1):
    # at M=1 the spin-2 channel has no 2D-disk term, so pairs into it
    # sit ~100x BELOW the rule — the carrier of the old fit verdict
    cand = [n for n in range(4) if su2_M1[(n, n)]]
    _idx, v = flowed_image(su2_M1, cand, S, dim_su2, cas_su2)
    pairs = pair_match(v, dim_su2, cas_su2)
    assert pairs["0,2"]["value_pow"] < S4 ** 8 / 50
    assert pairs["1,2"]["value_pow"] < S4 ** 5 / 50


def test_su2_M2_disk_term_restored_and_pairs_flip(su2_M2):
    # T[0,2] at M=2 contains the 2D disk term 3 s^32 (absent at M=1),
    # and ALL pairs move ABOVE the 2D rule: the M=1 sign was
    # truncation-borne.  (M=2 tails above the final windows are
    # provisional; exponent 32 is far below every window.)
    T, win = su2_M2
    assert T[(0, 2)][32] == Fr(3)
    assert win[(0, 2)] > 32
    _idx, v = flowed_image(T, [0, 1, 2], S, dim_su2, cas_su2)
    pairs = pair_match(v, dim_su2, cas_su2)
    assert pairs["0,1"]["value_pow"] > S4 ** 3
    assert pairs["0,2"]["value_pow"] > S4 ** 8
    assert pairs["1,2"]["value_pow"] > S4 ** 5


def test_sign_not_scheme_covariant_at_strong_coupling(su2_M1):
    # legacy fit says BELOW (0.034121 < 0.0625) while the exact
    # (0,1)-pair says ABOVE at the same s, same kernel, same M —
    # the strong-coupling sign is definition-dependent
    cand = [n for n in range(4) if su2_M1[(n, n)]]
    _idx, v = flowed_image(su2_M1, cand, S, dim_su2, cas_su2)
    sp, _w = legacy_fit(v, dim_su2, cas_su2)
    assert f"{sp:.6f}" == "0.034121" and sp < float(S4)
    pairs = pair_match(v, dim_su2, cas_su2)
    assert pairs["0,1"]["value_pow"] > S4 ** 3


def test_separator_su2_window_and_stability(su2_M1, su2_M2):
    # certified sigma window at M=1 sits in [7.0346e-8, 7.0347e-8]
    # (numpy cross-checked); M=2 within 0.2% of it (M-stable)
    G1 = gram_su2(su2_M1, [0, 1, 2, 3])
    r1 = separator_match(G1, [0, 1, 2, 3], S, cas_su2(1), dim_su2(1))
    lo, hi = r1["sigma"]
    assert r1["zero_rows"] == [3]
    assert Fr(70346, 10 ** 12) < lo <= hi < Fr(70347, 10 ** 12)
    T2, _win = su2_M2
    G2 = gram_su2(T2, [0, 1, 2])
    r2 = separator_match(G2, [0, 1, 2], S, cas_su2(1), dim_su2(1))
    lo2, hi2 = r2["sigma"]
    assert abs(lo2 - lo) < lo / 400          # < 0.25% shift M=1 -> M=2
    # both matched couplings far below s^4: the connected channel is
    # strongly suppressed at strong coupling (both groups; see below)
    assert r1["s_prime"][1] < S4


def test_separator_group_separation_by_magnitude(su2_M1, u1_M2):
    # U(1) keeps ~4x more connected transfer than SU(2): exact
    # window comparison, SU(2) hi < U(1) lo (both still below s^4)
    G_su2 = gram_su2(su2_M1, [0, 1, 2, 3])
    r_su2 = separator_match(G_su2, [0, 1, 2, 3], S, cas_su2(1),
                            dim_su2(1))
    G_u1 = gram_u1(u1_M2, [0, 1, -1, 2, -2])
    r_u1 = separator_match(G_u1, [0, 1, -1, 2, -2], S, 1, 1)
    assert Fr(13612, 10 ** 6) < r_u1["sigma"][0] <= r_u1["sigma"][1] \
        < Fr(13613, 10 ** 6)
    assert r_su2["sigma"][1] * 4 < r_u1["sigma"][0]
    assert r_u1["s_prime"][1] < S4


def test_u1_pair_ledger_contains_banked_witness(u1_M2):
    # pair(0,1) for U(1) IS the banked DP.6-U1 witness rho_1 * s^4
    from computations.flow_matching import cas_u1, dim_u1
    _idx, v = flowed_image(u1_M2, list(range(-2, 3)), S, dim_u1, cas_u1)
    pairs = pair_match(v, dim_u1, cas_u1)
    rho1 = Fr(14330603980276662272, 11258810062447479809)
    assert pairs["0,1"]["value_pow"] == rho1 * S4
