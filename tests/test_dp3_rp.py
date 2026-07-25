"""Pins for the DP.3 first RP data point (exponent granularity).

Layers:
  1. live recontraction gates for the cheap kernel entries (SU(2) via the
     exact Haar engine; the FULL U(1) grid via the lattice-point count);
  2. the saved kernel polynomials in dp3_rp_results.json pinned exactly;
  3. Gram algebra re-derived from the saved kernels: Sturm verdicts of
     every leading principal minor on (0,1), exact minors and LDL pivots
     at s = 1/2, PSD verdicts at all three probed s values;
  4. the pairing-identification pins: the U(1) OS Gram (conjugated) is
     PSD while the unconjugated control is NOT (negative 2x2 minor on
     all of (0,1)) — the antilinearity of theta is load-bearing.
"""

import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # repo root

from computations import dp3_rp_check as dp3  # noqa: E402


# ---------------------------------------------------------------------------
# Pinned kernel polynomials (M = 1, owned-boundary scheme).
# ---------------------------------------------------------------------------

SU2_PIN = {
    (0, 0): {0: 1, 18: 16, 30: 16, 36: 32, 42: 16, 48: 4},
    (0, 1): {12: 2, 24: 8, 30: 8, 36: 14},
    (0, 2): {48: 4},
    (0, 3): {},
    (1, 1): {24: 5, 30: 12, 36: 2},
    (1, 2): {36: 2},
    (1, 3): {},
    (2, 2): {48: 4},
    (2, 3): {},
    (3, 3): {},
}

U1_PIN = {
    (0, 0): {0: 1, 6: 8, 10: 8, 12: 8, 14: 8, 16: 2},
    (0, 1): {4: 1, 8: 4, 10: 4, 12: 7},
    (0, 2): {16: 1},
    (0, 3): {},
    (1, 1): {8: 1},
    (1, -1): {8: 2, 10: 12, 12: 2},
    (1, 2): {},
    (1, -2): {12: 1},
    (2, 2): {},
    (2, -2): {16: 1},
    (3, 3): {},
    (3, -3): {},
}


def _as_frac_poly(d):
    return {k: Fr(v) for k, v in d.items()}


# ---------------------------------------------------------------------------
# 1. Live recontraction gates (cheap entries only).
# ---------------------------------------------------------------------------


def test_su2_cheap_entries_live():
    from computations.slab_blocking_kernel import kernel_entry

    assert kernel_entry(1, 2, 1) == _as_frac_poly(SU2_PIN[(1, 2)])
    assert kernel_entry(2, 2, 1) == _as_frac_poly(SU2_PIN[(2, 2)])
    assert kernel_entry(0, 2, 1) == _as_frac_poly(SU2_PIN[(0, 2)])
    assert kernel_entry(0, 1, 1) == _as_frac_poly(SU2_PIN[(0, 1)])
    assert kernel_entry(0, 0, 1) == _as_frac_poly(SU2_PIN[(0, 0)])


def test_u1_full_grid_live_and_symmetries():
    from computations.dp6_u1_slab_blocking import (
        certify_kernel_basis,
        kernel_entry_u1,
    )

    assert certify_kernel_basis()
    T = {}
    for n in range(-3, 4):
        for m in range(-3, 4):
            T[(n, m)] = kernel_entry_u1(n, m, 1)
    for (n, m), pin in U1_PIN.items():
        assert T[(n, m)] == _as_frac_poly(pin), (n, m)
    # exact symmetries: z-flip and charge conjugation
    for n in range(-3, 4):
        for m in range(-3, 4):
            assert T[(n, m)] == T[(m, n)]
            assert T[(n, m)] == T[(-n, -m)]
    # the OS conjugation is material for U(1): T[1,1] != T[-1,1]
    assert T[(1, 1)] != T[(-1, 1)]


# ---------------------------------------------------------------------------
# 2 + 3. Saved kernels pinned; Gram algebra re-derived and pinned.
# ---------------------------------------------------------------------------


def _load():
    su2_T, u1_T, D = dp3.load_kernels_from_json()
    return su2_T, u1_T, D


def test_saved_kernels_match_pins():
    su2_T, u1_T, _ = _load()
    for (n, m), pin in SU2_PIN.items():
        assert su2_T[(n, m)] == _as_frac_poly(pin), ("su2", n, m)
    for (n, m), pin in U1_PIN.items():
        assert u1_T[(n, m)] == _as_frac_poly(pin), ("u1", n, m)


def test_su2_os_gram_minors_and_pivots():
    su2_T, _, _ = _load()
    a = dp3.analyze("SU2_OS_Gram", dp3.SU2_BASIS, dp3.gram_su2(su2_T),
                    verbose=False)
    assert a["zero_rows"] == [3]
    # Sturm verdicts on ALL of (0,1)
    assert [e["sturm"] for e in a["minors_poly"]] == [
        "positive", "positive", "positive", "zero"]
    # pinned 3x3 leading-minor polynomial (exponent-aggregated, exact)
    assert a["minors_poly"][2]["poly"] == _as_frac_poly({
        78: 48, 84: -120, 90: 128, 96: 320, 102: -128, 108: 256,
        114: 1152, 120: 448, 126: 128})
    # PSD at every probed s
    assert all(e["psd"] for e in a["per_s"])
    # exact pins at s = 1/2
    e = next(x for x in a["per_s"] if x["s"] == Fr(1, 2))
    assert e["minors"] == [
        Fr(70373040226561, 70368744177664),
        Fr(170108259427459713, 2417851639229258349412352),
        Fr(101501335277793, 664613997892457936451903530140172288),
        Fr(0),
    ]
    assert e["pivots"] == [
        Fr(70373040226561, 70368744177664),
        Fr(170108259427459713, 2417999250345375404392448),
        Fr(33833778425931, 15586334101769027236107649024),
        Fr(0),
    ]
    # pivot sign pattern: strictly positive until the exact-zero row
    assert [p > 0 for p in e["pivots"]] == [True, True, True, False]
    assert e["pivots"][3] == 0


def test_u1_os_gram_minors_and_pivots():
    _, u1_T, _ = _load()
    a = dp3.analyze("U1_OS_Gram", dp3.U1_BASIS, dp3.gram_u1(u1_T),
                    verbose=False)
    assert a["zero_rows"] == [3, -3]
    assert [e["sturm"] for e in a["minors_poly"]] == [
        "positive", "positive", "positive", "positive", "positive",
        "zero", "zero"]
    assert all(e["psd"] for e in a["per_s"])
    e = next(x for x in a["per_s"] if x["s"] == Fr(1, 2))
    assert e["minors"] == [
        Fr(37201, 32768),
        Fr(1054645, 67108864),
        Fr(29094681, 137438953472),
        Fr(41494529, 18014398509481984),
        Fr(921075, 36893488147419103232),
        Fr(0), Fr(0),
    ]
    assert e["pivots"] == [
        Fr(37201, 32768),
        Fr(1054645, 76187648),
        Fr(29094681, 2159912960),
        Fr(41494529, 3813498028032),
        Fr(921075, 84980795392),
        Fr(0), Fr(0),
    ]


def test_u1_unconjugated_control_fails():
    """The non-OS (unconjugated) pairing is NOT PSD: using it would have
    produced a spurious RP-violation verdict.  Pin the failure."""
    _, u1_T, _ = _load()
    a = dp3.analyze("ctrl", dp3.U1_BASIS, dp3.gram_u1_unconjugated(u1_T),
                    verbose=False)
    assert a["minors_poly"][1]["sturm"] == "negative"  # 2x2 minor < 0
    assert a["minors_poly"][1]["poly"] == _as_frac_poly({
        12: -8, 16: -30, 18: -24, 20: -64, 22: -48, 24: -47})
    for e in a["per_s"]:
        assert not e["psd"]
        assert e["witness"] == {"type": "negative_pivot", "index": 1}
    e = next(x for x in a["per_s"] if x["s"] == Fr(1, 2))
    assert e["pivots"][1] == Fr(-43247, 19046912)
    assert e["minors"][1] == Fr(-43247, 16777216)


def test_json_verdicts_match_rederivation():
    su2_T, u1_T, D = _load()
    for name, basis, gram in [
        ("SU2_OS_Gram", dp3.SU2_BASIS, dp3.gram_su2(su2_T)),
        ("U1_OS_Gram", dp3.U1_BASIS, dp3.gram_u1(u1_T)),
    ]:
        a = dp3.analyze(name, basis, gram, verbose=False)
        saved = D["grams"][name]
        assert saved["verdict_per_s"] == {
            str(e["s"]): bool(e["psd"]) for e in a["per_s"]}
        assert saved["zero_rows"] == a["zero_rows"]
        assert [e["sturm"] for e in saved["minors_poly"]] == [
            e["sturm"] for e in a["minors_poly"]]
