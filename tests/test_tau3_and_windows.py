"""Pins for c_su2_tau3, su2_flat_slack, su2_minf_windows
(work_plan §16g).

Heavy recomputations (the slab tau^3 cross blocks, ~10 min) are
pinned through their ledgers; the exact gates that run in seconds
are re-executed live.
"""

import json
import math
import os
from fractions import Fraction as F

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
COMP = os.path.join(HERE, "..", "computations")


# ---------------------------------------------------------------------------
# tau^3 engine: live gates.
# ---------------------------------------------------------------------------


def test_bch_grades_4_5():
    from computations.c_su2_tau3 import bch45_gate
    assert bch45_gate()


def test_u1_mirror_kappa3_zero():
    from computations.c_su2_tau3 import u1_tau3_gate
    assert u1_tau3_gate()


def test_fusion_star_k1_closed_form():
    """Both loops on one link: engine must reproduce the exact
    fusion cumulants sum_J (2J+1) e^{-tau C(2J)} through kappa_3."""
    from computations.c_su2_tau3 import fusion_gate
    ok, rows = fusion_gate(1)
    assert ok, rows


def test_fusion_closed_cumulants_structure():
    """Var(delta_J) = (4/3) Cn Cm and mu3c(delta_J) = -(16/3) Cn Cm
    exactly: the fusion parts of the tau^2/tau^3 cross coefficients
    are (2/3) Cn Cm and (8/9) Cn Cm."""
    from computations.c_su2_tau3 import fusion_closed_cumulants
    from computations.c_su2_assembly import cas4
    for (n, m) in ((1, 1), (1, 2), (2, 2), (2, 3)):
        cc = cas4(n) * cas4(m)
        c1, c2, c3 = fusion_closed_cumulants(n, m, 1)
        assert c1 == -(cas4(n) + cas4(m))
        assert c2 == F(2, 3) * cc
        assert c3 == F(8, 9) * cc


def test_slab_x_tau3_ledger():
    """The banked slab result: X_nm = (2/3) C C tau^2
    + (115/54) C C tau^3, all gates green."""
    from computations.c_su2_assembly import cas4
    path = os.path.join(COMP, "c_su2_tau3_results.json")
    if not os.path.exists(path):
        pytest.skip("tau^3 ledger not generated in this tree")
    with open(path) as fh:
        res = json.load(fh)
    assert res["bch45"] and res["u1_tau3"] and res["star"] \
        and res["fusion"] and res["gram_internal"]
    for key, (n, m) in (("1,1", (1, 1)), ("1,2", (1, 2)),
                        ("2,2", (2, 2))):
        cc = cas4(n) * cas4(m)
        assert F(res["X"][key]["tau2"]) == F(2, 3) * cc
        assert F(res["X"][key]["tau3"]) == F(115, 54) * cc


# ---------------------------------------------------------------------------
# Image-slack certificate.
# ---------------------------------------------------------------------------


def test_eps_img_certificate_values():
    from computations.su2_flat_slack import eps_img
    e1 = eps_img(F(1, 20), F(1, 2))
    assert 0 < e1 < F(1, 10 ** 12)
    e2 = eps_img(F(1, 10), F(1, 2))
    assert 0 < e2 < F(1, 10 ** 5)
    # monotone in tau (smaller tau => smaller slack)
    assert e1 < e2


def test_eps_img_numeric_domination():
    from computations.su2_flat_slack import numeric_gate
    assert numeric_gate()


# ---------------------------------------------------------------------------
# M -> infinity domination windows.
# ---------------------------------------------------------------------------


def test_domination_gate():
    from computations.su2_minf_windows import (
        DomTransfer, entry_value_and_unreached, load_m2)
    d = load_m2()
    for s in (F(1, 2),):
        for key, (n, m) in (("0,0", (0, 0)), ("1,1", (1, 1)),
                            ("0,1", (0, 1))):
            dt = DomTransfer(n, m, s, 4)
            dom2 = dt.dominated_trace(2)
            t2, u2 = entry_value_and_unreached(d, key, n, m, s)
            assert dom2 + u2 >= t2


def test_x11_certified_positive_at_half():
    """THE consumer pin: at s = 1/2 the M -> infinity window of
    X_11 is certified positive (T11 T00 > T01^2 including all
    truncation corrections)."""
    from computations.su2_minf_windows import x11_window
    r = x11_window(F(1, 2))
    assert r["positive"]
    assert r["ratio_gt_1_certified"]
    assert r["X11_lo"] > F(1, 20)
    assert r["X11_hi"] < F(1, 2)


def test_tail_monotone_in_M():
    from computations.su2_minf_windows import tail_bound
    s = F(1, 2)
    t2 = tail_bound(1, 1, s, 2, 6)
    t3 = tail_bound(1, 1, s, 3, 6)
    assert 0 < t3 < t2
