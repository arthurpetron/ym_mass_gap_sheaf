"""Pins for computations.c_su2_assembly (MD.3, work_plan §16f).

Every pin is an exact rational identity; no floats, no tolerance.
"""

import json
import math
import os
from fractions import Fraction as F

import pytest

from computations.c_su2_assembly import (
    Series,
    SeriesU1,
    bch_gate,
    bch_parts,
    cas4,
    chain_gate,
    chain_net,
    flow_slope,
    slab_net,
    trace_word,
    u1_flow_gate,
    _trace_cache_gate,
)

HERE = os.path.dirname(os.path.abspath(__file__))


@pytest.fixture(scope="module")
def slab_series():
    return Series(slab_net())


def test_trace_cache_identities():
    assert _trace_cache_gate()


def test_bch_series_vs_matrix_log():
    assert bch_gate()


def test_bch2_is_classical():
    d2, d3 = bch_parts(2)
    # Delta2 component 0 = (1/2)(y0_1 y1_2 - y0_2 y1_1)
    assert d2[0][((0, 1), (1, 2))] == F(1, 2)
    assert d2[0][((0, 2), (1, 1))] == F(-1, 2)


def test_semigroup_chain_gates():
    """K*K = K: the entire tau^2 connected coefficient vanishes on
    the 1-, 2-, 3-link chains — the decisive engine identity."""
    for k in (1, 2, 3):
        ok, rows = chain_gate(k)
        assert ok, f"chain gate k={k} failed: {rows}"


def test_u1_mirror_c_dyn_zero():
    net = slab_net()
    su1 = SeriesU1(net)
    for (n, m) in ((1, 1), (1, 2), (2, 2)):
        closed = su1.s12_closed(n, m)
        eng = su1.s12_engine(n, m)
        assert closed == eng
        assert eng[1] - eng[0] * eng[0] / 2 == 0


def test_u1_mirror_flow_c1():
    ok, res = u1_flow_gate(2)
    assert ok
    for v in res.values():
        assert v["E0"] == 3 and v["c1"] == F(-4)


def test_slab_s1_structure(slab_series):
    base = slab_series.s12(0, 0)[0]
    for (n, m) in ((1, 0), (1, 1), (2, 1), (3, 2)):
        s1, _ = slab_series.s12(n, m)
        assert s1 - base == -3 * (cas4(n) + cas4(m))


def test_slab_kappa2_closed_form(slab_series):
    """kappa2(n,m) - kappa2(0,0) = -(21/8)(Cn + Cm) + (2/3) Cn Cm."""
    def kap(n, m):
        s1, s2 = slab_series.s12(n, m)
        return s2 - s1 * s1 / 2

    k0 = kap(0, 0)
    for (n, m) in ((1, 0), (1, 1), (2, 1), (2, 2), (3, 1), (4, 2)):
        cn, cm = F(cas4(n)), F(cas4(m))
        want = -F(21, 8) * (cn + cm) + F(2, 3) * cn * cm
        assert kap(n, m) - k0 == want


def test_slab_flow_slopes(slab_series):
    """c_SU2(N) = 21/8 - (2/3) E_w[C(m)], pair-independent; the
    banked values 41/40, -11/8, -183/40 at N = 1, 2, 3."""
    want = {1: F(41, 40), 2: F(-11, 8), 3: F(-183, 40)}
    cache = {}

    def sfun(n, m):
        if (n, m) not in cache:
            cache[(n, m)] = slab_series.s12(n, m)
        return cache[(n, m)]

    for N, cval in want.items():
        flow = flow_slope(sfun, N, lambda m: m + 1, cas4,
                          list(range(0, N + 1)))
        for v in flow.values():
            assert v["E0"] == 3
            assert v["c1"] == cval


def test_x11_exactly_six(slab_series):
    def kap(n, m):
        s1, s2 = slab_series.s12(n, m)
        return s2 - s1 * s1 / 2

    x11 = kap(1, 1) + kap(0, 0) - kap(1, 0) - kap(0, 1)
    assert x11 == 6
    # and the general form (2/3) Cn Cm:
    x12 = kap(1, 2) + kap(0, 0) - kap(1, 0) - kap(0, 2)
    assert x12 == F(2, 3) * cas4(1) * cas4(2)


def test_x11_positive_on_exact_m2_kernel():
    """Exact-rational sign pin on the banked M=2 SU(2) kernel:
    T[1,1] T[0,0] - T[0,1]^2 > 0 (the flat-limit +6 tau^2 sign) at
    moderate couplings where the M=2 tails are certifiably tiny."""
    path = os.path.join(HERE, "..", "computations",
                        "dp3_m2_entries.json")
    with open(path) as fh:
        d = json.load(fh)

    def poly(key):
        return {int(k): F(v[0], v[1]) for k, v in d[key]["poly"].items()}

    P = {k: poly(k) for k in ("0,0", "1,1", "0,1")}

    def ev(p, s):
        return sum(c * s ** k for k, c in p.items())

    for (num, den) in ((1, 2), (13, 20), (3, 4), (4, 5)):
        s = F(num, den)
        assert ev(P["1,1"], s) * ev(P["0,0"], s) \
            > ev(P["0,1"], s) ** 2


def test_ledger_exists_and_gates_green():
    path = os.path.join(HERE, "..", "computations",
                        "c_su2_assembly_results.json")
    if not os.path.exists(path):
        pytest.skip("ledger not generated in this tree")
    with open(path) as fh:
        res = json.load(fh)
    assert res["bch_gate"] and res["chain_gates"] and res["u1_mirror"]
    assert res["kappa2_fit_exact"] and res["closed_form_gate"]
    assert res["c_dyn"] == "21/8"
    assert res["X11_tau2"] == "6"
