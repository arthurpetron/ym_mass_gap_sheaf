"""Pins for su2_cut_eval and su2_m2_finality (work_plan §16i)."""

import json
import math
import os
from fractions import Fraction as F

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
COMP = os.path.join(HERE, "..", "computations")


def test_ordered_elimination_agrees_with_greedy():
    """The corner-sweep ordered elimination computes the same exact
    invariant as the greedy engine (light spin-<=1 case)."""
    from computations.su2_cut_eval import (corner_orders,
                                           eliminate_ordered,
                                           _factors, _to_scalar)
    from computations.dp3_fixed_tile import network_value_fixed
    case = (1, 1, (0, 1, 0, 1), (1, 1, 1, 1), (1, 0, 1, 0),
            (1, 0, 1, 0))
    ref = network_value_fixed(*case)
    ref = ref[0] if ref else F(0)
    for order in corner_orders()[:2]:
        v = _to_scalar(eliminate_ordered(_factors(*case), order))
        assert v == ref


def test_network_value_fast_greedy_path():
    from computations.su2_cut_eval import network_value_fast
    v = network_value_fast(1, 1, (1, 1, 1, 1), (0, 2, 0, 2),
                           (0, 0, 2, 2), (0, 0, 2, 2),
                           greedy_first_s=120)
    assert v == F(1, 62208)


def test_corner_orders_cover_free_links():
    from computations.su2_cut_eval import corner_orders
    from computations.slab_blocking_kernel import _CX
    for order in corner_orders():
        assert sorted(order) == sorted(_CX.free)


def test_finality_ledger_values_consistent():
    """Every landed direct M=2 value must respect the OS/CS bound
    where its diagonal partners exist (lemma consistency)."""
    from computations.su2_m2_finality import load_all
    from computations.su2_cs_tail import (canon_key, _key_str,
                                          load_diag)
    vals = load_all()
    diag = load_diag()
    checked = 0
    for ks, v in vals.items():
        if v is None:
            continue
        entry, qs, ws, ts, bs = ks.split("|")
        n, m = map(int, entry.split(","))
        q = tuple(map(int, qs.split(",")))
        w = tuple(map(int, ws.split(",")))
        top = tuple(map(int, ts.split(",")))
        bot = tuple(map(int, bs.split(",")))
        val = F(int(v[0]), int(v[1]))
        da = diag.get(_key_str(canon_key(n, q, w, top)))
        db = diag.get(_key_str(canon_key(m, q, w, bot)))
        if da is not None and db is not None:
            assert val * val <= da * db
            checked += 1
    # checked may be 0 if no direct values landed; that's fine


def test_combined_window_at_half_and_11_20():
    """The combined assembly must reproduce (or beat) the §16h
    certified windows."""
    from computations.su2_m2_finality import combined_x11_window
    r = combined_x11_window(F(1, 2))
    assert r["positive"] and r["ratio_gt_1_certified"]
    assert r["X11_lo"] > 0.25 and r["X11_hi"] < 0.26
    r2 = combined_x11_window(F(11, 20))
    assert r2["positive"] and r2["ratio_gt_1_certified"]
    assert r2["X11_lo"] > 0.25


def test_u2_cs_residual_not_worse_than_crude():
    from computations.su2_m2_finality import (cs_sharpened_u2,
                                              resolved_and_residual)
    s = F(3, 5)
    for entry, (n, m) in (("0,0", (0, 0)), ("1,1", (1, 1)),
                          ("0,1", (0, 1))):
        add1, res1, _k1 = resolved_and_residual(entry, n, m, s)
        add2, res2, _k2, _ncs = cs_sharpened_u2(entry, n, m, s)
        assert add1 == add2
        assert res2 <= res1
