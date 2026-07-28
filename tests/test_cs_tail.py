"""Pins for computations.su2_cs_tail (work_plan §16h): the OS/CS
lemma gate, the D4 canonicalization gate (via banked values), and
the sharpened certified windows.
"""

import json
import math
import os
from fractions import Fraction as F

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
COMP = os.path.join(HERE, "..", "computations")


def _diag():
    from computations.su2_cs_tail import load_diag
    return load_diag()


def test_cs_lemma_gate_on_banked_negatives():
    """|N|^2 <= D_a D_b on the banked exact negative network values
    — nontrivial: N < 0 from signed recoupling, the bound a product
    of OS norms."""
    from computations.su2_cs_tail import cs_gate
    ok, rows = cs_gate()
    checked = [r for r in rows if len(r) == 6]
    assert checked, "no gate cases had diagonal values available"
    assert ok, rows


def test_diagonal_values_nonnegative():
    """Every computed diagonal value is an OS norm: >= 0."""
    d = _diag()
    vals = [v for v in d.values() if v is not None]
    assert vals, "no diagonal values computed"
    assert all(v >= 0 for v in vals)


def test_level3_tail_certified_and_smaller_than_crude():
    from computations.su2_cs_tail import (level3_tail, level_configs,
                                          crude_bound,
                                          config_exponent)
    d = _diag()
    s = F(3, 5)
    sharp, used, tot = level3_tail(1, 1, s, d)
    crude = sum(crude_bound(1, 1, *c) * s ** config_exponent(*c)
                for c in level_configs(1, 1, 3))
    assert used > 0
    assert 0 < sharp < crude


def test_x11_window_sharpened_at_11_20():
    """The §16g domination windows closed above s = 1/2; the CS
    sharpening certifies X_11 > 0 at s = 11/20."""
    from computations.su2_cs_tail import sharpened_x11_window
    r = sharpened_x11_window(F(11, 20))
    assert r["positive"] and r["ratio_gt_1_certified"]
    assert r["X11_lo"] > 0.2


def test_x11_window_at_half_tighter_than_16g():
    from computations.su2_cs_tail import sharpened_x11_window
    r = sharpened_x11_window(F(1, 2))
    assert r["positive"] and r["ratio_gt_1_certified"]
    # §16g gave [0.0665, 0.4193]; the sharpened window must be
    # strictly inside
    assert r["X11_lo"] > 0.0665
    assert r["X11_hi"] < 0.4193


def test_ledger_gates_green():
    path = os.path.join(COMP, "su2_cs_tail_results.json")
    if not os.path.exists(path):
        pytest.skip("ledger not generated in this tree")
    with open(path) as fh:
        res = json.load(fh)
    assert res["cs_gate"]
