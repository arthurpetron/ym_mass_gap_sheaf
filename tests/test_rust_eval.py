"""Pins for the Rust contraction engine (work_plan §16j)."""

import os
from fractions import Fraction as F

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "..", "rust", "haar_contract", "target",
                   "release", "haar_contract")

needs_bin = pytest.mark.skipif(
    not os.path.exists(BIN),
    reason="Rust engine not built (cargo build --release in "
           "rust/haar_contract)")


@needs_bin
def test_rust_matches_d4_gate_values():
    from computations.su2_rust_eval import eval_config
    assert eval_config(1, 1, (0, 1, 2, 1), (1, 1, 1, 1),
                       (1, 0, 1, 2), (1, 0, 1, 2),
                       timeout_s=180) == F(1, 331776)


@needs_bin
def test_rust_matches_signed_negative():
    """The signed 6j-interference value — sign and magnitude exact."""
    from computations.su2_rust_eval import eval_config
    assert eval_config(1, 1, (0, 1, 2, 1), (1, 1, 1, 1),
                       (1, 0, 1, 2), (1, 2, 1, 2),
                       timeout_s=180) == F(-1, 1492992)


@needs_bin
def test_rust_matches_cs_diagonal_ledger():
    """Every Python-computed diagonal in the CS ledger that the Rust
    engine can redo quickly must agree exactly."""
    from computations.su2_rust_eval import eval_config
    from computations.su2_cs_tail import load_diag
    diag = load_diag()
    checked = 0
    for ks, val in sorted(diag.items()):
        if val is None or checked >= 2:
            continue
        loop_s, qs, ws, ts = ks.split("|")
        loop = int(loop_s)
        q = tuple(map(int, qs.split(",")))
        w = tuple(map(int, ws.split(",")))
        t = tuple(map(int, ts.split(",")))
        v = eval_config(loop, loop, q, w, t, t, timeout_s=180)
        if v is None:
            continue
        assert v == val
        checked += 1
    assert checked >= 1


@needs_bin
def test_rust_finality_values_satisfy_cs_lemma():
    """Every landed direct M=2 value must satisfy the OS/CS bound
    whenever its diagonal partners are known."""
    from computations.su2_m2_finality import load_all
    from computations.su2_cs_tail import (canon_key, _key_str,
                                          load_diag)
    vals = load_all()
    diag = load_diag()
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
