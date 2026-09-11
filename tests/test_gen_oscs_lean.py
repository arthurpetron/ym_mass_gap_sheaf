"""Pins for the OSCSLedger.lean generator (work_plan §16k).

The generator is pure Python; these tests never invoke Lean (host
safety: no Lean process may be launched from the test suite).  The
Lean-side verification protocol is the spike convention: elaborate
under the pinned toolchain, `#print axioms` on every theorem,
mutation battery — recorded in dual_kappa_spike/README.md.
"""

import os
import subprocess
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
GEN = os.path.join(ROOT, "scripts", "gen_oscs_lean.py")


def _emit() -> str:
    proc = subprocess.run([sys.executable, GEN], capture_output=True,
                          timeout=300)
    assert proc.returncode == 0, proc.stderr.decode()[:2000]
    return proc.stdout.decode()


def test_generator_emits_all_theorems():
    src = _emit()
    for thm in ("diag_count", "diag_nonneg", "diag_le_crude",
                "m2_count", "m2_negative_count", "m2_le_crude",
                "cs_count", "cs_partners_located", "cs_bound_all"):
        assert f"theorem {thm}" in src, thm
    assert "namespace OSCSLedger" in src
    assert "end OSCSLedger" in src
    # no classical escape hatches in the emitted file
    for bad in ("Classical", "native_decide", "sorry", "axiom "):
        assert bad not in src, bad


def test_counts_match_merged_ledgers():
    from computations.su2_cs_tail import load_diag
    from computations.su2_m2_finality import load_all
    src = _emit()
    diag = load_diag()
    n_diag = sum(1 for v in diag.values() if v is not None)
    m2 = load_all()
    n_m2 = sum(1 for v in m2.values() if v is not None)
    assert f"diagLedger.length = {n_diag}" in src
    assert f"m2Ledger.length = {n_m2}" in src


def test_cs_rows_verified_in_python():
    """Every emitted CS row must satisfy N^2 <= Da*Db and cite partner
    values that really sit in the diagonal ledger under the D4 action
    (independent recomputation of what the Lean kernel re-checks)."""
    from computations.su2_cs_tail import canon_key, _key_str, load_diag
    from computations.su2_m2_finality import load_all
    diag = load_diag()
    m2 = load_all()
    rows = 0
    for ks, v in m2.items():
        if v is None:
            continue
        entry, qs, ws, ts, bs = ks.split("|")
        n, m = map(int, entry.split(","))
        q = tuple(map(int, qs.split(",")))
        w = tuple(map(int, ws.split(",")))
        top = tuple(map(int, ts.split(",")))
        bot = tuple(map(int, bs.split(",")))
        da = diag.get(_key_str(canon_key(n, q, w, top)))
        db = diag.get(_key_str(canon_key(m, q, w, bot)))
        if da is None or db is None:
            continue
        val = F(int(v[0]), int(v[1]))
        assert val * val <= da * db, ks
        assert da >= 0 and db >= 0
        rows += 1
    assert rows >= 6
    src = _emit()
    assert f"csRows.length = {rows}" in src
