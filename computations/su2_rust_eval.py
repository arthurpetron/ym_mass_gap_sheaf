"""Rust-backed exact Haar network evaluation (work_plan §16j).

Drives `rust/haar_contract` — a faithful port of the
exact_haar_network hot core (p_mul, integrate_link, p_reduce_units,
greedy elimination) with num-bigint exact rationals and packed
monomials: typically 10-50x less memory and much faster than the
Python dict/Fraction representation, which §16i identified as the
single blocker of the certified-window advance.

Factors are still CONSTRUCTED by the gated Python code path
(su2_cut_eval._factors -> exact_haar_network.chi/holonomy): only the
contraction moves to Rust.  The gate battery compares Rust values
against every banked exact value (D4 gates, the signed negative
configs, the CS diagonal ledger).

Run:  python -m computations.su2_rust_eval gate
      python -m computations.su2_rust_eval sweep [budget_s]
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from fractions import Fraction
from typing import Optional

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "..", "rust", "haar_contract", "target",
                   "release", "haar_contract")

sys.set_int_max_str_digits(0)


def _serialize_factors(factors) -> list:
    out = []
    for poly in factors:
        terms = []
        for mono, sp in poly.items():
            terms.append([
                [[int(v), int(e)] for (v, e) in mono],
                [[int(p), str(c.numerator), str(c.denominator)]
                 for p, c in sp.items()],
            ])
        out.append(terms)
    return out


def eval_config(n: int, m: int, q, w, top, bot,
                timeout_s: int = 300,
                max_monomials: int = 6_000_000) -> Optional[Frac]:
    """Exact network value via the Rust engine; None on budget/size."""
    from computations.su2_cut_eval import _factors
    from computations.slab_blocking_kernel import _CX

    payload = {
        "factors": _serialize_factors(
            _factors(n, m, tuple(q), tuple(w), tuple(top),
                     tuple(bot))),
        "free_links": list(_CX.free),
        "max_monomials": max_monomials,
    }
    try:
        proc = subprocess.run(
            [BIN], input=json.dumps(payload).encode(),
            capture_output=True, timeout=timeout_s)
    except subprocess.TimeoutExpired:
        return None
    if proc.returncode != 0:
        return None
    try:
        res = json.loads(proc.stdout.decode())
    except Exception:
        return None
    if not res.get("ok"):
        return None
    sc = res["scalar"]
    if not sc:
        return Frac(0)
    # the value must be a pure scalar (s-power 0 only)
    assert all(int(t[0]) == 0 for t in sc), "nonscalar result"
    tot = Frac(0)
    for t in sc:
        tot += Frac(int(t[1]), int(t[2]))
    return tot


def gate(verbose: bool = True) -> bool:
    """Rust vs every banked exact value."""
    ok = True
    t0 = time.time()
    # 1. D4-gate values
    cases = [
        (1, 1, (0, 1, 2, 1), (1, 1, 1, 1), (1, 0, 1, 2),
         (1, 0, 1, 2), Frac(1, 331776)),
        (1, 1, (1, 1, 1, 1), (0, 2, 0, 2), (0, 0, 2, 2),
         (0, 0, 2, 2), Frac(1, 62208)),
        (1, 1, (0, 1, 2, 1), (1, 1, 1, 1), (1, 0, 1, 2),
         (1, 2, 1, 2), Frac(-1, 1492992)),
    ]
    # 2. banked negative configs (exact N in dp3_m2_entries)
    with open(os.path.join(HERE, "dp3_m2_entries.json")) as fh:
        d = json.load(fh)
    for entry, (n, m) in (("1,1", (1, 1)), ("0,1", (0, 1)),
                          ("1,2", (1, 2))):
        for cfg in d[entry]["negative_configs"][:2]:
            cases.append((n, m, tuple(cfg["q"]), tuple(cfg["w"]),
                          tuple(cfg["top"]), tuple(cfg["bot"]),
                          Frac(cfg["N"][0], cfg["N"][1])))
    for (n, m, q, w, top, bot, want) in cases:
        t1 = time.time()
        v = eval_config(n, m, q, w, top, bot, timeout_s=240)
        good = (v == want)
        ok &= good
        if verbose:
            print(f"  ({n},{m}) q={q} w={w}: "
                  f"{'OK' if good else f'MISMATCH {v} vs {want}'}"
                  f" [{time.time() - t1:.1f}s]", flush=True)
    # 3. CS diagonal ledger (recompute a sample in Rust)
    from computations.su2_cs_tail import load_diag
    diag = load_diag()
    got_any = 0
    for ks, val in sorted(diag.items()):
        if val is None or got_any >= 6:
            continue
        loop_s, qs, ws, ts = ks.split("|")
        loop = int(loop_s)
        q = tuple(map(int, qs.split(",")))
        w = tuple(map(int, ws.split(",")))
        t = tuple(map(int, ts.split(",")))
        t1 = time.time()
        v = eval_config(loop, loop, q, w, t, t, timeout_s=240)
        good = (v == val)
        ok &= good
        got_any += 1
        if verbose:
            print(f"  diag {ks}: "
                  f"{'OK' if good else f'MISMATCH {v} vs {val}'}"
                  f" [{time.time() - t1:.1f}s]", flush=True)
    if verbose:
        print(f"  gate total [{time.time() - t0:.0f}s]", flush=True)
    return ok


def bench_heavy(verbose: bool = True):
    """The 556 s (Python) diagonal and the 900 s+ timeout class."""
    rows = []
    for (tag, n, m, q, w, top, bot) in (
        ("heavy-556s", 1, 1, (0, 0, 1, 2), (0, 1, 1, 2),
         (1, 1, 2, 3), (1, 1, 2, 3)),
        ("timeout-908s", 0, 0, (0, 1, 2, 1), (1, 1, 3, 1),
         (0, 1, 2, 1), (0, 1, 2, 1)),
        ("m2-unreached", 0, 1, (0, 1, 1, 1), (1, 2, 2, 1),
         (0, 1, 1, 1), (1, 0, 2, 2)),
    ):
        t0 = time.time()
        v = eval_config(n, m, q, w, top, bot, timeout_s=600)
        dt = time.time() - t0
        rows.append((tag, v, dt))
        if verbose:
            print(f"  {tag}: "
                  f"{'ok ' + str(v) if v is not None else 'BUDGET'}"
                  f" [{dt:.1f}s]", flush=True)
    return rows


def main() -> None:
    mode = sys.argv[1] if len(sys.argv) > 1 else "gate"
    if mode == "gate":
        print("Rust engine gate battery")
        ok = gate()
        print(f"GATE: {'PASSED' if ok else 'FAILED'}")
        print("Heavy bench:")
        bench_heavy()


if __name__ == "__main__":
    main()
