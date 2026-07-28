"""DP.2/DP.3 at activity truncation M = 2 — resumable skeleton driver.

Reassembles `slab_blocking_kernel.kernel_entry_skeleton` EXACTLY (same
D4 class enumeration, same layer-feasibility prefilter, same weight
formula) but with (a) a per-class wall-clock budget that is a reported
parameter rather than a hard-coded 120 s, (b) per-class timing, and
(c) a disk cache so an interrupted run resumes instead of restarting.

Equality with the repo function is GATED, not assumed: `gate_M1()`
reproduces `kernel_entry_skeleton(n, m, 1)` for every n, m <= nmax and
asserts exact polynomial equality.  Only then is the driver used at
M = 2, where the repo function's fixed 120 s alarm is impractical.

UNREACHED classes are recorded with their (q, w) and the budget that
expired.  They are NOT silently dropped: every consumer of this data
must carry the UNREACHED list, and the truncation error they induce is
part of the eps_slab(M) modulus (Simplification Ledger item 7).
"""

from __future__ import annotations

import json
import os
import signal
import time
from fractions import Fraction
from typing import Dict, List, Tuple

from computations.exact_haar_network import casimir4, dim
from computations.slab_blocking_kernel import (
    _canon,
    _skeletons,
    kernel_entry_skeleton,
    skeleton_value,
)

Frac = Fraction
SPoly = Dict[int, Fraction]

CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "dp3_m2_cache.json")


def _classes(M: int):
    cl: Dict[Tuple, List[Tuple]] = {}
    for q, w in _skeletons(M):
        cl.setdefault(_canon(q, w), []).append((q, w))
    return cl


def wpow(q, w) -> int:
    """Minimum s-exponent the skeleton class (q, w) can contribute.

    A class enters T only through `out[p + wpow]` with p >= 0 (tile
    heat-activity exponents are nonnegative), so every coefficient of
    degree < wpow(q, w) is untouched by that class.  Processing classes
    in ascending wpow therefore makes the EXACTNESS WINDOW
    D = min{ wpow(q, w) : (q, w) UNREACHED } as large as the budget
    allows: all computed coefficients below D are exact regardless of
    which expensive high-spin classes timed out.
    """
    return sum(2 * casimir4(qi) for qi in q) + sum(casimir4(wi) for wi in w)


def _triad_ok(a: int, b: int, c: int) -> bool:
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


def _layer_feasible(nn: int, q, w, M: int) -> bool:
    cand = [[a for a in range(M + 1) if _triad_ok(nn, qi, a)] for qi in q]
    if any(not c for c in cand):
        return False

    def rec(i, chosen):
        if i == 4:
            return _triad_ok(chosen[3], chosen[0], w[3])
        for a in cand[i]:
            if i > 0 and not _triad_ok(chosen[-1], a, w[i - 1]):
                continue
            if rec(i + 1, chosen + [a]):
                return True
        return False

    return rec(0, [])


def _load_cache():
    if os.path.exists(CACHE):
        with open(CACHE) as fh:
            raw = json.load(fh)
        out = {}
        for k, v in raw.items():
            out[k] = (None if v is None
                      else {int(p): Frac(a, b) for p, (a, b) in v.items()})
        return out
    return {}


def _save_cache(cache):
    tmp = CACHE + ".tmp"
    with open(tmp, "w") as fh:
        json.dump({k: (None if v is None
                       else {str(p): [c.numerator, c.denominator]
                             for p, c in v.items()})
                   for k, v in cache.items()}, fh)
    os.replace(tmp, CACHE)


def entry(n: int, m: int, M: int, budget: int = 120, progress: bool = False,
          cache=None, save_every: int = 3):
    """Exact T[n,m] at truncation M; returns (poly, unreached, timings)."""
    if cache is None:
        cache = _load_cache()
    out: SPoly = {}
    unreached: List[Tuple] = []
    timings: List[Tuple] = []
    dirty = 0
    ordered = sorted(_classes(M).items(), key=lambda kv: (wpow(*kv[0]), kv[0]))
    for rep, members in ordered:
        q, w = rep
        if not _layer_feasible(n, q, w, M) or not _layer_feasible(m, q, w, M):
            continue
        key = f"{n}|{m}|{M}|{q}|{w}"
        if key in cache:
            val = cache[key]
            if val is None:
                unreached.append((q, w, "cached-unreached"))
                continue
        else:
            t0 = time.time()

            def _alarm(_s, _f):
                raise TimeoutError(f"per-skeleton budget {budget}s exceeded")

            old = signal.signal(signal.SIGALRM, _alarm)
            signal.alarm(budget)
            try:
                val = skeleton_value(n, m, q, w, M)
            except Exception as exc:
                cache[key] = None
                dirty += 1
                unreached.append((q, w, str(exc)))
                if progress:
                    print(f"    UNREACHED q={q} w={w}: {exc}", flush=True)
                _save_cache(cache)
                dirty = 0
                continue
            finally:
                signal.alarm(0)
                signal.signal(signal.SIGALRM, old)
            dt = time.time() - t0
            timings.append((q, w, dt))
            cache[key] = val
            dirty += 1
            if progress and dt > 5:
                print(f"    q={q} w={w}: {dt:.1f}s, {len(val)} terms",
                      flush=True)
            if dirty >= save_every:
                _save_cache(cache)
                dirty = 0
        if not val:
            continue
        wp = wpow(q, w)
        wc = Frac(1)
        for qi in q:
            wc *= dim(qi) ** 2
        for wi in w:
            wc *= dim(wi)
        for p, c in val.items():
            out[p + wp] = out.get(p + wp, Frac(0)) + c * wc * len(members)
    if dirty:
        _save_cache(cache)
    return {p: c for p, c in out.items() if c}, unreached, timings


def gate_M1(nmax: int = 3, verbose: bool = True) -> bool:
    """Driver must reproduce the repo function exactly at M = 1."""
    ok = True
    for n in range(nmax + 1):
        for m in range(n, nmax + 1):
            mine, un, _ = entry(n, m, 1, budget=120)
            theirs = kernel_entry_skeleton(n, m, 1)
            good = (mine == theirs) and not un
            ok &= good
            if verbose:
                print(f"  gate M=1 T[{n},{m}]: "
                      f"{'OK' if good else 'MISMATCH'}", flush=True)
    return ok
