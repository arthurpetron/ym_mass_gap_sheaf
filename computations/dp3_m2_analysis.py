"""DP.3 at activity truncation M = 2 — verdicts, with per-exponent rigor.

**Rigor device.**  A slab configuration contributes to exactly ONE
s-exponent, E(config).  Hence a computed coefficient at exponent E is
FINAL — equal to the true coefficient — as soon as no UNREACHED
configuration sits at that same E.  This is strictly sharper than the
global "exact below the smallest unreached E" window: a coefficient can
be final even when it lies far above that window, provided the
unreached configurations happen to land on other exponents.

The same device lifts to the blocked image
`(Bv)_n = sum_m T[n,m] * d_m s^{C(m)}`: its coefficient at exponent E is
final iff, for every m, no unreached configuration of T[n,m] sits at
exponent E - C(m).

Consumers:
  * `entry_verdicts()`   — per-entry coefficientwise sign audit
  * `blocked_verdicts()` — the aggregated cone-preservation test
  * `final_at(...)`      — the per-exponent finality predicate
"""
from __future__ import annotations

import glob
import json
import os
from fractions import Fraction
from typing import Dict, List, Tuple

from computations.exact_haar_network import casimir4, dim

Frac = Fraction
SPoly = Dict[int, Fraction]

RESULTS_GLOB = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "dp3_m2_entries*.json")


def load(pattern: str = None):
    """Return (T, unreached_exponents, window) keyed by (n, m)."""
    T: Dict[Tuple[int, int], SPoly] = {}
    UN: Dict[Tuple[int, int], List[int]] = {}
    W: Dict[Tuple[int, int], int] = {}
    for f in sorted(glob.glob(pattern or RESULTS_GLOB)):
        for key, rec in json.load(open(f)).items():
            n, m = map(int, key.split(","))
            poly = {int(p): Frac(a, b) for p, (a, b) in rec["poly"].items()}
            un = [u["E"] for u in rec["unreached"]]
            for k in ((n, m), (m, n)):
                T[k] = poly
                UN[k] = un
                W[k] = rec["exact_below_E"]
    return T, UN, W


def final_at(UN, key, E: int) -> bool:
    """Is the coefficient of T[key] at exponent E equal to the true one?

    True iff no unreached configuration of that entry sits at exponent E
    (each configuration contributes to exactly one exponent)."""
    return key in UN and E not in UN[key]


def entry_verdicts(T, UN, W):
    """Coefficientwise sign audit per entry, with per-coefficient rigor."""
    out = {}
    for key in sorted({tuple(sorted(k)) for k in T}):
        poly = T[key]
        negs = sorted((e, c) for e, c in poly.items() if c < 0)
        rig = [(e, c) for e, c in negs if final_at(UN, key, e)]
        out[key] = {
            "n_terms": len(poly),
            "negative": [(e, str(c)) for e, c in negs],
            "negative_final": [(e, str(c)) for e, c in rig],
            "window": W.get(key),
        }
    return out


def blocked_image(T, n: int, ms=(0, 1, 2)) -> SPoly:
    """(Bv)_n for the heat-kernel envelope v_m = d_m s^{C(m)}."""
    out: SPoly = {}
    for m in ms:
        if (n, m) not in T:
            raise KeyError((n, m))
        shift, coef = casimir4(m), Frac(dim(m))
        for e, c in T[(n, m)].items():
            out[e + shift] = out.get(e + shift, Frac(0)) + coef * c
    return {k: v for k, v in out.items() if v}


def blocked_final_at(UN, n: int, E: int, ms=(0, 1, 2)) -> bool:
    return all(final_at(UN, (n, m), E - casimir4(m)) for m in ms)


def blocked_verdicts(T, UN, ms=(0, 1, 2)):
    out = {}
    for n in ms:
        try:
            B = blocked_image(T, n, ms)
        except KeyError:
            continue
        negs = sorted((e, c) for e, c in B.items() if c < 0)
        rig = [(e, c) for e, c in negs if blocked_final_at(UN, n, e, ms)]
        out[n] = {
            "n_terms": len(B),
            "negative": [(e, str(c)) for e, c in negs],
            "negative_final": [(e, str(c)) for e, c in rig],
        }
    return out


def contributions_to(T, n: int, E: int, ms=(0, 1, 2)):
    """Per-m breakdown of the (Bv)_n coefficient at exponent E."""
    rows = []
    for m in ms:
        C = casimir4(m)
        c = T[(n, m)].get(E - C, Frac(0))
        rows.append((m, E - C, c, Frac(dim(m)) * c))
    return rows
