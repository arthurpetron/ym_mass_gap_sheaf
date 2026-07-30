"""INDEPENDENT-REPLICATION TOOLING for the sector-SOS certificate
(work_plan §17g, notes/sector-sos-positivity.md).

STATUS: gated, NOT yet pinned in the test suite.  `spinnet` (the fast
exact rational spin-network evaluator) is gated BIT-FOR-BIT against the
incumbent evaluator `computations.dp3_fixed_tile.network_value_fixed` on
all 171 cap<=1 configurations, 320 character-orthogonality identities and
130 random networks (see `xcheck2`), and the cap<=1 family it rebuilds
reproduces `computations.sector_sos` exactly.  It exists only to build the
DISJOINT cap<=2 family (187 sectors) used as the independent replication
gate; nothing on the certificate's critical path depends on it.  Pinning
these modules in `tests/` is a named follow-up.
"""
from __future__ import annotations

"""N(n,m,q,w,top,bot) via the exact spin-network evaluator, plus a
cross-check against the upstream quaternion brute force."""

import sys
from fractions import Fraction as F
from functools import lru_cache

sys.set_int_max_str_digits(0)

from computations.dp3_fixed_tile import BOT_TILES, TOP_TILES
from computations.dp3_fixed_tile import network_value_fixed as _brute
from computations.exact_haar_network import casimir4, dim
from computations.slab_blocking_kernel import (
    _FACES, _IWALL_SIDES, _LOOP_BOT, _LOOP_TOP, _PWALL_CLASSES,
)
from .spinnet import haar_paths

_F = lambda fi: tuple(_FACES[fi])
_LT = tuple(_LOOP_TOP)
_LB = tuple(_LOOP_BOT)


@lru_cache(maxsize=None)
def N(n, m, q, w, top, bot) -> F:
    items = []
    for a, fi in zip(top, TOP_TILES):
        items.append((a, _F(fi)))
    for b, fi in zip(bot, BOT_TILES):
        items.append((b, _F(fi)))
    for qi, (fa, fb) in zip(q, _PWALL_CLASSES):
        items.append((qi, _F(fa)))
        items.append((qi, _F(fb)))
    for wi, fi in zip(w, _IWALL_SIDES):
        items.append((wi, _F(fi)))
    items.append((n, _LT))
    items.append((m, _LB))
    return haar_paths(items)


def _triad(a, b, c):
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


def layers(loop, q, w, M):
    import itertools
    cand = [[a for a in range(M + 1) if _triad(loop, qi, a)] for qi in q]
    return [t for t in itertools.product(*cand)
            if all(_triad(t[i - 1], t[i], w[i - 1]) for i in range(4))]


def sector_kernel(n, m, q, w, M):
    """skeleton_value_fixed(n,m,q,w,M) computed via the spin network."""
    out = {}
    for top in layers(n, q, w, M):
        for bot in layers(m, q, w, M):
            val = N(n, m, q, w, top, bot)
            if not val:
                continue
            c = val
            for a in top:
                c *= dim(a)
            for b in bot:
                c *= dim(b)
            e = sum(casimir4(a) for a in top) + sum(casimir4(b) for b in bot)
            out[e] = out.get(e, F(0)) + c
    return {k: v for k, v in out.items() if v}


def crosscheck(cases, verbose=True):
    """Demand exact agreement with the upstream brute force."""
    bad = []
    for c in cases:
        got = N(*c)
        ref = _brute(*c)
        refv = ref[0] if ref else F(0)
        if ref and set(ref) != {0}:
            bad.append(('nonscalar', c))
        elif got != refv:
            bad.append((c, str(got), str(refv)))
            if verbose:
                print('  MISMATCH', c, got, refv, flush=True)
    return bad
