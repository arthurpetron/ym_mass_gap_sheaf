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

"""Deliverable (1)+(2): build the exact cap<=2 sector family with
per-half-config Haar values, sector kernels, and exact PSD verdicts."""
import itertools
import pickle
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, '/home/claude/ym')
sys.set_int_max_str_digits(0)

from . import slabnet as sl
from computations.exact_haar_network import casimir4, dim
from .psdtools import esym_psd, is_symmetric, ldl_psd

NM = [(0, 0), (0, 1), (1, 0), (1, 1)]


def wsec(q, w):
    c = 1
    e = 0
    for qi in q:
        c *= dim(qi) ** 2
        e += 2 * casimir4(qi)
    for wi in w:
        c *= dim(wi)
        e += casimir4(wi)
    return F(c), e


def build(cap, M):
    out = {}
    t0 = time.time()
    nq = 0
    for q in itertools.product(range(cap + 1), repeat=4):
        for w in itertools.product(range(cap + 1), repeat=4):
            nq += 1
            L = {0: sl.layers(0, q, w, M), 1: sl.layers(1, q, w, M)}
            if not L[0] and not L[1]:
                continue
            hs = [(0, t) for t in L[0]] + [(1, t) for t in L[1]]
            Ntab = {}
            for (n, a) in hs:
                for (m, b) in hs:
                    Ntab[((n, a), (m, b))] = sl.N(n, m, q, w, a, b)
            # sector kernel per (n,m)
            G = {}
            for (n, m) in NM:
                acc = {}
                for a in L[n]:
                    for b in L[m]:
                        v = Ntab[((n, a), (m, b))]
                        if not v:
                            continue
                        c = v
                        for x in a:
                            c *= dim(x)
                        for y in b:
                            c *= dim(y)
                        e = (sum(casimir4(x) for x in a)
                             + sum(casimir4(y) for y in b))
                        acc[e] = acc.get(e, F(0)) + c
                G[(n, m)] = {k: v for k, v in acc.items() if v}
            if not any(G.values()):
                continue
            out[(q, w)] = {'L0': L[0], 'L1': L[1], 'hs': hs,
                           'N': Ntab, 'G': G}
            if len(out) % 50 == 0:
                print(f'  {len(out)} sectors ({nq} pairs scanned) '
                      f'{time.time()-t0:.0f}s', flush=True)
    return out, time.time() - t0


def hmatrix(sec):
    hs = sec['hs']
    Nt = sec['N']
    return [[Nt[(h1, h2)] for h2 in hs] for h1 in hs]


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    print(f'=== building cap<={cap} at M={M}', flush=True)
    S, wall = build(cap, M)
    print(f'cap<={cap} M={M}: {len(S)} nonzero sectors, {wall:.1f}s wall',
          flush=True)

    # --- M-independence: rebuild at M+1 and demand identical kernels
    t = time.time()
    Sp, wall2 = build(cap, M + 1)
    same_keys = set(S) == set(Sp)
    diffs = [k for k in S if S[k]['G'] != Sp[k]['G']]
    print(f'M-independence M={M} vs M={M+1}: same sector set={same_keys}, '
          f'kernel diffs={len(diffs)} ({wall2:.1f}s)', flush=True)
    if M >= 3:
        Sm, _ = build(cap, M - 1)
        dm = [k for k in S if S[k]['G'] != Sm.get(k, {}).get('G')]
        print(f'  non-vacuity: M={M-1} differs on {len(dm)} sectors '
              f'(truncation still active there)', flush=True)

    # --- PSD gate on the half-config Gram H
    print('=== PSD gate on half-config Gram H', flush=True)
    t = time.time()
    fails = []
    stats = {}
    order = sorted(S, key=lambda k: -(sum(k[0]) * 2 + sum(k[1])))
    for i, k in enumerate(order):
        Hm = hmatrix(S[k])
        n = len(Hm)
        sym = is_symmetric(Hm)
        ok1, msg1 = ldl_psd(Hm)
        ok2, msg2 = esym_psd(Hm)
        S[k]['psd'] = (sym, ok1, ok2, n)
        stats[n] = stats.get(n, 0) + 1
        if not (sym and ok1 and ok2):
            fails.append((k, sym, ok1, msg1, ok2, msg2, n))
            print('  PSD FAILURE', k, 'sym', sym, 'ldl', ok1, msg1,
                  'esym', ok2, msg2, flush=True)
        if i % 100 == 0:
            print(f'  {i}/{len(order)} checked {time.time()-t:.0f}s',
                  flush=True)
    print(f'PSD gate: {len(S)} sectors, {len(fails)} FAILURES, '
          f'{time.time()-t:.0f}s', flush=True)
    print('  H sizes histogram:', dict(sorted(stats.items())), flush=True)

    pickle.dump({'cap': cap, 'M': M, 'sectors': S, 'psd_fails': fails,
                 'wall': wall},
                open(f'/home/claude/ym/sec_cap{cap}.pkl', 'wb'))
    print(f'pickled -> /home/claude/ym/sec_cap{cap}.pkl', flush=True)


if __name__ == '__main__':
    main()
