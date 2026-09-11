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

"""Follow-ups: (i) does any sector 2x2 det go NEGATIVE in (0,1)?
(ii) structure of the s=1 degeneracy; (iii) PSD for the zero-content
sectors too."""
import itertools
import pickle
import sys
from fractions import Fraction as F

sys.path.insert(0, '/home/claude/ym')
sys.set_int_max_str_digits(0)

from . import detsturm as ds
from .psdtools import esym_psd, is_symmetric, ldl_psd


def sqfree_decomp(P):
    """Yun: return list of (multiplicity, factor) for squarefree parts."""
    P = ds.trim(list(P))
    out = []
    a = ds.pgcd(P, ds.pdiff(P))
    b = ds.pdivexact(list(P), a) if len(a) > 1 else list(P)
    i = 1
    while len(b) > 1:
        c = ds.pgcd(b, a) if len(a) > 1 else [F(1)]
        f = ds.pdivexact(list(b), c) if len(c) > 1 else list(b)
        if len(f) > 1:
            out.append((i, f))
        if len(a) > 1 and len(c) > 1:
            a = ds.pdivexact(list(a), c)
        elif len(c) <= 1:
            a = a
        b = c
        i += 1
        if i > 60:
            break
    return out


def odd_part_roots_01(poly_dict):
    """#distinct roots of odd multiplicity strictly in (0,1) -> sign changes."""
    P, lo = ds.to_list(poly_dict)
    P = ds.trim(P)
    dec = sqfree_decomp(P)
    odd = [F(1)]
    for m, f in dec:
        if m % 2 == 1:
            odd = ds.trim(ds.pmul({i: c for i, c in enumerate(odd)},
                                  {i: c for i, c in enumerate(f)}))
            odd = [odd.get(i, F(0)) if isinstance(odd, dict) else odd[i]
                   for i in range(len(odd))] if isinstance(odd, dict) else odd
    if isinstance(odd, dict):
        odd = ds.trim([odd.get(i, F(0)) for i in range(max(odd) + 1)])
    if len(odd) <= 1:
        return 0, dec
    ch = ds.sturm_chain(odd)
    n0 = ds.sign_changes(ch, F(0))
    n1 = ds.sign_changes(ch, F(1))
    at1 = ds.evl(odd, F(1)) == 0
    return n0 - n1 - (1 if at1 else 0), dec


def bisect_sign(poly_dict, lo, hi, depth=40):
    """Sample the polynomial finely on [lo,hi] and report min sign."""
    signs = set()
    vals = []
    n = 200
    for i in range(n + 1):
        s = lo + (hi - lo) * F(i, n)
        if s <= 0 or s >= 1:
            continue
        v = ds.ev(poly_dict, s)
        signs.add(0 if v == 0 else (1 if v > 0 else -1))
        vals.append((s, v))
    return signs, vals


def main():
    for tag, path in [('cap<=1', 'sec_cap1.pkl'), ('cap<=2', 'sec_cap2.pkl')]:
        D = pickle.load(open('/home/claude/ym/' + path, 'rb'))
        S = D['sectors']
        print(f'===== {tag}: {len(S)} sectors', flush=True)

        # (i) per-sector det sign analysis
        worst = []
        for k, sec in S.items():
            G = sec['G']
            dp = ds.padd(ds.pmul(G[(0, 0)], G[(1, 1)]),
                         ds.pneg(ds.pmul(G[(0, 1)], G[(0, 1)])))
            if not dp:
                continue
            cnt, _, info = ds.roots_in_open_01(dp)
            if cnt:
                oc, dec = odd_part_roots_01(dp)
                mults = [(m, len(f) - 1) for m, f in dec]
                print(f'  sector {k}: {cnt} distinct det-roots in (0,1); '
                      f'ODD-multiplicity roots in (0,1) = {oc}; '
                      f'squarefree decomposition (mult,deg)={mults}',
                      flush=True)
                sgn, vals = bisect_sign(dp, F(1, 1000), F(999, 1000))
                print(f'      sampled signs on [0.001,0.999]: {sorted(sgn)}',
                      flush=True)
                worst.append((k, cnt, oc))
        print(f'  sectors with interior det root: {len(worst)}; '
              f'any with a SIGN CHANGE: '
              f'{[x[0] for x in worst if x[2] > 0]}', flush=True)

        # (ii) s=1 structure
        T = {(0, 0): {}, (0, 1): {}, (1, 1): {}}
        for k, sec in S.items():
            c, e0 = ds.wsec(*k)
            for nm in T:
                T[nm] = ds.padd(T[nm], ds.pshift(sec['G'][nm], c, e0))
        t00, t01, t11 = T[(0, 0)], T[(0, 1)], T[(1, 1)]
        combos = {
            'T01 - 2*T00': ds.padd(t01, ds.pshift(t00, F(-2), 0)),
            'T11 - 4*T00': ds.padd(t11, ds.pshift(t00, F(-4), 0)),
            'T11 - 2*T01': ds.padd(t11, ds.pshift(t01, F(-2), 0)),
        }
        for nm, p in combos.items():
            m, c, lo = ds.mult_at_1(p)
            print(f'  ord_(s-1) [{nm}] = {m}, leading value {c}', flush=True)
        det = ds.padd(ds.pmul(t00, t11), ds.pneg(ds.pmul(t01, t01)))
        m, c, lo = ds.mult_at_1(det)
        print(f'  ord_(s-1) detT = {m}, detT/(s-1)^{m}|_1 = {c}', flush=True)
        print(f'  T00(1)={ds.ev(t00,F(1))} T01(1)={ds.ev(t01,F(1))} '
              f'T11(1)={ds.ev(t11,F(1))}', flush=True)

    # (iii) PSD for zero-content sectors as well (cap<=2)
    import slabnet as sl
    print('===== zero-content cap<=2 sectors: H PSD too?', flush=True)
    n_zero = 0
    fails = []
    for q in itertools.product(range(3), repeat=4):
        for w in itertools.product(range(3), repeat=4):
            L0 = sl.layers(0, q, w, 3)
            L1 = sl.layers(1, q, w, 3)
            hs = [(0, t) for t in L0] + [(1, t) for t in L1]
            if not hs:
                continue
            Hm = [[sl.N(h1[0], h2[0], q, w, h1[1], h2[1]) for h2 in hs]
                  for h1 in hs]
            if all(all(x == 0 for x in r) for r in Hm):
                continue
            key = (q, w)
            D2 = pickle.load(open('/home/claude/ym/sec_cap2.pkl', 'rb')) \
                if False else None
            n_zero += 1
            ok = (is_symmetric(Hm) and ldl_psd(Hm)[0] and esym_psd(Hm)[0])
            if not ok:
                fails.append(key)
                print('  PSD FAILURE (zero/any content)', key, flush=True)
    print(f'  checked {n_zero} sectors with a nonzero H, failures={len(fails)}',
          flush=True)


if __name__ == '__main__':
    main()
