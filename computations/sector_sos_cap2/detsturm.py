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

"""Deliverable (2a)+(3): 2x2 PSD gate per sector and exact Sturm analysis
of detT(s) = T00 T11 - T01^2 for a sector family."""
import pickle
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, '/home/claude/ym')
sys.set_int_max_str_digits(0)

from computations.exact_haar_network import casimir4, dim

# ------------------------------------------------------------------ polys
# dict form {exponent: coeff} for s-polynomials, list form ascending coeffs


def padd(p, q):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, F(0)) + c
    return {e: c for e, c in r.items() if c}


def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            k = e1 + e2
            r[k] = r.get(k, F(0)) + c1 * c2
    return {e: c for e, c in r.items() if c}


def pneg(p):
    return {e: -c for e, c in p.items()}


def pshift(p, c, e0):
    return {e + e0: v * c for e, v in p.items() if v}


def ev(p, s):
    return sum(c * s ** e for e, c in p.items())


def to_list(p):
    if not p:
        return []
    lo, hi = min(p), max(p)
    out = [F(0)] * (hi - lo + 1)
    for e, c in p.items():
        out[e - lo] = c
    return out, lo


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def pdiff(p):
    return trim([p[i] * i for i in range(1, len(p))])


def prem(a, b):
    a = trim(a)
    b = trim(b)
    while a and len(a) >= len(b):
        f = a[-1] / b[-1]
        sh = len(a) - len(b)
        for i in range(len(b)):
            a[i + sh] -= f * b[i]
        a = trim(a)
    return a


def evl(p, x):
    r = F(0)
    for c in reversed(p):
        r = r * x + c
    return r


def pgcd(a, b):
    a, b = trim(a), trim(b)
    while b:
        a, b = b, prem(list(a), b)
    if a:
        a = [c / a[-1] for c in a]
    return trim(a)


def pdivexact(a, b):
    a, b = trim(a), trim(b)
    q = [F(0)] * (len(a) - len(b) + 1)
    while a and len(a) >= len(b):
        f = a[-1] / b[-1]
        sh = len(a) - len(b)
        q[sh] = f
        for i in range(len(b)):
            a[i + sh] -= f * b[i]
        a = trim(a)
    assert not a, 'division not exact'
    return trim(q)


def sturm_chain(p):
    ch = [trim(list(p)), pdiff(p)]
    while trim(ch[-1]):
        r = prem(list(ch[-2]), ch[-1])
        if not trim(r):
            break
        ch.append([-c for c in r])
    return [c for c in ch if trim(c)]


def sign_changes(ch, x):
    sg = []
    for c in ch:
        v = evl(c, x)
        if v:
            sg.append(1 if v > 0 else -1)
    return sum(1 for i in range(1, len(sg)) if sg[i] != sg[i - 1])


def roots_in_open_01(poly_dict):
    """(#distinct roots strictly in (0,1), squarefree degree, extra info)."""
    P, lo = to_list(poly_dict)
    P = trim(P)
    if len(P) <= 1:
        return 0, 0, 'constant after factoring out s^%d' % lo
    g = pgcd(P, pdiff(P))
    Sq = P if len(g) <= 1 else pdivexact(list(P), g)
    ch = sturm_chain(Sq)
    n0 = sign_changes(ch, F(0))
    n1 = sign_changes(ch, F(1))
    at1 = (evl(Sq, F(1)) == 0)
    at0 = (evl(Sq, F(0)) == 0)
    cnt = n0 - n1 - (1 if at1 else 0)
    return cnt, len(Sq) - 1, (f'lowpow={lo} degP={len(P)-1} '
                              f'sq_deg={len(Sq)-1} sturm(0)={n0} '
                              f'sturm(1)={n1} Sq(1)==0:{at1} '
                              f'Sq(0)==0:{at0}')


def mult_at_1(poly_dict):
    P, lo = to_list(poly_dict)
    P = trim(P)
    mult = 0
    Q = list(P)
    while Q and evl(Q, F(1)) == 0:
        desc = list(reversed(Q))
        res = [desc[0]]
        for c in desc[1:]:
            res.append(c + res[-1])
        assert res[-1] == 0
        Q = trim(list(reversed(res[:-1])))
        mult += 1
    return mult, evl(Q, F(1)), lo


# ------------------------------------------------------------------ sectors


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


SVALS = [F(1, 10), F(1, 2), F(3, 5), F(4, 5), F(9, 10), F(99, 100)]


def main(path, label):
    D = pickle.load(open(path, 'rb'))
    S = D['sectors']
    print(f'=== {label}: {len(S)} sectors from {path}', flush=True)

    # ---- (2a) per-sector 2x2 gate
    print('--- (2a) per-sector 2x2 G gate', flush=True)
    bad_pt, bad_sym = [], []
    detzero = 0
    for k, sec in S.items():
        G = sec['G']
        g00, g01, g11 = G[(0, 0)], G[(0, 1)], G[(1, 1)]
        if G[(0, 1)] != G[(1, 0)]:
            bad_sym.append(('G01!=G10', k))
        for s in SVALS:
            a, b, c = ev(g00, s), ev(g11, s), ev(g01, s)
            d = a * b - c * c
            if a < 0 or b < 0 or d < 0:
                bad_pt.append((k, str(s), str(a), str(b), str(d)))
        dpoly = padd(pmul(g00, g11), pneg(pmul(g01, g01)))
        if not dpoly:
            detzero += 1
            continue
        cnt, _, info = roots_in_open_01(dpoly)
        if cnt:
            bad_sym.append(('sector det has root in (0,1)', k, cnt, info))
        # also: sign of the det polynomial's lowest coefficient
        if dpoly[min(dpoly)] < 0:
            bad_sym.append(('sector det negative near 0', k))
    print(f'  pointwise failures: {len(bad_pt)}', flush=True)
    for x in bad_pt[:10]:
        print('   ', x, flush=True)
    print(f'  symbolic failures: {len(bad_sym)}   '
          f'(sectors with det identically 0: {detzero})', flush=True)
    for x in bad_sym[:10]:
        print('   ', x, flush=True)

    # ---- (3) assembled kernel
    print('--- (3) assembled T and detT', flush=True)
    T = {(0, 0): {}, (0, 1): {}, (1, 1): {}}
    for k, sec in S.items():
        c, e0 = wsec(*k)
        for nm in T:
            T[nm] = padd(T[nm], pshift(sec['G'][nm], c, e0))
    for nm in T:
        print(f'  T{nm}: {len(T[nm])} terms, exps '
              f'[{min(T[nm])},{max(T[nm])}], T{nm}(1)='
              f'{ev(T[nm], F(1))}', flush=True)
    det = padd(pmul(T[(0, 0)], T[(1, 1)]), pneg(pmul(T[(0, 1)], T[(0, 1)])))
    lo = min(det)
    print(f'  detT: {len(det)} terms, exps [{lo},{max(det)}]', flush=True)
    print(f'  lowest coeff: s^{lo} * {det[lo]}', flush=True)
    nneg = sum(1 for c in det.values() if c < 0)
    print(f'  negative coefficients: {nneg}/{len(det)}', flush=True)
    for s in SVALS + [F(999, 1000), F(1) - F(1, 10 ** 6)]:
        v = ev(det, s)
        print(f'   detT({s}) sign: {"+" if v > 0 else ("0" if v == 0 else "-")}',
              flush=True)
    t = time.time()
    cnt, sqdeg, info = roots_in_open_01(det)
    print(f'  STURM: distinct roots strictly in (0,1) = {cnt}', flush=True)
    print(f'         {info}  ({time.time()-t:.1f}s)', flush=True)
    mult, const, lo2 = mult_at_1(det)
    print(f'  multiplicity of s=1 root = {mult}', flush=True)
    print(f'  detT(s)/(s-1)^{mult} at s=1 = {const}', flush=True)
    pickle.dump({'T': T, 'det': det},
                open(path.replace('.pkl', '_polys.pkl'), 'wb'))
    return T, det


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else 'family')
