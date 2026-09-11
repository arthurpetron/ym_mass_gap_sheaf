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

"""Independent positivity certificate for detT on (0,1), diagonal-entry
positivity, and constant factorisations."""
import pickle
import sys
from fractions import Fraction as F

sys.path.insert(0, '/home/claude/ym')
sys.set_int_max_str_digits(0)

from . import detsturm as ds


def mobius_descartes(P):
    """P: ascending coefficient list.  Substitute s = 1/(1+t) and clear
    denominators: Q(t) = (1+t)^deg * P(1/(1+t)).  Roots of P in (0,1)
    <-> roots of Q in (0, inf), so 0 sign variations in Q certifies
    (Descartes) that P has NO root in (0,1)."""
    d = len(P) - 1
    # Q(t) = sum_k P[k] (1+t)^(d-k)
    Q = [F(0)] * (d + 1)
    from math import comb
    for k, c in enumerate(P):
        if not c:
            continue
        n = d - k
        for j in range(n + 1):
            Q[j] += c * comb(n, j)
    return ds.trim(Q)


def divide_t_power(Q):
    k = 0
    while k < len(Q) and Q[k] == 0:
        k += 1
    return Q[k:], k


def sign_variations(Q):
    sg = [1 if c > 0 else -1 for c in Q if c != 0]
    return sum(1 for i in range(1, len(sg)) if sg[i] != sg[i - 1])


def analyse(path, tag):
    D = pickle.load(open(path, 'rb'))
    T, det = D['T'], D['det']
    print(f'===== {tag}', flush=True)
    for nm in [(0, 0), (1, 1)]:
        p = T[nm]
        cnt, _, info = ds.roots_in_open_01(p)
        allpos = all(c > 0 for c in p.values())
        print(f'  T{nm}: all coefficients > 0 : {allpos}; '
              f'distinct roots in (0,1) = {cnt}', flush=True)
    P, lo = ds.to_list(det)
    P = ds.trim(P)
    Q = mobius_descartes(P)
    Q2, k = divide_t_power(Q)
    sv = sign_variations(Q2)
    print(f'  detT/s^{lo}: degree {len(P)-1}', flush=True)
    print(f'  Mobius s=1/(1+t): Q has t^{k} factor (== multiplicity of s=1)',
          flush=True)
    print(f'  Descartes sign variations of Q/t^{k}: {sv}'
          f'   => roots of detT in (0,1) <= {sv}', flush=True)
    print(f'  Q/t^{k} constant term (= detT/(s-1)^{k} at s=1, up to sign): '
          f'{Q2[0]}', flush=True)
    print(f'  Q/t^{k} leading coeff (= detT/s^{lo} at s=0): {Q2[-1]}',
          flush=True)
    m, c, _ = ds.mult_at_1(det)
    print(f'  multiplicity at s=1 = {m}; detT/(s-1)^{m}|_{{s=1}} = {c}',
          flush=True)

    def fac(n):
        n = abs(int(n))
        f = {}
        d = 2
        while d * d <= n:
            while n % d == 0:
                f[d] = f.get(d, 0) + 1
                n //= d
            d += 1
        if n > 1:
            f[n] = f.get(n, 0) + 1
        return f
    print(f'  factorisation of the constant: {fac(c)}', flush=True)
    return c


if __name__ == '__main__':
    c1 = analyse('/home/claude/ym/sec_cap1_polys.pkl', 'cap<=1 (16 sectors)')
    c2 = analyse('/home/claude/ym/sec_cap2_polys.pkl', 'cap<=2 (187 sectors)')
    print(f'ratio cap2/cap1 constant = {F(c2, c1)}', flush=True)
