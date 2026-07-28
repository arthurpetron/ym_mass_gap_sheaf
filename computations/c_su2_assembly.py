"""MD.3 — the c_SU2 assembly: insertion moments, BCH cubic moments,
finite-basis cumulants, and the U(1) mirror gate (work_plan §16e queue
(a)-(d)).

**What this module is.**  The second (decisive) stage of the c_SU2
moment computation: an exact tilted-moment engine for the flat-limit
Gaussian network of the slab, correct THROUGH ORDER tau^2 including
the operator-ordering terms that §16e deferred — they enter at
exactly the order the marginal-defect coefficient lives at, so here
they are computed, not deferred.  Everything is exact rational
arithmetic (Fractions; complex rationals for traces); mpmath appears
only in the numeric BCH gate; no floats on the critical path.

**The object.**  Per su(2) triple, the slab pair moment in the flat
limit is

    T[n,m] = Z(tau) * e^{F tau} * tr_{V_n (x) V_m} E[ e^{iL} *
             exp( q  -  V_3  -  V_4 ) ],
    L   = theta_t . J_1 + theta_b . J_2      (loop tilts; single free
                                              links, adapted gauge),
    q   = sum_f |theta_f|^2/24 - sum_e |X_e|^2/12  + quartics
          (the phi/sin phi heat-kernel Jacobians and the (sin u/u)^2
           link Haar densities),
    V_3 = sum_f theta_f^(1) . Delta_f^(2) / (8 tau),
    V_4 = sum_f [ |Delta_f^(2)|^2 + 2 theta_f^(1) . Delta_f^(3) ]
          / (16 tau),

with theta_f^(1) = (B X)_f the abelianized face angle and
Delta^(2), Delta^(3) the quadratic/cubic BCH corrections of the
face-ordered link product (su(2) vector calculus: the commutator is
the cross product).  The Gaussian has per-component covariance
8 tau G^{-1}, G = B^T B — the §16e dictionary, unchanged.

**Order bookkeeping (complete at the stated accuracy).**  With
X ~ tau^{1/2}, every Gaussian moment carries one exact power of tau.
The (n,m)-DEPENDENT part of the series

    S(n,m) = 1 + tau s_1(n,m) + tau^2 s_2(n,m) + O(tau^3)

is EXACT through tau^2 from the term list

    s_1: -E[L^2]/2 + { E[q_2] - E[V_4] + E[V_3^2]/2 + F },
    s_2: E[L^4]/24 - E[L^2 q_2]/2 + E[L^2 V_4]/2
         - E[L^2 V_3^2]/4 + Im E[L^3 V_3]-term,

because every discarded monomial either carries no J factor (pure
normalization — cancels in every log-difference at this order), has
an odd J count (trace zero), or is O(tau^3).  E[V_3 L] = 0 exactly
(epsilon-delta parity), pinned by the engine.

**Gates (exact identities, run by main and the test suite).**
  g1  semigroup chains: K*K = K and K*K*K = K force the ENTIRE tau^2
      connected coefficient of log(T[n]/T[0]) to vanish on the 2- and
      3-link chain networks — one exact identity exercising the
      Jacobian insertions, V_3, V_4, the L^4 orderings, and the
      normalization together.  Any sign or factor error anywhere
      breaks it.
  g2  single-face network: the same identity on the 1-link geometry
      (orderings + Jacobian conspiracy, no BCH).
  g3  BCH series: the derived Delta^(2)/Delta^(3) coefficients are
      checked against high-precision mpmath 2x2 matrix logs.
  g4  U(1) mirror: the identical engine at one abelian component
      (epsilon = 0, no Jacobians, no BCH) must return the EXACT
      exponential — kappa_2 = 0, i.e. c_dyn^{U(1)} = 0 — and the
      identical finite-basis flow assembly must reproduce the banked
      c_1 = -gamma^2 Var_N(m)/2 = -4 at N = 2.
  g5  structure: s_1-dependence exactly -3(C(n)+C(m)); assembled
      series exactly real; kappa_2 an exact polynomial in
      (C(n), C(m)) on the grid, verified on held-out points.

Run:  python -m computations.c_su2_assembly
"""

from __future__ import annotations

import itertools
import json
import os
import sys
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "c_su2_assembly_results.json")

sys.set_int_max_str_digits(0)


# ---------------------------------------------------------------------------
# Small exact linear algebra.
# ---------------------------------------------------------------------------


def mat_T(A):
    return [list(r) for r in zip(*A)]


def mat_mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def mat_inv(A):
    n = len(A)
    M = [[Frac(A[i][j]) for j in range(n)]
         + [Frac(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        inv = 1 / M[col][col]
        M[col] = [x * inv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [row[n:] for row in M]


def _perm_sign(perm: List[int]) -> int:
    s = 1
    p = list(perm)
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


def _eps(a, b, c) -> int:
    if (a, b, c) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
        return 1
    if (a, b, c) in ((0, 2, 1), (2, 1, 0), (1, 0, 2)):
        return -1
    return 0


# ---------------------------------------------------------------------------
# BCH to cubic order, pure Python.
#
# Vectors are symbolic: a "poly-vector" is a list of 3 polynomials;
# a polynomial maps a sorted tuple of (factor, component) variables to
# a Fraction.  Cross product implements the su(2) commutator
# ([x., y.] <-> x cross y under g = exp(-(i/2) v.sigma)).
# ---------------------------------------------------------------------------


def _p_add(p, q, c=Frac(1)):
    for k, v in q.items():
        p[k] = p.get(k, Frac(0)) + c * v
        if p[k] == 0:
            del p[k]
    return p


def _p_mul(p, q):
    out: Dict = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = tuple(sorted(k1 + k2))
            out[k] = out.get(k, Frac(0)) + v1 * v2
            if out[k] == 0:
                del out[k]
    return out


def _v_zero():
    return [{}, {}, {}]


def _v_add(u, v, c=Frac(1)):
    for a in range(3):
        _p_add(u[a], v[a], c)
    return u


def _v_cross(u, v):
    out = _v_zero()
    for a in range(3):
        b, c = (a + 1) % 3, (a + 2) % 3
        _p_add(out[a], _p_mul(u[b], v[c]), Frac(1))
        _p_add(out[a], _p_mul(u[c], v[b]), Frac(-1))
    return out


def _v_dot(u, v):
    out: Dict = {}
    for a in range(3):
        _p_add(out, _p_mul(u[a], v[a]))
    return out


def _v_scale_deg(v, deg):
    """Keep only monomials of total degree deg."""
    out = _v_zero()
    for a in range(3):
        for k, c in v[a].items():
            if len(k) == deg:
                out[a][k] = c
    return out


def _base_vec(i):
    v = _v_zero()
    for a in range(3):
        v[a][((i, a),)] = Frac(1)
    return v


_BCH_CACHE: Dict[int, Tuple[list, list]] = {}


def bch_parts(k: int):
    """(Delta2, Delta3) poly-vectors for log(e^{Y_0} ... e^{Y_{k-1}}),
    grades 2 and 3, via the exact graded recursion

      BCH(A, B) = (A1+B1) + (A2 + [A1,B1]/2)
                  + (A3 + [A2,B1]/2 + [A1,[A1,B1]]/12 + [B1,[B1,A1]]/12)

    with B a pure grade-1 element (the next factor)."""
    if k in _BCH_CACHE:
        return _BCH_CACHE[k]
    A1 = _base_vec(0)
    A2 = _v_zero()
    A3 = _v_zero()
    for i in range(1, k):
        B1 = _base_vec(i)
        n1 = _v_add(_v_zero(), A1)
        _v_add(n1, B1)
        n2 = _v_add(_v_zero(), A2)
        _v_add(n2, _v_cross(A1, B1), Frac(1, 2))
        n3 = _v_add(_v_zero(), A3)
        _v_add(n3, _v_cross(A2, B1), Frac(1, 2))
        _v_add(n3, _v_cross(A1, _v_cross(A1, B1)), Frac(1, 12))
        _v_add(n3, _v_cross(B1, _v_cross(B1, A1)), Frac(1, 12))
        A1, A2, A3 = n1, n2, n3
    out = (_v_scale_deg(A2, 2), _v_scale_deg(A3, 3))
    _BCH_CACHE[k] = out
    return out


def bch_gate(digits: int = 30) -> bool:
    """mpmath: series log vs exact matrix log on random rationals."""
    import mpmath as mp
    import random

    mp.mp.dps = digits + 20
    rnd = random.Random(20260728)
    ok = True
    for k in (2, 3, 4):
        d2, d3 = bch_parts(k)
        for _trial in range(3):
            t = mp.mpf(1) / 10 ** 4
            vs = [[t * rnd.randint(-9, 9) for _ in range(3)]
                  for _ in range(k)]

            def amat(v):
                return mp.matrix(
                    [[-0.5j * v[2], -0.5j * (v[0] - 1j * v[1])],
                     [-0.5j * (v[0] + 1j * v[1]), 0.5j * v[2]]])

            P = mp.eye(2)
            for v in vs:
                P = P * mp.expm(amat(v))
            Z = mp.logm(P)
            # Z = -(i/2) z.sigma  =>  z_a = i tr(Z sigma_a)
            zx = 1j * (Z[0, 1] + Z[1, 0])
            zy = 1j * (1j * Z[0, 1] - 1j * Z[1, 0])
            zz = 1j * (Z[0, 0] - Z[1, 1])
            z_exact = [zx, zy, zz]

            def ev(poly):
                tot = mp.mpf(0)
                for mono, c in poly.items():
                    p = mp.mpf(c.numerator) / c.denominator
                    for (i, a) in mono:
                        p = p * vs[i][a]
                    tot += p
                return tot

            z_ser = [sum(v[a] for v in vs) + ev(d2[a]) + ev(d3[a])
                     for a in range(3)]
            err = max(abs(z_exact[a] - z_ser[a]) for a in range(3))
            budget = (mp.mpf(40) * k * t) ** 4
            ok &= bool(err < budget)
    return ok


# ---------------------------------------------------------------------------
# Trace cache: tr(J^{a1}...J^{ak}) on spin j = n/2, k <= 4, exact
# complex rationals.  Integer-similarity basis: J+ has unit entries,
# J- has integer entries, Jz half-integers — traces are basis-free.
# ---------------------------------------------------------------------------


class CMat:
    """Dense complex-rational matrix: entries (re, im) Fractions."""

    def __init__(self, d, entries=None):
        self.d = d
        self.e = entries if entries is not None else \
            [[(Frac(0), Frac(0))] * d for _ in range(d)]

    @staticmethod
    def eye(d):
        m = CMat(d)
        for i in range(d):
            m.e[i][i] = (Frac(1), Frac(0))
        return m

    def mul(self, o):
        d = self.d
        out = CMat(d)
        for i in range(d):
            row = self.e[i]
            orow = out.e[i]
            for k in range(d):
                ar, ai = row[k]
                if ar == 0 and ai == 0:
                    continue
                brow = o.e[k]
                for j in range(d):
                    br, bi = brow[j]
                    if br == 0 and bi == 0:
                        continue
                    cr, ci = orow[j]
                    orow[j] = (cr + ar * br - ai * bi,
                               ci + ar * bi + ai * br)
        return out

    def trace(self):
        r = sum((self.e[i][i][0] for i in range(self.d)), Frac(0))
        im = sum((self.e[i][i][1] for i in range(self.d)), Frac(0))
        return (r, im)


_JMATS: Dict[int, List[CMat]] = {}


def _spin_mats(n: int) -> List[CMat]:
    if n in _JMATS:
        return _JMATS[n]
    d = n + 1
    j = Frac(n, 2)
    ms = [j - i for i in range(d)]
    Jz = CMat(d)
    for i, m in enumerate(ms):
        Jz.e[i][i] = (m, Frac(0))
    # integer-similarity: J+ unit superdiagonal, J- integer subdiag.
    Jp = CMat(d)
    Jm = CMat(d)
    for i in range(1, d):
        m = ms[i]           # J+ |m> -> |m+1> (row i-1, col i)
        Jp.e[i - 1][i] = (Frac(1), Frac(0))
        # J- J+ |m> = (j-m)(j+m+1) |m>  => J- entry (i, i-1)
        Jm.e[i][i - 1] = ((j - ms[i - 1] + 1) * (j + ms[i - 1]), Frac(0))
    # Jx = (J+ + J-)/2 ; Jy = (J+ - J-)/(2i) = -(i/2)(J+ - J-)
    Jx = CMat(d)
    Jy = CMat(d)
    for i in range(d):
        for k in range(d):
            pr, _ = Jp.e[i][k]
            mr, _ = Jm.e[i][k]
            Jx.e[i][k] = ((pr + mr) / 2, Frac(0))
            Jy.e[i][k] = (Frac(0), -(pr - mr) / 2)
    out = [Jx, Jy, Jz]
    _JMATS[n] = out
    return out


_TR_CACHE: Dict[Tuple[int, Tuple[int, ...]], Tuple[Frac, Frac]] = {}


def trace_word(n: int, word: Tuple[int, ...]) -> Tuple[Frac, Frac]:
    if not word:
        return (Frac(n + 1), Frac(0))
    key = (n, word)
    if key in _TR_CACHE:
        return _TR_CACHE[key]
    Js = _spin_mats(n)
    M = Js[word[0]]
    for a in word[1:]:
        M = M.mul(Js[a])
    out = M.trace()
    _TR_CACHE[key] = out
    return out


def _trace_cache_gate() -> bool:
    """tr(J^a J^b) = delta d C2/3;  tr(J^aJ^bJ^c) = (i/2) eps d C2/3."""
    ok = True
    for n in (1, 2, 3):
        d = n + 1
        c2 = Frac(n * (n + 2), 4)
        for a in range(3):
            for b in range(3):
                r, i = trace_word(n, (a, b))
                ok &= (i == 0 and r == (d * c2 / 3 if a == b else 0))
                for c in range(3):
                    r3, i3 = trace_word(n, (a, b, c))
                    want_i = Frac(_eps(a, b, c)) * d * c2 / 6
                    want_r = Frac(0)
                    ok &= (r3 == want_r and i3 == want_i)
    return ok


# ---------------------------------------------------------------------------
# Geometry.
# ---------------------------------------------------------------------------


class Net:
    def __init__(self, nl: int, faces: List[List[Tuple[int, int]]],
                 loop_t: Tuple[int, int],
                 loop_b: Optional[Tuple[int, int]] = None):
        self.nl = nl
        self.faces = faces
        self.loop_t = loop_t
        self.loop_b = loop_b
        B = [[0] * nl for _ in faces]
        for fi, path in enumerate(faces):
            for e, s in path:
                B[fi][e] += s
        self.B = B
        self.G = mat_mul(mat_T(B), B)
        self.Ginv = mat_inv(self.G)

    def cov(self, e: int, f: int) -> Frac:
        return self.Ginv[e][f]


def slab_net() -> Net:
    from computations.dp6_u1_slab_blocking import (
        _W_TOP_LOOP, _W_BOT_LOOP, _FREE,
    )
    from computations.slab_blocking_kernel import _FACES

    pos = {e: i for i, e in enumerate(_FREE)}
    faces = []
    for path in _FACES:
        faces.append([(pos[e], o) for e, o in path if e in pos])

    def loop_of(w):
        nz = [(pos[e], w[e]) for e in _FREE if w[e]]
        assert len(nz) == 1 and abs(nz[0][1]) == 1
        return nz[0]

    return Net(len(_FREE), faces, loop_of(_W_TOP_LOOP),
               loop_of(_W_BOT_LOOP))


def chain_net(k: int) -> Net:
    faces = [[(i, 1), (i + 1, -1)] for i in range(k - 1)]
    faces.append([(k - 1, 1)])
    return Net(k, faces, (0, 1), None)


# ---------------------------------------------------------------------------
# The engine.  Word tables: {(w1, w2): [re, im]} per net tau power.
# ---------------------------------------------------------------------------


WordTab = Dict[Tuple[Tuple[int, ...], Tuple[int, ...]], List[Frac]]


def _tab_add(tab: WordTab, key, re=Frac(0), im=Frac(0)):
    if re == 0 and im == 0:
        return
    if key not in tab:
        tab[key] = [Frac(0), Frac(0)]
    tab[key][0] += re
    tab[key][1] += im


def _pairings(slots):
    if not slots:
        yield []
        return
    a = slots[0]
    rest = slots[1:]
    for i, b in enumerate(rest):
        for sub in _pairings(rest[:i] + rest[i + 1:]):
            yield [(a, b)] + sub


# precomputed epsilon-contraction scalars for E[det . det . L^2],
# case "both tilts into det slots": key (pos1, pos2, pairing-key)
# -> Fraction w with the component tensor equal to w * delta_{c1 c2}.
_DDL_PATTERNS: Optional[List[Tuple[int, int, int, Tuple, Frac]]] = None


def _ddl_patterns():
    """Enumerate: pos1, pos2 in the six det slots (3 of det A, 3 of
    det B), pos1 != pos2; pairing of the remaining four slots; the
    component sum  sum_{assign} eps_A eps_B  with slots pos1, pos2
    held at components c1, c2 — an invariant rank-2 tensor, so equal
    to w * delta.  Returns a list of (slotA_or_B flags...) tuples:
    (p1, p2, pairing, w) with p1, p2 in 0..5 (0-2 det A, 3-5 det B)
    and pairing a tuple of index pairs into the remaining slot list."""
    global _DDL_PATTERNS
    if _DDL_PATTERNS is not None:
        return _DDL_PATTERNS
    out = []
    slots = list(range(6))
    for p1 in slots:
        for p2 in slots:
            if p1 == p2:
                continue
            rem = [s for s in slots if s not in (p1, p2)]
            for pairing in _pairings(list(range(4))):
                # component tensor
                W = [[0] * 3 for _ in range(3)]
                for c1 in range(3):
                    for c2 in range(3):
                        tot = 0
                        for assign in itertools.product(range(3),
                                                        repeat=2):
                            comp = {}
                            comp[p1] = c1
                            comp[p2] = c2
                            for (u, v), cc in zip(pairing, assign):
                                comp[rem[u]] = cc
                                comp[rem[v]] = cc
                            ea = _eps(comp[0], comp[1], comp[2])
                            if not ea:
                                continue
                            eb = _eps(comp[3], comp[4], comp[5])
                            if not eb:
                                continue
                            tot += ea * eb
                        W[c1][c2] = tot
                # must be w * delta
                w = Frac(W[0][0])
                iso = all(
                    W[a][b] == (w if a == b else 0)
                    for a in range(3) for b in range(3))
                assert iso, "det-det L2 tensor not isotropic"
                if w:
                    out.append((p1, p2, tuple(tuple(p) for p in pairing),
                                w))
    _DDL_PATTERNS = out
    return out


class Engine:
    def __init__(self, net: Net, components: int = 3):
        self.net = net
        self.comp = components
        self.q2_terms = self._build_q2() if components == 3 else []
        self.v3_terms = self._build_v3() if components == 3 else {}
        self.v4_terms = self._build_v4() if components == 3 else []
        self.lslots = [(net.loop_t[0], 0, net.loop_t[1])]
        if net.loop_b is not None:
            self.lslots.append((net.loop_b[0], 1, net.loop_b[1]))

    # -- insertions ----------------------------------------------------------

    def _build_q2(self):
        out: Dict[Tuple[int, int], Frac] = {}
        for row in self.net.B:
            nz = [(e, c) for e, c in enumerate(row) if c]
            for (e, ce) in nz:
                for (f, cf) in nz:
                    if e <= f:
                        key = (e, f)
                        mult = Frac(ce * cf, 24) * (1 if e == f else 2)
                        out[key] = out.get(key, Frac(0)) + mult
        for e in range(self.net.nl):
            out[(e, e)] = out.get((e, e), Frac(0)) - Frac(1, 12)
        return [(c, e, f) for (e, f), c in out.items() if c]

    def _build_v3(self):
        out: Dict[Tuple[int, int, int], Frac] = {}
        for path in self.net.faces:
            ys = [(e, Frac(s)) for e, s in path]
            row: Dict[int, Frac] = {}
            for e, s in path:
                row[e] = row.get(e, Frac(0)) + s
            for (pi, qi) in itertools.combinations(range(len(ys)), 2):
                p, sp_ = ys[pi]
                q, sq = ys[qi]
                for e, ce in row.items():
                    if e in (p, q):
                        continue
                    coef = Frac(1, 2) * sp_ * sq * ce * Frac(1, 8)
                    if not coef:
                        continue
                    tri = sorted([(e, 0), (p, 1), (q, 2)])
                    sign = _perm_sign([t[1] for t in tri])
                    key = tuple(t[0] for t in tri)
                    if key[0] == key[1] or key[1] == key[2]:
                        continue
                    out[key] = out.get(key, Frac(0)) + sign * coef
        return {k: c for k, c in out.items() if c}

    def _build_v4(self):
        acc: Dict[Tuple[int, int, int, int], Frac] = {}

        def add(c, e, f, g, h):
            d1 = tuple(sorted((e, f)))
            d2 = tuple(sorted((g, h)))
            key = min(d1 + d2, d2 + d1)
            acc[key] = acc.get(key, Frac(0)) + c

        for path in self.net.faces:
            ys = [(e, Frac(s)) for e, s in path]
            k = len(ys)
            row: Dict[int, Frac] = {}
            for e, s in path:
                row[e] = row.get(e, Frac(0)) + s
            pairs = list(itertools.combinations(range(k), 2))
            for (pi, qi) in pairs:
                for (ri, si) in pairs:
                    p, sp_ = ys[pi]
                    q, sq = ys[qi]
                    r, sr = ys[ri]
                    s2, ss = ys[si]
                    c0 = Frac(1, 4) * sp_ * sq * sr * ss * Frac(1, 16)
                    add(c0, p, r, q, s2)
                    add(-c0, p, s2, q, r)
            if k >= 2:
                _d2, d3 = bch_parts(k)
                # 2 theta . Delta3 / 16: theta = sum_e row_e X_e
                # d3 components are polys in (factor, comp) vars of
                # the ORIENTED path vectors Y_i = s_i X_{e_i}.
                # theta . Delta3 = sum_a theta_a d3_a: expand into
                # dot-monomials via explicit component polynomial:
                # each cubic monomial of d3_a has vars
                # ((i1,a1),(i2,a2),(i3,a3)); multiplied by theta_a =
                # sum_e row_e X_e^a.  The result is an O(3)-invariant
                # quartic; convert monomial-wise into dot structure:
                # a monomial X_w^a X_x^b X_y^c X_z^d with the index
                # pattern coming from eps-eps products is NOT
                # individually a dot term — so instead contract the
                # FULL tensor: build T[e1,e2,e3][a,b,c] coefficients
                # and pair with theta_a; then decompose over the three
                # dot pairings by solving the 3-parameter system per
                # link 4-tuple.
                # Practical route: accumulate the full component
                # tensor per unordered link 4-tuple, then decompose.
                tens: Dict[Tuple[int, int, int, int],
                           Dict[Tuple[int, int, int, int], Frac]] = {}
                for a in range(3):
                    for mono, c in d3[a].items():
                        (i1, a1), (i2, a2), (i3, a3) = mono
                        c_full = c * ys[i1][1] * ys[i2][1] * ys[i3][1]
                        for e, ce in row.items():
                            # full quartic monomial as 4 (link, comp)
                            # factors, symmetrized over ALL slots so
                            # each per-link-tuple tensor is the
                            # canonical (invariant) symmetric tensor
                            fac = ((e, a), (ys[i1][0], a1),
                                   (ys[i2][0], a2), (ys[i3][0], a3))
                            perms = sorted(set(
                                itertools.permutations(fac)))
                            cc = 2 * c_full * ce * Frac(1, 16) \
                                / len(perms)
                            for pm in perms:
                                links = tuple(l for l, _a in pm)
                                comps = tuple(_a for _l, _a in pm)
                                tens.setdefault(links, {})
                                tens[links][comps] = tens[links].get(
                                    comps, Frac(0)) + cc
                for links, tmap in tens.items():
                    # decompose T_{abcd} = x d_ab d_cd + y d_ac d_bd
                    #                     + z d_ad d_bc  (exact).
                    x = tmap.get((0, 0, 1, 1), Frac(0))
                    y = tmap.get((0, 1, 0, 1), Frac(0))
                    z = tmap.get((0, 1, 1, 0), Frac(0))
                    diag = tmap.get((0, 0, 0, 0), Frac(0))
                    assert diag == x + y + z, "V4 tensor not pure dots"
                    # full verification of the decomposition
                    for comps in itertools.product(range(3), repeat=4):
                        a_, b_, c_, d_ = comps
                        want = (x * (a_ == b_) * (c_ == d_)
                                + y * (a_ == c_) * (b_ == d_)
                                + z * (a_ == d_) * (b_ == c_))
                        got = tmap.get(comps, Frac(0))
                        assert got == want, "V4 tensor decomposition"
                    e1, e2, e3, e4 = links
                    if x:
                        add(x, e1, e2, e3, e4)
                    if y:
                        add(y, e1, e3, e2, e4)
                    if z:
                        add(z, e1, e4, e2, e3)
        return [(c, k[0], k[1], k[2], k[3]) for k, c in acc.items() if c]

    # -- dot-monomial Wick ---------------------------------------------------

    def _wick_dots(self, dots, lword, base, net_pow,
                   target: Dict[int, WordTab]):
        net = self.net
        D = len(dots)
        links = []
        for e, f in dots:
            links += [e, f]
        for j in lword:
            links.append(self.lslots[j][0])
        nslots = len(links)
        if nslots % 2:
            return
        base_pairs = [(2 * k, 2 * k + 1) for k in range(D)]
        sgn_l = Frac(1)
        for j in lword:
            sgn_l *= self.lslots[j][2]
        tab = target.setdefault(net_pow, {})
        for pairing in _pairings(list(range(nslots))):
            covp = base * sgn_l
            for a, b in pairing:
                covp *= net.cov(links[a], links[b])
                if covp == 0:
                    break
            if covp == 0:
                continue
            idx = list(range(nslots))

            def find(i):
                while idx[i] != i:
                    idx[i] = idx[idx[i]]
                    i = idx[i]
                return i

            for a, b in base_pairs + pairing:
                ra, rb = find(a), find(b)
                if ra != rb:
                    idx[rb] = ra
            lclasses = [find(2 * D + jpos) for jpos in range(len(lword))]
            all_roots = {find(s) for s in range(nslots)}
            lroots = sorted(set(lclasses))
            n_free = len(all_roots) - len(lroots)
            mult = Frac(self.comp) ** n_free
            if not lroots:
                _tab_add(tab, ((), ()), covp * mult)
                continue
            for assign in itertools.product(range(self.comp),
                                            repeat=len(lroots)):
                amap = dict(zip(lroots, assign))
                w1, w2 = [], []
                for jpos, j in enumerate(lword):
                    fam = self.lslots[j][1]
                    (w1 if fam == 0 else w2).append(amap[lclasses[jpos]])
                _tab_add(tab, (tuple(w1), tuple(w2)), covp * mult)

    def _lwords(self, k):
        return list(itertools.product(range(len(self.lslots)), repeat=k))

    # -- det blocks ----------------------------------------------------------

    def _det_det(self, tri1, c1, tri2, c2, net_pow,
                 target: Dict[int, WordTab]):
        """E[det(tri1) det(tri2)] = 6 det(C),  C_ij = cov(a_i, b_j)."""
        net = self.net
        a, b = list(tri1), list(tri2)
        tot = Frac(0)
        for perm in itertools.permutations(range(3)):
            s = _perm_sign(list(perm))
            p = Frac(1)
            for i in range(3):
                p *= net.cov(a[i], b[perm[i]])
                if p == 0:
                    break
            tot += s * p
        val = 6 * tot * c1 * c2
        if val:
            _tab_add(target.setdefault(net_pow, {}), ((), ()), val)

    def _det_det_l2(self, tri1, c1, tri2, c2, lword, net_pow,
                    target: Dict[int, WordTab]):
        net = self.net
        a, b = list(tri1), list(tri2)
        j1, j2 = lword
        l1, fam1, s1 = self.lslots[j1]
        l2, fam2, s2 = self.lslots[j2]
        base = c1 * c2 * s1 * s2
        tab = target.setdefault(net_pow, {})

        def emit(coef, comp1, comp2):
            if not coef:
                return
            w1, w2 = [], []
            for fam, c in ((fam1, comp1), (fam2, comp2)):
                (w1 if fam == 0 else w2).append(c)
            _tab_add(tab, (tuple(w1), tuple(w2)), coef)

        # case A: tilts pair together
        totA = Frac(0)
        for perm in itertools.permutations(range(3)):
            s = _perm_sign(list(perm))
            p = Frac(1)
            for i in range(3):
                p *= net.cov(a[i], b[perm[i]])
                if p == 0:
                    break
            totA += s * p
        cA = 6 * totA * base * net.cov(l1, l2)
        if cA:
            for c in range(3):
                emit(cA, c, c)
        # case B: both tilts into det slots (precomputed patterns)
        link_of = a + b
        for (p1, p2, pairing, w) in _ddl_patterns():
            cB = net.cov(l1, link_of[p1]) * net.cov(l2, link_of[p2])
            if not cB:
                continue
            rem = [s for s in range(6) if s not in (p1, p2)]
            cP = Frac(1)
            for (u, v) in pairing:
                cP *= net.cov(link_of[rem[u]], link_of[rem[v]])
                if cP == 0:
                    break
            if not cP:
                continue
            coef = base * cB * cP * w
            for c in range(3):
                emit(coef, c, c)

    def _det_l3(self, tri, c0, lword, net_pow, target: Dict[int, WordTab]):
        net = self.net
        a = list(tri)
        links_l = [self.lslots[j][0] for j in lword]
        sgn = Frac(1)
        for j in lword:
            sgn *= self.lslots[j][2]
        tab = target.setdefault(net_pow, {})
        for perm in itertools.permutations(range(3)):
            cB = c0 * sgn
            for t in range(3):
                cB *= net.cov(links_l[t], a[perm[t]])
                if cB == 0:
                    break
            if not cB:
                continue
            for comps in itertools.product(range(3), repeat=3):
                det_c = [None, None, None]
                for t in range(3):
                    det_c[perm[t]] = comps[t]
                e = _eps(det_c[0], det_c[1], det_c[2])
                if not e:
                    continue
                w1, w2 = [], []
                for t, j in enumerate(lword):
                    fam = self.lslots[j][1]
                    (w1 if fam == 0 else w2).append(comps[t])
                _tab_add(tab, (tuple(w1), tuple(w2)), cB * e)

    def _det_l1(self, tri, c0, lword, target: Dict[int, WordTab]):
        """E[det x L]: exact zero by parity — computed honestly."""
        net = self.net
        a = list(tri)
        l1, fam, s1 = self.lslots[lword[0]]
        tab = target.setdefault(1, {})
        for i in range(3):
            cB = net.cov(l1, a[i]) * c0 * s1
            if not cB:
                continue
            rem = [x for x in range(3) if x != i]
            cP = net.cov(a[rem[0]], a[rem[1]])
            if not cP:
                continue
            for ci in range(3):
                tot = 0
                for cc in range(3):
                    det_c = [None] * 3
                    det_c[i] = ci
                    det_c[rem[0]] = cc
                    det_c[rem[1]] = cc
                    tot += _eps(det_c[0], det_c[1], det_c[2])
                if tot:
                    w1, w2 = ([ci], []) if fam == 0 else ([], [ci])
                    _tab_add(tab, (tuple(w1), tuple(w2)),
                             cB * cP * tot)

    # -- build all tables ----------------------------------------------------

    def build_tables(self, progress: bool = False):
        T: Dict[str, Dict[int, WordTab]] = {}

        def tgt(name):
            return T.setdefault(name, {})

        for k in (2, 4):
            for lword in self._lwords(k):
                self._wick_dots([], lword, Frac(1), k // 2, tgt(f"L{k}"))
        for c, e, f in self.q2_terms:
            self._wick_dots([(e, f)], (), c, 1, tgt("q2"))
            for lword in self._lwords(2):
                self._wick_dots([(e, f)], lword, c, 2, tgt("q2L2"))
        for c, e, f, g, h in self.v4_terms:
            self._wick_dots([(e, f), (g, h)], (), c, 1, tgt("V4"))
            for lword in self._lwords(2):
                self._wick_dots([(e, f), (g, h)], lword, c, 2,
                                tgt("V4L2"))
        v3 = list(self.v3_terms.items())
        n3 = len(v3)
        for i1 in range(n3):
            t1, c1 = v3[i1]
            for i2 in range(n3):
                t2, c2 = v3[i2]
                self._det_det(t1, c1, t2, c2, 1, tgt("V3V3"))
                for lword in self._lwords(2):
                    self._det_det_l2(t1, c1, t2, c2, lword, 2,
                                     tgt("V3V3L2"))
            if progress and (i1 + 1) % 25 == 0:
                print(f"    ...V3^2 row {i1 + 1}/{n3}", flush=True)
        for tri, c0 in v3:
            for lword in self._lwords(3):
                self._det_l3(tri, c0, lword, 2, tgt("V3L3"))
            for lword in self._lwords(1):
                self._det_l1(tri, c0, lword, tgt("V3L1"))
        return T


# ---------------------------------------------------------------------------
# Assembled series per network.
# ---------------------------------------------------------------------------


class Series:
    def __init__(self, net: Net, components: int = 3,
                 unit: Frac = Frac(8), progress: bool = False):
        self.net = net
        self.comp = components
        self.unit = unit
        self.eng = Engine(net, components)
        self.tabs = self.eng.build_tables(progress=progress)
        for tp, tab in self.tabs.get("V3L1", {}).items():
            for k, (re, im) in tab.items():
                assert re == 0 and im == 0, "E[V3 L] != 0 — parity"

    def _ev(self, name, net_pow, rminus, n, m) -> Tuple[Frac, Frac]:
        tab = self.tabs.get(name, {}).get(net_pow)
        if not tab:
            return Frac(0), Frac(0)
        dnorm = Frac((n + 1) * ((m + 1) if m is not None else 1))
        re_tot, im_tot = Frac(0), Frac(0)
        for (w1, w2), (cre, cim) in tab.items():
            r1, i1 = trace_word(n, w1)
            if m is None:
                if w2:
                    continue
                r2, i2 = Frac(1), Frac(0)
            else:
                r2, i2 = trace_word(m, w2)
            rr = r1 * r2 - i1 * i2
            ii = r1 * i2 + i1 * r2
            re_tot += cre * rr - cim * ii
            im_tot += cre * ii + cim * rr
        scale = self.unit ** (net_pow + rminus)
        return re_tot * scale / dnorm, im_tot * scale / dnorm

    def s12(self, n: int, m: Optional[int]) -> Tuple[Frac, Frac]:
        ev = self._ev
        L2 = ev("L2", 1, 0, n, m)
        L4 = ev("L4", 2, 0, n, m)
        q2 = ev("q2", 1, 0, n, m)
        q2L2 = ev("q2L2", 2, 0, n, m)
        V4 = ev("V4", 1, 1, n, m)
        V4L2 = ev("V4L2", 2, 1, n, m)
        V3V3 = ev("V3V3", 1, 2, n, m)
        V3V3L2 = ev("V3V3L2", 2, 2, n, m)
        V3L3 = ev("V3L3", 2, 1, n, m)
        for nm, val in (("L2", L2), ("L4", L4), ("q2", q2),
                        ("q2L2", q2L2), ("V4", V4), ("V4L2", V4L2),
                        ("V3V3", V3V3), ("V3V3L2", V3V3L2)):
            assert val[1] == 0, f"imaginary part in {nm}"
        # NOTE: the e^{F tau} face normalization is MULTIPLICATIVE —
        # it contributes exactly F tau to log T and nothing to
        # kappa_2, so it is EXCLUDED from the series (it cancels in
        # every ratio observable).  The n-independent tau-linear
        # means E[q2], E[V4], E[V3^2] are INSIDE the expectation and
        # do couple into kappa_2 through s1^2/2 — they stay.
        s1 = -L2[0] / 2 + q2[0] - V4[0] + V3V3[0] / 2
        # e^{iL} exp(q - V3 - V4):
        #   tau^2, J-carrying:  (i^2/2) L^2 (q2 + V4-sign...) etc.
        #   (i^4/24) L^4  ->  + L4/24
        #   (i^2/2) L^2 q2  ->  - q2L2/2
        #   (i^2/2) L^2 (-V4)  ->  + V4L2/2
        #   (i^2/2) L^2 (V3^2/2)  ->  - V3V3L2/4
        #   (i^3/6) L^3 (-V3) = (i/6) E[L^3 V3]:
        #       E[L^3 V3] = V3L3re + i V3L3im  =>  real part
        #       contribution  - V3L3im/6,  imaginary + V3L3re/6.
        s2 = (L4[0] / 24 - q2L2[0] / 2 + V4L2[0] / 2 - V3V3L2[0] / 4
              - V3L3[1] / 6)
        im_res = (L4[1] / 24 - q2L2[1] / 2 + V4L2[1] / 2
                  - V3V3L2[1] / 4 + V3L3[0] / 6)
        assert im_res == 0, "imaginary residue in s2"
        return s1, s2


# ---------------------------------------------------------------------------
# U(1) mirror.
# ---------------------------------------------------------------------------


class SeriesU1:
    """One abelian component on the same geometry: no Jacobians, no
    BCH, integer tilt charges; covariance 2 tau G^{-1}."""

    def __init__(self, net: Net):
        self.net = net
        self.eng = Engine(net, components=1)
        self.tabs = self.eng.build_tables()

    def s12_closed(self, n: int, m: int) -> Tuple[Frac, Frac]:
        net = self.net
        u = Frac(2)
        lt, lb = net.loop_t, net.loop_b
        q = Frac(n * n) * net.cov(lt[0], lt[0])
        if lb is not None:
            q += Frac(m * m) * net.cov(lb[0], lb[0])
            q += 2 * n * m * lt[1] * lb[1] * net.cov(lt[0], lb[0])
        s1 = -u * q / 2
        s2 = s1 * s1 / 2
        return s1, s2

    def s12_engine(self, n: int, m: int) -> Tuple[Frac, Frac]:
        u = Frac(2)

        def ev(name, net_pow):
            tab = self.tabs.get(name, {}).get(net_pow)
            if not tab:
                return Frac(0)
            tot = Frac(0)
            for (w1, w2), (re, im) in tab.items():
                assert im == 0
                tot += re * Frac(n) ** len(w1) * Frac(m) ** len(w2)
            return tot * u ** net_pow

        s1 = -ev("L2", 1) / 2
        s2 = ev("L4", 2) / 24
        return s1, s2


# ---------------------------------------------------------------------------
# Flow assembly.
# ---------------------------------------------------------------------------


def cas4(n: int) -> int:
    return n * (n + 2)


def flow_slope(sfun, N: int, dim, cas, basis,
               pairs=((0, 1), (0, 2), (1, 2))) -> Dict:
    """Generic finite-basis pair-curve slope: v_n = sum_{m in basis}
    dim(m) e^{-tau cas(m)} T[n,m] with log T = const + tau s1 +
    tau^2 (s2 - s1^2/2); returns E0 (leading E*) and c1 per pair.
    sfun(n, m) -> (s1, s2); T's dim factors folded via dim(m)^2/d_n
    conventions cancel in pairs."""
    logv = {}
    for n in range(0, max(b for _a, b in pairs) + 1):
        W0, W1, W2 = Frac(0), Frac(0), Frac(0)
        for m in basis:
            w = Frac(dim(m)) ** 2
            s1, s2 = sfun(n, m)
            c = Frac(cas(m))
            W0 += w
            W1 += w * (s1 - c)
            W2 += w * (s2 - c * s1 + c * c / 2)
        logv[n] = (W1 / W0, W2 / W0 - W1 * W1 / (2 * W0 * W0))
    out = {}
    for (a, b) in pairs:
        dc = Frac(cas(b) - cas(a))
        e0 = -(logv[b][0] - logv[a][0]) / dc
        c1 = -(logv[b][1] - logv[a][1]) / dc
        out[f"{a},{b}"] = {"E0": e0, "c1": c1}
    return out


def u1_flow_gate(N: int = 2) -> Tuple[bool, Dict]:
    """The mirror through the SAME flow assembly: exact abelian
    exponential, basis |m| <= N: must give E0 = 3, c1 = -4 (N = 2)."""
    def sfun(n, m):
        s1 = -Frac(3 * n * n + 3 * m * m + 2 * n * m)
        return s1, s1 * s1 / 2

    res = flow_slope(sfun, N, lambda m: 1, lambda m: m * m,
                     [m for m in range(-N, N + 1)])
    ok = all(v["E0"] == 3 and v["c1"] == Frac(-4) for v in res.values())
    return ok, res


# ---------------------------------------------------------------------------
# Gates and main.
# ---------------------------------------------------------------------------


def chain_gate(k: int, nmax: int = 3):
    ser = Series(chain_net(k))
    rows = []
    ok = True
    s10, s20 = ser.s12(0, None)
    for n in range(1, nmax + 1):
        s1, s2 = ser.s12(n, None)
        lin = s1 - s10
        quad = (s2 - s1 * s1 / 2) - (s20 - s10 * s10 / 2)
        ok &= (lin == -k * cas4(n)) and (quad == 0)
        rows.append((n, lin, quad))
    return ok, rows


def _lstsq_exact(A, y):
    At = mat_T(A)
    M = mat_mul(At, A)
    b = [[sum(At[i][k] * y[k] for k in range(len(y)))]
         for i in range(len(At))]
    x = mat_mul(mat_inv(M), b)
    return [row[0] for row in x]


def main() -> None:
    import time

    t0 = time.time()
    print("MD.3 — the c_SU2 assembly (§16e queue (a)-(d))")
    print("=" * 72)

    print("GATE t — trace cache identities")
    ok_tr = _trace_cache_gate()
    print(f"  tr(J^aJ^b), tr(J^aJ^bJ^c) closed forms: "
          f"{'PASSED' if ok_tr else 'FAILED'}")

    print("GATE g3 — BCH series vs mpmath matrix logs")
    ok_bch = bch_gate()
    print(f"  2-, 3-, 4-factor cubic BCH: "
          f"{'PASSED' if ok_bch else 'FAILED'}")

    print("GATE g2 — single-face network (heat-kernel identity)")
    ok1, rows1 = chain_gate(1)
    for n, lin, quad in rows1:
        print(f"  n={n}: linear {lin} (want {-cas4(n)}), tau^2 "
              f"connected {quad} (want 0)")
    print(f"  gate g2: {'PASSED' if ok1 else 'FAILED'}")

    print("GATE g1 — semigroup chains (BCH + Jacobians + orderings)")
    ok2, rows2 = chain_gate(2)
    for n, lin, quad in rows2:
        print(f"  k=2 n={n}: linear {lin} (want {-2 * cas4(n)}), "
              f"tau^2 connected {quad} (want 0)")
    ok3, rows3 = chain_gate(3)
    for n, lin, quad in rows3:
        print(f"  k=3 n={n}: linear {lin} (want {-3 * cas4(n)}), "
              f"tau^2 connected {quad} (want 0)")
    print(f"  gate g1: {'PASSED' if (ok2 and ok3) else 'FAILED'}")

    print("GATE g4 — U(1) mirror: c_dyn = 0 and c1 = -4 at N = 2")
    net = slab_net()
    su1 = SeriesU1(net)
    ok4 = True
    for (n, m) in ((1, 1), (1, 2), (2, 2)):
        a = su1.s12_closed(n, m)
        b = su1.s12_engine(n, m)
        kappa2 = b[1] - b[0] * b[0] / 2
        ok4 &= (a == b) and (kappa2 == 0)
        print(f"  U(1) ({n},{m}): engine == closed exponential: "
              f"{a == b}; kappa2 = {kappa2}")
    okf, u1flow = u1_flow_gate(2)
    for key, v in u1flow.items():
        print(f"  U(1) flow pair {key}: E0 = {v['E0']}, c1 = {v['c1']}")
    ok4 &= okf
    print(f"  gate g4: {'PASSED' if ok4 else 'FAILED'}")

    print("=" * 72)
    print("THE SLAB — assembling the SU(2) series (exact)")
    ser = Series(net, progress=True)
    print(f"  V3 det-terms: {len(ser.eng.v3_terms)}; V4 dot-terms: "
          f"{len(ser.eng.v4_terms)}; q2 dot-terms: "
          f"{len(ser.eng.q2_terms)}  [{time.time() - t0:.0f}s]")
    cache: Dict = {}

    def sfun(n, m):
        if (n, m) not in cache:
            cache[(n, m)] = ser.s12(n, m)
        return cache[(n, m)]

    grid = {}
    for n in range(0, 4):
        for m in range(0, 4):
            grid[(n, m)] = sfun(n, m)
    base = grid[(0, 0)][0]
    ok5 = all(s1 - base == -3 * (cas4(n) + cas4(m))
              for (n, m), (s1, _s2) in grid.items())
    print(f"  gate g5a — s1 == const - 3(C(n)+C(m)): "
          f"{'PASSED' if ok5 else 'FAILED'}")
    kap = {k: (v[1] - v[0] * v[0] / 2) for k, v in grid.items()}

    def basis_row(n, m):
        cn, cm = Frac(cas4(n)), Frac(cas4(m))
        return [cn, cm, cn * cm, cn * cn, cm * cm,
                cn * cn * cm, cn * cm * cm, cn * cn * cm * cm]

    pts = [(n, m) for n in range(0, 4) for m in range(0, 4)
           if (n, m) != (0, 0)]
    A = [basis_row(n, m) for (n, m) in pts]
    y = [kap[(n, m)] - kap[(0, 0)] for (n, m) in pts]
    coef = _lstsq_exact(A, y)
    resid = [sum(a * c for a, c in zip(row, coef)) - yy
             for row, yy in zip(A, y)]
    names = ["Cn", "Cm", "CnCm", "Cn2", "Cm2", "Cn2Cm", "CnCm2",
             "Cn2Cm2"]
    print("  kappa2(n,m) - kappa2(0,0) = "
          + " + ".join(f"({c})*{nm}"
                       for c, nm in zip(coef, names) if c))
    ok6 = all(r == 0 for r in resid)
    print(f"  gate g5b — exact polynomial fit on the 4x4 grid: "
          f"{'PASSED' if ok6 else 'FAILED'}")
    okv = True
    for (n, m) in ((4, 0), (4, 2), (4, 4)):
        s1, s2 = sfun(n, m)
        kv = s2 - s1 * s1 / 2
        pred = kap[(0, 0)] + sum(
            a * c for a, c in zip(basis_row(n, m), coef))
        okv &= (kv == pred)
    print(f"  gate g5c — held-out (n=4) verification: "
          f"{'PASSED' if okv else 'FAILED'}")

    print("=" * 72)
    print("THE NUMBERS")
    res = {"trace_gate": ok_tr, "bch_gate": ok_bch,
           "chain_gates": bool(ok1 and ok2 and ok3),
           "u1_mirror": bool(ok4),
           "s1_structure": bool(ok5),
           "kappa2_fit_exact": bool(ok6 and okv),
           "kappa2_fit": {nm: str(c) for nm, c in zip(names, coef)},
           "flows": {}}
    alpha, beta = coef[0], coef[2]   # Cn-linear, CnCm coefficients
    c_dyn = -alpha
    print(f"  c_dyn (the dynamical diagonal defect) = -alpha = {c_dyn}")
    res["c_dyn"] = str(c_dyn)
    ok7 = True
    for N in (1, 2, 3):
        flow = flow_slope(sfun, N, lambda m: m + 1, cas4,
                          list(range(0, N + 1)))
        # closed form: c(N) = c_dyn - (2/3) E_w[C(m)], w ~ d_m^2
        wsum = sum(Frac((m + 1) ** 2) for m in range(N + 1))
        ew_c = sum(Frac((m + 1) ** 2) * cas4(m)
                   for m in range(N + 1)) / wsum
        closed = c_dyn - beta * ew_c
        print(f"  basis N = {N}:  closed form c = c_dyn - beta*E_w[C] "
              f"= {closed}")
        for key, e in flow.items():
            print(f"    pair {key}: E* leading {e['E0']}, slope c = "
                  f"{e['c1']}  (~ {float(e['c1']):+.6f})")
            ok7 &= (e["E0"] == 3 and e["c1"] == closed)
        res["flows"][str(N)] = {
            k: {"E0": str(v["E0"]), "c1": str(v["c1"])}
            for k, v in flow.items()}
    print(f"  gate g6 — closed form == assembled flow, all pairs, "
          f"N = 1..3: {'PASSED' if ok7 else 'FAILED'}")
    res["closed_form_gate"] = bool(ok7)
    # per-block attribution of the connected coefficient: the n-dep
    # part of kappa_2 decomposes additively into connected blocks
    # (the only n-dependent s1 piece is A = -L2/2, so cross products
    # among the insertion means are n-independent):
    #   tilt:  L4/24 - A^2/2          (fusion variance + orderings)
    #   q2 :   -q2L2/2 - A E[q2]      (heat-kernel Jacobians / Haar)
    #   V4 :   +V4L2/2 - A E[-V4]     (BCH quartic)
    #   V3^2:  -V3V3L2/4 - A E[V3^2]/2 (BCH cubic squared)
    #   V3L3:  the epsilon-linear cubic moment
    print("  block attribution (coefficients of Cn and CnCm in "
          "kappa2):")
    blocks = {}
    for bname in ("tilt", "q2", "V4", "V3V3", "V3L3"):
        vals = {}
        for (n, m) in [(n, m) for n in range(3) for m in range(3)]:
            ev = ser._ev
            A = -ev("L2", 1, 0, n, m)[0] / 2
            if bname == "tilt":
                v = ev("L4", 2, 0, n, m)[0] / 24 - A * A / 2
            elif bname == "q2":
                v = -ev("q2L2", 2, 0, n, m)[0] / 2 \
                    - A * ev("q2", 1, 0, n, m)[0]
            elif bname == "V4":
                v = ev("V4L2", 2, 1, n, m)[0] / 2 \
                    - A * (-ev("V4", 1, 1, n, m)[0])
            elif bname == "V3V3":
                v = -ev("V3V3L2", 2, 2, n, m)[0] / 4 \
                    - A * ev("V3V3", 1, 2, n, m)[0] / 2
            else:
                v = -ev("V3L3", 2, 1, n, m)[1] / 6
            vals[(n, m)] = v
        # extract Cn and CnCm coefficients on the grid
        b_cn = (vals[(1, 0)] - vals[(0, 0)]) / 3
        b_cross = (vals[(1, 1)] + vals[(0, 0)] - vals[(1, 0)]
                   - vals[(0, 1)]) / 9
        # verify linear+cross structure on (2,2)
        pred22 = vals[(0, 0)] + b_cn * 16 + b_cross * 64
        ok_b = (vals[(2, 2)] == pred22)
        blocks[bname] = (b_cn, b_cross, ok_b)
        print(f"    {bname:5s}: Cn-coef {b_cn}  CnCm-coef {b_cross}  "
              f"(structure OK: {ok_b})")
    res["blocks"] = {k: {"Cn": str(v[0]), "CnCm": str(v[1]),
                         "structure_ok": v[2]}
                    for k, v in blocks.items()}
    sum_cn = sum(v[0] for v in blocks.values())
    sum_cross = sum(v[1] for v in blocks.values())
    print(f"    sum:   Cn-coef {sum_cn} (fit {alpha}); CnCm-coef "
          f"{sum_cross} (fit {beta})")
    assert sum_cn == alpha and sum_cross == beta, "attribution sum"

    k11 = cache[(1, 1)][1] - cache[(1, 1)][0] ** 2 / 2
    k00 = cache[(0, 0)][1] - cache[(0, 0)][0] ** 2 / 2
    k10 = cache[(1, 0)][1] - cache[(1, 0)][0] ** 2 / 2
    k01 = cache[(0, 1)][1] - cache[(0, 1)][0] ** 2 / 2
    x11 = k11 + k00 - k10 - k01
    print(f"  X_11 = ({x11}) tau^2 + O(tau^3)   (~ {float(x11):+.4f};"
          f" pure-fusion prediction was +6)")
    res["X11_tau2"] = str(x11)
    with open(OUT_JSON, "w") as fh:
        json.dump(res, fh, indent=1)
    print(f"\nledger written to {OUT_JSON}  [{time.time() - t0:.0f}s]")


if __name__ == "__main__":
    main()
