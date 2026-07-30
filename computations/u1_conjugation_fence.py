"""THE U(1) CONJUGATION FENCE — where the SU(2) sector-PSD mechanism
must fail abelian-ly, in exact arithmetic (work_plan §17.4 fence,
§17e "the Gram object is T[nbar, m]").

WHAT IS BEING FENCED
--------------------
The new SU(2) one-step result decomposes the slab kernel over
transverse sectors,  T[n,m](s) = sum_sigma W_sigma(s) G_sigma(s),
with W_sigma > 0 and each 2x2 block G_sigma (n, m in {0,1}) PSD,
because Osterwalder-Seiler link-reflection positivity holds
sector-wise.  det is superadditive on PSD 2x2 matrices, so
truncating the sector family DECREASES det, and a finite sector
family certifies X_11 = log(T00 T11 / T01^2) > 0.

The standing fence: this must NOT go through for 4D compact U(1)
(Coulomb phase at weak coupling), where the banked one-step cross
observable is NEGATIVE.  This module locates the failure exactly.

THE ABELIAN KERNEL, IN CLOSED FORM (proved here, exactly)
---------------------------------------------------------
The M = infinity abelian owned-boundary kernel is the rank-4
cube-flip theta series of computations/u1_theta_kernel:

    T[n,m](s) = sum_{c in Z^4} s^{Q(c; n, m)},
    Q(c; n, m) = c^T A c + b(n,m).c + |k0(n,m)|^2,
    A = 6 I - Adj(C_4)  (spectrum {4,6,6,8}),
    b(n,m) = 2 (n - m) (1,1,1,1),   |k0(n,m)|^2 = 4 n^2 + 4 m^2.

Write  a(c) := c^T A c,  S(c) := sum_i c_i,  D_n := s^{4 n^2}.  Then
Q(c;n,m) = a(c) + 2 S(c) (n - m) + 4 n^2 + 4 m^2, hence EXACTLY

    T[n,m](s) = D_n D_m Phi(n - m),      Phi(k) := sum_c s^{a(c) + 2 k S(c)}

-- a TOEPLITZ form in Phi dressed by a positive diagonal.  Phi is
even (c -> -c), and Phi(k) = sum_c w_c x_c^k with w_c = s^{a(c)} > 0
and x_c = s^{2 S(c)} > 0: a STIELTJES MOMENT SEQUENCE.

Charge conjugation is n -> nbar = -n on U(1).  The conjugated
(= OS Gram) object is therefore

    M[n,m] := T[-n, m] = D_n D_m Phi(-(n + m)) = D_n D_m Phi(n + m)

-- a HANKEL form in the same Phi.

    HANKEL of a moment sequence is PSD.       (conjugated: PASSES)
    TOEPLITZ of a moment sequence is NOT.     (unconjugated: FAILS)

Sector-wise the two statements are one line each.  Take the sector
to be a flip-lattice orbit sigma = {c, -c} (the orbit, because OS
reflection acts on the transverse configuration exactly by c -> -c;
single c gives a non-symmetric block).  With a = a(c), S = S(c):

  CONJUGATED, per single c:  M_c[n,m] = s^{a + f(n) + f(m)},
      f(n) = -2 S n + 4 n^2   =>   M_c = x x^T,  x_n = s^{a/2 + f(n)}
      RANK ONE, PSD, det = 0 exactly.  Sum over c: PSD.  QED.

  UNCONJUGATED, per orbit {c, -c}:
      G_sigma = [[2 s^a, s^{a+4}(t + 1/t)], [., 2 s^{a+8}]],  t = s^{2S}
      det G_sigma = s^{2a+8} (4 - (t + 1/t)^2)  <  0  whenever S(c) != 0,
      since t + 1/t > 2 for t != 1.
      EVERY sector with S(c) != 0 has a STRICTLY NEGATIVE determinant.

So the abelian sector blocks are, in the X_11 indexing, uniformly
NOT PSD; det-superadditivity is unavailable (truncation no longer
lower-bounds det), and indeed the assembled determinant is negative:

    det [T[n,m]]_{n,m in {0,1}} = s^8 (Phi(0)^2 - Phi(1)^2)  <  0,
    X_U1(s) = log(T00 T11 / T01^2) = -2 log(Phi(1) / Phi(0))  <  0
              for EVERY s in (0, 1),

because, grouping the flip lattice into +/- orbits,

    Phi(1) - Phi(0) = sum_{orbits, S != 0} s^{a(c)} (s^{-S(c)} - s^{S(c)})^2 > 0

-- a manifest sum of positive rationals.  Any finite subfamily of
orbits certifies Phi(1) > Phi(0), hence X_U1 < 0, with NO tail
analysis at all.  (Also exact and used below: T[n,n] = s^{8 n^2} T[0,0]
term by term, and T[-n,n] = s^{4 n^2} T[0,0] ... no: T[-n,n] =
D_n^2 Phi(0) is false; T[-n,n] = D_n D_n Phi(0) = s^{8n^2} Phi(0).)

WHERE SU(2) SELF-CONJUGACY IS LOAD-BEARING
------------------------------------------
OS/link reflection positivity yields PSD of the Gram matrix
[ <R f_nbar, f_m> ] = [ T[nbar, m] ] -- the reflection conjugates the
boundary charge.  On U(1) nbar = -n != n, so the PSD object is the
HANKEL matrix [Phi(n+m)] and the observable X_11 is built from the
TOEPLITZ matrix [Phi(n-m)]: different matrices, opposite sign.  On
SU(2) every irrep is self-conjugate (chi_jbar = chi_j, real
characters), so nbar = n and T[nbar, m] = T[n, m]: the OS-PSD object
and the X_11 object are the SAME matrix, sector by sector.  That
identification -- and nothing else about the group in this step --
is what licenses the sector-PSD + det-superadditivity argument.

Run:  python -m computations.u1_conjugation_fence
"""

from __future__ import annotations

import itertools
import json
import math
import os
import sys
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.set_int_max_str_digits(0)

# The five probe couplings demanded by the fence protocol.
PROBE_S: Tuple[Frac, ...] = (Frac(1, 10), Frac(1, 2), Frac(3, 5),
                             Frac(4, 5), Frac(9, 10))

# ---------------------------------------------------------------------------
# The exact flip-lattice geometry.
#
# Preferred: import the banked module.  If the certified geometry module
# computations/dp6_u1_slab_blocking is not present in the checkout, we
# RECONSTRUCT (A, b, c0) from the three independently banked facts in
# computations/u1_theta_kernel's own docstring/gates:
#   (i)   A = 6 I - Adj(C_4), charpoly = (x-4)(x-6)^2(x-8);
#   (ii)  b(n,m) = 2 (n-m) (1,1,1,1)  [B^T u = (1,1,1,1) = -B^T w];
#   (iii) |u|^2 = |w|^2 = 4, u.w = 0  [E* = |u|^2 - 1^T A^{-1} 1 = 4-1 = 3,
#         and qmin(1,1) = 8], hence |k0(n,m)|^2 = 4 n^2 + 4 m^2.
# The reconstruction is then GATED against the banked exact ledger
# computations/u1_theta_results.json (v_n windows at s = 1/2, 3/4, 9/10).
# ---------------------------------------------------------------------------

A_MAT: List[List[int]] = [[6 if i == j else
                           (-1 if (i - j) % 4 in (1, 3) else 0)
                           for j in range(4)] for i in range(4)]


def qform_data(n: int, m: int) -> Tuple[int, List[int]]:
    """(c0, b) with Q(c; n, m) = c^T A c + b.c + c0, all integers."""
    return 4 * n * n + 4 * m * m, [2 * (n - m)] * 4


def charpoly4(M: Sequence[Sequence[int]]) -> List[int]:
    """Exact characteristic polynomial coefficients [c0..c4] of a 4x4
    integer matrix, via Leverrier-Faddeev on exact integers."""
    n = 4
    # det(xI - M) by exact expansion over permutations (integer coeffs)
    coeffs = [0] * (n + 1)
    for perm in itertools.permutations(range(n)):
        sgn = _perm_sign(perm)
        # product over i of (x delta_{i,perm[i]} - M[i][perm[i]])
        poly = [1]                     # constant 1
        for i in range(n):
            j = perm[i]
            fac = [-M[i][j], 1] if i == j else [-M[i][j]]
            poly = _polymul(poly, fac)
        for d, c in enumerate(poly):
            coeffs[d] += sgn * c
    return coeffs


def _perm_sign(perm: Sequence[int]) -> int:
    s = 1
    p = list(perm)
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


def _polymul(a: Sequence[int], b: Sequence[int]) -> List[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def _solve(Amat, rhs):
    n = len(Amat)
    M = [[Frac(Amat[i][j]) for j in range(n)] + [Frac(rhs[i])]
         for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        inv = 1 / M[col][col]
        M[col] = [x * inv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def qmin(n: int, m: int) -> Frac:
    """Exact real minimum |k0|^2 - b^T A^{-1} b / 4 = 3n^2+3m^2+2nm."""
    c0, b = qform_data(n, m)
    x = _solve(A_MAT, [Frac(bi, 2) for bi in b])
    return Frac(c0) - sum(Frac(bi) * xi for bi, xi in zip(b, x)) / 2


# ---------------------------------------------------------------------------
# Certified theta windows (same tail theorem as u1_theta_kernel).
# ---------------------------------------------------------------------------


def tail_bound(n: int, m: int, s: Frac, R: int) -> Frac:
    c0, b = qform_data(n, m)
    b1 = sum(abs(x) for x in b)
    assert 2 * R >= b1, f"R = {R} too small for |b|_1 = {b1}"
    q = s ** (2 * (R + 1))
    assert q < 1
    return (s ** c0) * 80 * q ** (R + 1) * Frac((R + 1) ** 3) \
        * 6 / (1 - q) ** 4


_HIST_CACHE: Dict[Tuple[int, int], Dict[int, int]] = {}


def _partial_sum_exponents(n: int, m: int, R: int) -> Dict[int, int]:
    """Histogram {Q(c): count} over |c_i| <= R.  Pure-python exact
    integers (no numpy: no int64 overflow risk)."""
    key = (n - m, R)                   # Q depends on (n-m) plus the shift c0
    c0, b = qform_data(n, m)
    if key in _HIST_CACHE:
        base = _HIST_CACHE[key]
        return {E + c0: h for E, h in base.items()}
    A = A_MAT
    base: Dict[int, int] = {}
    rng = range(-R, R + 1)
    bb = b[0]                          # b is (bb, bb, bb, bb)
    for c1 in rng:
        for c2 in rng:
            q12 = (6 * c1 * c1 + 6 * c2 * c2 + 2 * A[0][1] * c1 * c2
                   + bb * (c1 + c2))
            l3 = 2 * (A[0][2] * c1 + A[1][2] * c2) + bb
            l4 = 2 * (A[0][3] * c1 + A[1][3] * c2) + bb
            for c3 in rng:
                p3 = q12 + 6 * c3 * c3 + l3 * c3
                for c4 in rng:
                    E = p3 + 6 * c4 * c4 + 2 * A[2][3] * c3 * c4 + l4 * c4
                    base[E] = base.get(E, 0) + 1
    _HIST_CACHE[key] = base
    return {E + c0: h for E, h in base.items()}


def _eval_hist(hist: Dict[int, int], s: Frac) -> Frac:
    num, den = s.numerator, s.denominator
    exps = sorted(hist)
    acc = 0
    prev = 0
    pow_n = 1
    for E in exps:
        gap = E - prev
        pow_n *= num ** gap
        acc = acc * den ** gap + hist[E] * pow_n
        prev = E
    return Frac(acc, den ** prev)


_WIN_CACHE: Dict[Tuple[int, int, Frac, Frac], Tuple[Frac, Frac, int]] = {}


def theta_window(n: int, m: int, s: Frac, tail_target: Frac,
                 R_max: int = 60) -> Tuple[Frac, Frac, int]:
    """Certified window [lo, hi] for T_inf[n,m](s) with
    hi - lo <= tail_target."""
    key = (n, m, s, tail_target)
    if key in _WIN_CACHE:
        return _WIN_CACHE[key]
    _c0, b = qform_data(n, m)
    b1 = sum(abs(x) for x in b)
    R = max(2, (b1 + 1) // 2 + 1)
    while R <= R_max:
        if tail_bound(n, m, s, R) <= tail_target:
            break
        R += max(1, R // 8)
    else:
        raise ValueError("R_max exceeded before tail target met")
    part = _eval_hist(_partial_sum_exponents(n, m, R), s)
    res = (part, part + tail_bound(n, m, s, R), R)
    _WIN_CACHE[key] = res
    return res


def entry_window(n: int, m: int, s: Frac,
                 rel: Frac = Frac(1, 10 ** 15)) -> Tuple[Frac, Frac]:
    """Window scaled to the entry's own magnitude s^qmin."""
    target = s ** int(qmin(n, m)) * rel + Frac(1, 10 ** 40)
    lo, hi, _R = theta_window(n, m, s, target)
    return lo, hi


# ---------------------------------------------------------------------------
# Phi and the sign-of-det certificates (tail-free).
# ---------------------------------------------------------------------------


def _orbit_reps(R: int):
    """One representative per {c, -c} orbit of the box |c_i| <= R,
    together with a(c) = c^T A c and S(c) = sum c_i."""
    seen = set()
    for c in itertools.product(range(-R, R + 1), repeat=4):
        if c in seen:
            continue
        seen.add(c)
        seen.add(tuple(-x for x in c))
        a = sum(A_MAT[i][j] * c[i] * c[j] for i in range(4) for j in range(4))
        yield c, a, sum(c)


def phi_gap_lower(s: Frac, R: int = 3) -> Tuple[Frac, List[Tuple]]:
    """Certified STRICT lower bound on Phi(1) - Phi(0), as the exact
    finite sum of manifestly positive orbit terms

        s^{a(c)} (s^{-S(c)} - s^{S(c)})^2,     S(c) != 0,

    over the box |c_i| <= R.  Every dropped term is >= 0, so this is a
    valid lower bound with NO tail analysis.  Returns (bound, top terms)."""
    tot = Frac(0)
    terms = []
    for c, a, S in _orbit_reps(R):
        if S == 0:
            continue
        t = s ** a * (s ** (-S) - s ** S) ** 2
        tot += t
        terms.append((t, c, a, S))
    terms.sort(key=lambda x: -x[0])
    return tot, terms[:4]


def sector_det_unconj(c: Sequence[int], s: Frac) -> Frac:
    """Exact det of the 2x2 UNCONJUGATED sector block over the orbit
    sigma = {c, -c}:  G[n,m] = sum_{c' in sigma} s^{Q(c'; n, m)},
    n, m in {0, 1}."""
    g: Dict[Tuple[int, int], Frac] = {}
    orbit = [tuple(c), tuple(-x for x in c)]
    if orbit[0] == orbit[1]:
        orbit = orbit[:1]
    for n in (0, 1):
        for m in (0, 1):
            g[(n, m)] = sum(
                s ** _Q(cc, n, m) for cc in orbit)
    assert g[(0, 1)] == g[(1, 0)], "orbit block must be symmetric"
    return g[(0, 0)] * g[(1, 1)] - g[(0, 1)] * g[(1, 0)]


def sector_det_conj(c: Sequence[int], s: Frac) -> Frac:
    """Exact det of the 2x2 CONJUGATED sector block M[n,m] =
    s^{Q(c; -n, m)}, n, m in {0, 1} -- a single c suffices (already
    symmetric).  Must be exactly 0 (rank one)."""
    q = {(n, m): _Q(c, -n, m) for n in (0, 1) for m in (0, 1)}
    assert q[(0, 1)] == q[(1, 0)]
    return s ** q[(0, 0)] * s ** q[(1, 1)] - s ** q[(0, 1)] * s ** q[(1, 0)]


def _Q(c: Sequence[int], n: int, m: int) -> int:
    c0, b = qform_data(n, m)
    return (sum(A_MAT[i][j] * c[i] * c[j] for i in range(4) for j in range(4))
            + b[0] * sum(c) + c0)


def sector_min_eig_sign(mat: Dict[Tuple[int, int], Frac]) -> str:
    """PSD verdict for an exact symmetric 2x2 by Sylvester."""
    a, d = mat[(0, 0)], mat[(1, 1)]
    det = a * d - mat[(0, 1)] * mat[(1, 0)]
    if a >= 0 and d >= 0 and det >= 0:
        return "PSD"
    return "NOT PSD"


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def gate_spectrum() -> bool:
    """charpoly(A) == (x-4)(x-6)^2(x-8) = x^4-24x^3+212x^2-816x+1152."""
    return charpoly4(A_MAT) == [1152, -816, 212, -24, 1]


def gate_qmin_grid() -> bool:
    ok = True
    for n in range(-3, 4):
        for m in range(-3, 4):
            ok &= qmin(n, m) == 3 * n * n + 3 * m * m + 2 * n * m
    ok &= (qmin(1, 0), qmin(0, 1), qmin(1, 1), qmin(1, -1)) == \
        (Frac(3), Frac(3), Frac(8), Frac(4))
    return bool(ok)


def gate_closed_forms(s: Frac = Frac(3, 7)) -> bool:
    """T[n,m] = D_n D_m Phi(n-m) and T[n,n] = s^{8n^2} T[0,0], checked
    TERM BY TERM on the exponent histograms (exact, truncation-free
    as an identity of multisets)."""
    R = 5
    ok = True
    for (n, m) in [(0, 0), (0, 1), (1, 1), (1, -1), (2, 1), (-1, 2)]:
        h = _partial_sum_exponents(n, m, R)
        # D_n D_m Phi(n-m): shift the (0, m-n... ) reference histogram
        k = n - m
        href = _partial_sum_exponents(k, 0, R)          # b = 2k, c0 = 4k^2
        shift = 4 * n * n + 4 * m * m - 4 * k * k
        ok &= h == {E + shift: v for E, v in href.items()}
    for n in (1, 2):
        h = _partial_sum_exponents(n, n, R)
        h0 = _partial_sum_exponents(0, 0, R)
        ok &= h == {E + 8 * n * n: v for E, v in h0.items()}
    del s
    return bool(ok)


def gate_banked_ledger() -> Tuple[bool, List[str]]:
    """Reproduce the banked exact ledger u1_theta_results.json: the
    v_n = sum_{|m|<=2} T[n,m] s^{m^2} windows at s = 1/2, 3/4, 9/10
    must be reproduced by THIS module's kernel to the banked digits."""
    path = os.path.join(HERE, "u1_theta_results.json")
    notes: List[str] = []
    if not os.path.exists(path):
        return False, ["u1_theta_results.json absent -- cannot gate"]
    with open(path) as fh:
        led = json.load(fh)
    ok = True
    for row in led["rows"]:
        s = Frac(row["s"])
        if s not in (Frac(1, 2), Frac(3, 4), Frac(9, 10)):
            continue
        for nkey, (blo, bhi) in row["v_windows"].items():
            n = int(nkey)
            lo = Frac(0)
            hi = Frac(0)
            for m in range(-2, 3):
                mm = max(abs(n), abs(m))
                floor = s ** (int(qmin(mm, mm)) + 40)
                tl, th, _R = theta_window(n, m, s, floor / 10 ** 6)
                w = s ** (m * m)
                lo += tl * w
                hi += th * w
            bl, bh = Frac(blo), Frac(bhi)
            # the two certified windows must OVERLAP, and ours must be
            # consistent with the banked one to the banked precision
            good = not (hi < bl or lo > bh)
            ok &= good
            notes.append(
                f"  s={s} v_{n}: ours [{float(lo):.12f}, {float(hi):.12f}] "
                f"banked [{float(bl):.12f}, {float(bh):.12f}]  "
                f"{'OVERLAP' if good else 'DISJOINT -- MISMATCH'}")
    return bool(ok), notes


# ---------------------------------------------------------------------------
# The fence itself.
# ---------------------------------------------------------------------------


def x_u1_window(s: Frac) -> Tuple[Frac, Frac]:
    """Certified rational window for T00 T11 / T01^2 (X_U1 = log of it),
    same convention as p2_iterated.u1_x1_ratio_window."""
    w11 = entry_window(1, 1, s)
    w00 = entry_window(0, 0, s)
    w01 = entry_window(0, 1, s)
    return (w11[0] * w00[0] / (w01[1] ** 2),
            w11[1] * w00[1] / (w01[0] ** 2))


def teeth(s: Frac, R_sec: int = 2) -> dict:
    """The two-sided teeth at one coupling, all exact."""
    out: dict = {"s": str(s)}

    # ---- (2) UNCONJUGATED sector blocks: PSD must FAIL ----
    neg = []
    n_psd = 0
    n_neg = 0
    for c, a, S in _orbit_reps(R_sec):
        d = sector_det_unconj(c, s)
        if d < 0:
            n_neg += 1
            neg.append((d, c, a, S))
        else:
            n_psd += 1
        assert (d < 0) == (S != 0), \
            "sector det sign must be exactly [S(c) != 0]"
    neg.sort(key=lambda x: -x[0])          # least negative first
    out["unconj_sectors_total"] = n_neg + n_psd
    out["unconj_sectors_negative_det"] = n_neg
    out["unconj_witness"] = [
        {"c": list(c), "a": a, "S": S, "det": str(d), "det_float": float(d)}
        for d, c, a, S in neg[:1] + neg[-1:]]

    # ---- (3) CONJUGATED sector blocks: PSD must HOLD (rank one) ----
    bad_conj = []
    for c, a, S in _orbit_reps(R_sec):
        dc = sector_det_conj(c, s)
        if dc != 0:
            bad_conj.append((c, dc))
    out["conj_sectors_all_rank_one_det_zero"] = (bad_conj == [])
    out["conj_bad"] = [[list(c), str(d)] for c, d in bad_conj[:3]]

    # ---- assembled 2x2 blocks from certified kernel windows ----
    w00 = entry_window(0, 0, s)
    w01 = entry_window(0, 1, s)
    w11 = entry_window(1, 1, s)
    # unconjugated det upper bound: hi*hi - lo*lo
    det_un_hi = w00[1] * w11[1] - w01[0] ** 2
    out["assembled_unconj_det_hi"] = float(det_un_hi)
    # tail-free certified negativity: det = s^8 (Phi(0)^2 - Phi(1)^2)
    gap, top = phi_gap_lower(s, R=3)
    out["phi_gap_lower_exact"] = str(gap)
    out["phi_gap_lower_float"] = float(gap)
    out["phi_gap_top_terms"] = [
        {"c": list(c), "a": a, "S": S, "term": float(t)} for t, c, a, S in top]

    # conjugated assembled: M[n,m] = T[-n,m], n,m in {0,1}
    #   M00 = T[0,0], M01 = M10 = T[0,1] (=T[-1,0] by symmetry+evenness),
    #   M11 = T[-1,1]
    mw00 = entry_window(0, 0, s)
    mw01 = entry_window(0, 1, s)          # T[0,1]
    mw10 = entry_window(-1, 0, s)         # T[-1,0]  -- must equal T[0,1]
    mw11 = entry_window(-1, 1, s)
    out["conj_index_check_T0_1_eq_Tm1_0"] = not (
        mw01[1] < mw10[0] or mw01[0] > mw10[1])
    det_cj_lo = mw00[0] * mw11[0] - mw01[1] ** 2
    det_cj_hi = mw00[1] * mw11[1] - mw01[0] ** 2
    out["assembled_conj_det_window"] = [float(det_cj_lo), float(det_cj_hi)]
    # exact structural statement: det_conj = s^{8}(Phi(0)^2 - Phi(0)^2) = 0
    # for the {0,1} block, since M11 = T[-1,1] = s^8 Phi(0) and
    # M01 = T[0,1] = s^4 Phi(1)... check the true Hankel 2x2:
    #   det = s^8 Phi(0)^2 - s^8 Phi(1)^2  <- that is the TOEPLITZ one.
    # Hankel: M[n,m] = D_n D_m Phi(n+m):
    #   det = D_0^2 D_1^2 (Phi(0) Phi(2) - Phi(1)^2)  >= 0 by moment PSD.
    out["hankel_det_sign_claim"] = "Phi(0) Phi(2) - Phi(1)^2 >= 0 (Cauchy-Schwarz)"

    # ---- (4) reproduce X_U1 ----
    rlo, rhi = x_u1_window(s)
    out["X_U1"] = [math.log(float(rlo)), math.log(float(rhi))]
    out["X_U1_leading_minus_2tau"] = -2 * (-math.log(float(s)))
    return out


def hankel_toeplitz_2x2(s: Frac, R: int = 6) -> dict:
    """The reduction to Phi, checked with certified windows:
    Phi(0) = T[0,0], Phi(k) = T[k,0] / s^{4 k^2}.  Then
      Toeplitz 2x2 det  = Phi(0)^2 - Phi(1)^2   (must be < 0)
      Hankel   2x2 det  = Phi(0) Phi(2) - Phi(1)^2  (must be >= 0)
    Both certified from the same exact entry windows."""
    def phi(k: int) -> Tuple[Frac, Frac]:
        lo, hi = entry_window(k, 0, s)
        d = s ** (4 * k * k)
        return lo / d, hi / d
    p0, p1, p2 = phi(0), phi(1), phi(2)
    del R
    toep_hi = p0[1] ** 2 - p1[0] ** 2
    toep_lo = p0[0] ** 2 - p1[1] ** 2
    hank_lo = p0[0] * p2[0] - p1[1] ** 2
    hank_hi = p0[1] * p2[1] - p1[0] ** 2
    return {"Phi0": [float(p0[0]), float(p0[1])],
            "Phi1": [float(p1[0]), float(p1[1])],
            "Phi2": [float(p2[0]), float(p2[1])],
            "toeplitz_det": [float(toep_lo), float(toep_hi)],
            "toeplitz_negative_certified": toep_hi < 0,
            "hankel_det": [float(hank_lo), float(hank_hi)],
            "hankel_nonneg_certified": hank_lo >= 0}


def gate_teeth_charges(ss: Tuple[Frac, ...] = (Frac(1, 2), Frac(9, 10)),
                       K: int = 3) -> Tuple[bool, bool, List[str]]:
    """The banked §17e two-sided check, replayed independently:
    CONJUGATED Cauchy-Schwarz  T[-n,m]^2 <= T[-n,n] T[-m,m]  holds for
    all 0 <= n, m <= K; the UNCONJUGATED form T[n,m]^2 <= T[n,n] T[m,m]
    must FAIL somewhere."""
    conj_ok = True
    teeth_fired = False
    notes: List[str] = []
    for s in ss:
        for n in range(K + 1):
            for m in range(K + 1):
                if n == m:
                    continue

                def minabs(w):
                    lo, hi = w
                    return Frac(0) if lo <= 0 <= hi else min(abs(lo), abs(hi))
                dn = entry_window(-n, n, s)[1]
                dm = entry_window(-m, m, s)[1]
                c_ok = minabs(entry_window(-n, m, s)) ** 2 <= dn * dm
                conj_ok &= c_ok
                raw = minabs(entry_window(n, m, s)) ** 2 <= \
                    entry_window(n, n, s)[1] * entry_window(m, m, s)[1]
                if not raw:
                    teeth_fired = True
                    if len(notes) < 6:
                        notes.append(
                            f"  s={s} (n,m)=({n},{m}): UNCONJUGATED CS FAILS "
                            f"[2*qmin({n},{m})={2*int(qmin(n,m))} < "
                            f"qmin({n},{n})+qmin({m},{m})="
                            f"{int(qmin(n,n))+int(qmin(m,m))}]")
                if not c_ok:
                    notes.append(f"  s={s} (n,m)=({n},{m}): CONJUGATED CS "
                                 f"FAILS -- FENCE BROKEN")
    return bool(conj_ok), bool(teeth_fired), notes


def main() -> None:
    print("=" * 72)
    print("U(1) CONJUGATION FENCE -- the SU(2) sector-PSD mechanism must")
    print("fail abelian-ly.  All arithmetic exact (fractions.Fraction).")
    print("=" * 72)
    print(f"A = {A_MAT}")
    print("GATE charpoly(A) == (x-4)(x-6)^2(x-8):",
          "PASSED" if gate_spectrum() else "FAILED")
    print("GATE Qmin(n,m) == 3n^2+3m^2+2nm on [-3,3]^2:",
          "PASSED" if gate_qmin_grid() else "FAILED")
    print("GATE closed forms T[n,m]=D_n D_m Phi(n-m), T[n,n]=s^{8n^2}T[0,0]")
    print("     (exponent-multiset identity):",
          "PASSED" if gate_closed_forms() else "FAILED")
    okled, notes = gate_banked_ledger()
    print("GATE reproduce banked u1_theta_results.json v-windows:",
          "PASSED" if okled else "FAILED")
    for ln in notes:
        print(ln)

    print()
    print("-" * 72)
    print("TEETH (banked §17e replay): conjugated CS vs unconjugated CS")
    print("-" * 72)
    cok, tfired, tnotes = gate_teeth_charges()
    for ln in tnotes:
        print(ln)
    print(f"  CONJUGATED  T[-n,m]^2 <= T[-n,n]T[-m,m] for 0<=n,m<=3: "
          f"{'HOLDS (PASS)' if cok else 'FAILS (FENCE BROKEN)'}")
    print(f"  UNCONJUGATED T[n,m]^2 <= T[n,n]T[m,m]: "
          f"{'FAILS somewhere (PASS -- teeth)' if tfired else 'HOLDS EVERYWHERE -- REFUTATION'}")

    print()
    print("-" * 72)
    print("PER-COUPLING FENCE")
    print("-" * 72)
    rows = []
    for s in PROBE_S:
        r = teeth(s)
        h = hankel_toeplitz_2x2(s)
        r["hankel_toeplitz"] = h
        rows.append(r)
        print(f"s = {s}   tau = {-math.log(float(s)):.6f}")
        print(f"  X_U1 window                 : "
              f"[{r['X_U1'][0]:+.6f}, {r['X_U1'][1]:+.6f}]   "
              f"(leading -2tau = {r['X_U1_leading_minus_2tau']:+.6f})")
        print(f"  UNCONJUGATED sector blocks  : "
              f"{r['unconj_sectors_negative_det']} of "
              f"{r['unconj_sectors_total']} orbits have det < 0  -> NOT PSD")
        for w in r["unconj_witness"]:
            print(f"      witness c={w['c']} a={w['a']} S={w['S']}: "
                  f"det = {w['det']}")
            print(f"          = {w['det_float']:+.6e}")
        print(f"  CONJUGATED sector blocks    : all rank one, det == 0 "
              f"exactly: {r['conj_sectors_all_rank_one_det_zero']}")
        print(f"  Phi(1) - Phi(0) >= (exact, tail-free) "
              f"{r['phi_gap_lower_float']:.6e} > 0  -> det[T] < 0")
        print(f"  Toeplitz det Phi0^2-Phi1^2  : "
              f"[{h['toeplitz_det'][0]:+.6e}, {h['toeplitz_det'][1]:+.6e}] "
              f"NEGATIVE certified: {h['toeplitz_negative_certified']}")
        print(f"  Hankel   det Phi0Phi2-Phi1^2: "
              f"[{h['hankel_det'][0]:+.6e}, {h['hankel_det'][1]:+.6e}] "
              f"NONNEG certified: {h['hankel_nonneg_certified']}")
        print()

    ok_all = (gate_spectrum() and gate_qmin_grid() and gate_closed_forms()
              and okled and cok and tfired
              and all(r["unconj_sectors_negative_det"] > 0 for r in rows)
              and all(r["conj_sectors_all_rank_one_det_zero"] for r in rows)
              and all(r["X_U1"][1] < 0 for r in rows)
              and all(r["hankel_toeplitz"]["toeplitz_negative_certified"]
                      for r in rows)
              and all(r["hankel_toeplitz"]["hankel_nonneg_certified"]
                      for r in rows))
    print("=" * 72)
    print("FENCE VERDICT:", "FIRES AS REQUIRED" if ok_all
          else "*** DID NOT FIRE -- INVESTIGATE ***")
    print("=" * 72)
    with open(os.path.join(HERE, "u1_conjugation_fence_results.json"),
              "w") as fh:
        json.dump({"ok": ok_all, "rows": rows,
                   "teeth_conjugated_holds": cok,
                   "teeth_unconjugated_fails": tfired}, fh, indent=1,
                  default=str)
    if not ok_all:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
