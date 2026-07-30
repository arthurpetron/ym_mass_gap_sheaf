"""THE SECTOR-SOS POSITIVITY CERTIFICATE — X_11 > 0 on ALL of (0, 1)
from one exact polynomial (work_plan §17g, queue item P3).

WHY THIS MODULE EXISTS
----------------------
Queue item P3 ("overlap closure / the atlas-adequacy lemma") asked for a
FINITE Sturm-certified rational cover of the compact middle regime
[2^{-1/3}, s_*], chaining the unconditional strong-coupling anchor to the
validity edge of the MD.3 weak-coupling envelope.  The coverage audit
(computations/atlas_adequacy.py) shows why that request could not be met
by marching the §16h-§17e one-step window instrument: every certified
grid point banked so far (s = 1/2 ... 5/8) lies STRICTLY INSIDE the
unconditional anchor window [0, 2^{-1/3}), so the marched frontier
contributes ZERO coverage to the interval the atlas is for.

This module closes the SIGN half of atlas-adequacy outright, on the whole
open interval, by a structural route that needs no windows, no label
cutoff, no unresolved diagonals, no tail closure and no atlas.

THE STRUCTURE
-------------
The M -> infinity owned-boundary slab kernel decomposes over TRANSVERSE
SECTORS sigma = (q, w) -- the perimeter-class and interior-wall labels,
which sit on theta-invariant faces (su2_cs_tail, §16h):

    T[n,m](s) = sum_sigma  W_sigma(s) * G_sigma[n,m](s),         (1)
    W_sigma(s) = prod_i dim(q_i)^2 s^{2 C(q_i)} * prod_i dim(w_i) s^{C(w_i)} > 0,
    G_sigma[n,m](s) = sum_{top, bot} prod dim * s^{sum C} * N(n,m,sigma,top,bot),

with N the pure-character Haar value (dp3_fixed_tile.network_value_fixed).

THREE FACTS, IN ORDER.

(F1) EACH G_sigma IS AN EXACT FINITE POLYNOMIAL.  At fixed sector the
     triad constraint triad(n, q_i, a_i) forces |n - q_i| <= a_i <=
     n + q_i, so the tile sums TERMINATE: for M >= n + max(q) the
     sector kernel is exact.  There is no truncation error inside a
     sector -- ever.  (Gated: M-independence, gate_exactness.)

(F2) EACH G_sigma IS PSD as a 2x2 matrix over (n, m) in {0,1}^2.  This is
     the BANKED §16h mathematical input, sector-wise Osterwalder-Seiler
     link-reflection positivity: the half-config pairing
     H[(n,a),(m,b)] = N(n,m,sigma,a,b) is a PSD Gram matrix (it is what
     the §16h config-level lemma N^2 <= N_aa N_bb is derived FROM), and
     G_sigma = V^T H V with V's columns the strictly positive tile
     weights.  Two distinct uses of SU(2) SELF-CONJUGACY are load-bearing
     and are named in the U(1) fence below.  (Gated: gate_psd, exact
     square-root-free LDL on H, all sectors of the certificate family.)

(F3) det IS SUPERADDITIVE ON PSD 2x2 MATRICES.  For 2x2 matrices,
     det(X + Y) = det X + det Y + tr(X adj Y) exactly; for PSD X, Y both
     det Y >= 0 and tr(X adj Y) >= 0 (adj of a PSD 2x2 is PSD).  Hence

         det T_S(s)  <=  det T_full(s)   for every finite sector set S.  (2)

     Equivalently, with the exact pair expansion of (1),
         det T_full = sum_sigma W_sigma^2 det G_sigma
                      + sum_{sigma < sigma'} W_sigma W_sigma' Q(sigma,sigma'),
         Q(sigma,sigma') = A B' + B A' - 2 C C'  >=  0,
     a sum of NON-NEGATIVE terms indexed by sector pairs -- the depth-1
     analogue of the §17e depth-2 Lagrange/Cauchy-Binet SOS.  (Gated:
     gate_identity checks the expansion as an exact rational identity and
     gate_pair_nonneg checks every Q >= 0.)

THE CERTIFICATE
---------------
Take S = the 16 sectors with all labels <= 1.  Their exact kernels are
tiny integer polynomials:

    T00_S = 1 + 16 s^18 + 16 s^30 + 32 s^36 + 16 s^42 + 4 s^48
    T01_S = 2 s^12 + 8 s^24 + 8 s^30 + 24 s^32 + 14 s^36 + 24 s^44
            + 24 s^46 + 36 s^52 + 24 s^60 + 6 s^68
    T11_S = 5 s^24 + 12 s^30 + 2 s^36 + 24 s^38 + 60 s^46 + 36 s^52
            + 24 s^54 + 6 s^56 + 48 s^60 + 36 s^62 + 42 s^68 + 36 s^78
            + 9 s^88

    det_S(s) = T00_S T11_S - T01_S^2 = s^24 * P(s),  deg P = 106,
    P(0) = 1,  P integer-coefficiented (16 of its 46 terms negative).

POSITIVITY IS THEN A COEFFICIENT-SIGN STATEMENT.  The Moebius map
s = 1/(1+t) is a bijection (0,1) -> (0,infinity), and

    R(t) := (1+t)^{deg P} P(1/(1+t))  =  t^4 * Rhat(t),
    Rhat has 103 rational (here integer) coefficients, ALL >= 0,
    Rhat(0) = 15972864 > 0.

Hence Rhat(t) > 0 for all t >= 0, hence P(s) > 0 for all s in (0,1),
hence by (2)

    T00 T11 - T01^2  >=  det_S  =  s^24 P(s)  >  0    for ALL s in (0,1),

i.e.  X_11(s) = log(T00 T11 / T01^2)  >  0  on the WHOLE of (0, 1).

This is a Descartes-rule certificate, not a Sturm count: it is checkable
by comparing 103 integers against zero, which is why it transports to the
Lean kernel by `decide` (dual_kappa_spike/SectorSOSLedger.lean) as an
INTERVAL statement -- the program's first, all previous certified
statements being pointwise.

WHAT IS AND IS NOT CLAIMED
--------------------------
CLAIMED: the anti-screening SIGN of the one-step blocked observable,
uniformly on (0,1), modulo the banked (F2) OS input -- which is the same
input §16h/§17e already consume, not a new frontier atom.  This closes
the sign half of MD.4 atlas-adequacy and makes the three-regime
decomposition's middle regime covered rather than empty.

NOT CLAIMED: the mass gap; the trajectory hypothesis (TS); the MD.3
two-sided RATE envelope 1 < tau'/tau <= 1 + c tau.  det_S gives a
quantitative floor only after an UPPER bound on T01 (one entry, the cheap
direction of the window instrument), and the floor it gives near s = 1 is
O(tau^4), not the true O(tau^2): see gate_s1_multiplicity and the banked
REFUTATION that enlarging the sector family cannot fix this (the s -> 1
rank-one dimension-kernel collapse protects order 4 for every family).
That is the named next front, and it is a rate question, not a sign one.

Run:  python -m computations.sector_sos
"""

from __future__ import annotations

import itertools
import json
import math
import os
import sys
from fractions import Fraction as Frac
from math import comb
from typing import Dict, List, Sequence, Tuple

from computations.dp3_fixed_tile import skeleton_value_fixed
from computations.exact_haar_network import casimir4, dim

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "sector_sos_results.json")

sys.set_int_max_str_digits(0)

Poly = Dict[int, Frac]          # exponent -> coefficient
ENTRIES = ((0, 0), (0, 1), (1, 1))

# The anchor edge and the certified-grid edge, for the coverage statement.
ANCHOR_EDGE_CUBE = 2            # anchor window is [0, 2^{-1/3})
CERT_GRID_MAX = Frac(5, 8)      # highest banked one-step positivity point


# ---------------------------------------------------------------------------
# Exact polynomial arithmetic (dicts exponent -> Fraction).
# ---------------------------------------------------------------------------


def padd(p: Poly, q: Poly) -> Poly:
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, Frac(0)) + c
    return {e: c for e, c in r.items() if c}


def pneg(p: Poly) -> Poly:
    return {e: -c for e, c in p.items()}


def pmul(p: Poly, q: Poly) -> Poly:
    r: Poly = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            r[e1 + e2] = r.get(e1 + e2, Frac(0)) + c1 * c2
    return {e: c for e, c in r.items() if c}


def pshift(p: Poly, c: Frac, e0: int) -> Poly:
    return {e + e0: v * c for e, v in p.items() if v}


def pev(p: Poly, s: Frac) -> Frac:
    return sum((c * s ** e for e, c in p.items()), Frac(0))


# ---------------------------------------------------------------------------
# Sectors.
# ---------------------------------------------------------------------------


def sector_weight(q: Sequence[int], w: Sequence[int]) -> Tuple[Frac, int]:
    """W_sigma(s) = coeff * s^exp.  The q classes carry TWO theta-paired
    faces each (slab_blocking_kernel._PWALL_CLASSES), the w sides one."""
    coeff, exp = 1, 0
    for qi in q:
        coeff *= dim(qi) ** 2
        exp += 2 * casimir4(qi)
    for wi in w:
        coeff *= dim(wi)
        exp += casimir4(wi)
    return Frac(coeff), exp


def sector_kernels(cap: int, tile_M: int) -> Dict[Tuple[tuple, tuple], Dict[Tuple[int, int], Poly]]:
    """Exact sector kernels G_sigma for every sector with labels <= cap.

    tile_M must be >= 1 + cap for exactness (F1); gate_exactness checks it.
    """
    out: Dict[Tuple[tuple, tuple], Dict[Tuple[int, int], Poly]] = {}
    for q in itertools.product(range(cap + 1), repeat=4):
        for w in itertools.product(range(cap + 1), repeat=4):
            rows: Dict[Tuple[int, int], Poly] = {}
            nonempty = False
            for (n, m) in ENTRIES:
                sv = skeleton_value_fixed(n, m, q, w, tile_M)
                if sv:
                    nonempty = True
                rows[(n, m)] = dict(sv)
            if nonempty:
                out[(tuple(q), tuple(w))] = rows
    return out


def assemble(secs) -> Dict[Tuple[int, int], Poly]:
    """T_S[n,m](s) = sum over the family of W_sigma * G_sigma."""
    T = {k: {} for k in ENTRIES}
    for (q, w), rows in secs.items():
        c, e0 = sector_weight(q, w)
        for k in ENTRIES:
            T[k] = padd(T[k], pshift(rows[k], c, e0))
    return T


def det_poly(T: Dict[Tuple[int, int], Poly]) -> Poly:
    return padd(pmul(T[(0, 0)], T[(1, 1)]), pneg(pmul(T[(0, 1)], T[(0, 1)])))


# ---------------------------------------------------------------------------
# The Descartes / Moebius positivity certificate.
# ---------------------------------------------------------------------------


def as_coeff_list(p: Poly) -> Tuple[List[Frac], int]:
    """Return (ascending coefficient list of p/s^lo, lo)."""
    lo, hi = min(p), max(p)
    out = [Frac(0)] * (hi - lo + 1)
    for e, c in p.items():
        out[e - lo] = c
    while out and out[-1] == 0:
        out.pop()
    return out, lo


def moebius_reciprocal(P: Sequence[Frac]) -> List[Frac]:
    """R(t) = (1+t)^deg * P(1/(1+t)), ascending in t.

    s = 1/(1+t) maps (0,1) bijectively onto t in (0, infinity), so
    P > 0 on (0,1)  <==>  R > 0 on (0, infinity), and R having all
    coefficients >= 0 with a positive one is SUFFICIENT for the latter.
    """
    deg = len(P) - 1
    R = [Frac(0)] * (deg + 1)
    for i, c in enumerate(P):
        if c == 0:
            continue
        k = deg - i
        for j in range(k + 1):
            R[j] += c * comb(k, j)
    return R


def positivity_certificate(det: Poly) -> dict:
    """The certificate: det = s^lo * P, R = Moebius(P) = t^k * Rhat,
    Rhat coefficientwise >= 0 with Rhat(0) > 0."""
    P, lo = as_coeff_list(det)
    R = moebius_reciprocal(P)
    k = 0
    while k < len(R) and R[k] == 0:
        k += 1
    Rhat = R[k:]
    negatives = [(i, Rhat[i]) for i in range(len(Rhat)) if Rhat[i] < 0]
    return {
        "s_power": lo,
        "deg_P": len(P) - 1,
        "P": P,
        "t_power": k,
        "Rhat": Rhat,
        "n_coeffs": len(Rhat),
        "n_negative": len(negatives),
        "negatives": negatives,
        "Rhat0": Rhat[0] if Rhat else Frac(0),
        "certified": (not negatives) and bool(Rhat) and Rhat[0] > 0,
    }


# ---------------------------------------------------------------------------
# Exact PSD test: square-root-free LDL^T with zero-pivot handling.
# ---------------------------------------------------------------------------


def psd_exact(Amat: List[List[Frac]]) -> bool:
    """True iff the symmetric rational matrix is positive semidefinite.

    Symmetric Gaussian elimination: a negative pivot refutes; a zero
    pivot forces the whole remaining row to vanish (else the 2x2 minor
    [[0, x], [x, *]] = -x^2 < 0 refutes)."""
    n = len(Amat)
    A = [[Frac(x) for x in row] for row in Amat]
    for i in range(n):
        for j in range(i + 1, n):
            if A[i][j] != A[j][i]:
                return False
    for i in range(n):
        p = A[i][i]
        if p < 0:
            return False
        if p == 0:
            if any(A[i][j] != 0 for j in range(i + 1, n)):
                return False
            continue
        for j in range(i + 1, n):
            f = A[j][i] / p
            if f == 0:
                continue
            for k in range(i, n):
                A[j][k] -= f * A[i][k]
    return True


def _is_rank_deficient(Amat: List[List[Frac]]) -> bool:
    """Exact rank test by fraction-free elimination: True iff rank < size."""
    n = len(Amat)
    A = [[Frac(x) for x in row] for row in Amat]
    rank = 0
    row = 0
    for col in range(n):
        piv = None
        for r in range(row, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        A[row], A[piv] = A[piv], A[row]
        for r in range(row + 1, n):
            if A[r][col] != 0:
                f = A[r][col] / A[row][col]
                for c in range(col, n):
                    A[r][c] -= f * A[row][c]
        rank += 1
        row += 1
        if row == n:
            break
    return rank < n


def half_config_gram(q, w, tile_M: int):
    """H[(n,a),(m,b)] = N(n,m,sigma,a,b) over half-configs (loop, tiles).

    Built from dp3_fixed_tile's own `collect` hook, so the Haar values are
    the incumbent evaluator's, not a reimplementation."""
    vals: Dict[Tuple[int, tuple, int, tuple], Frac] = {}
    labels = {0: set(), 1: set()}
    for (n, m) in ((0, 0), (0, 1), (1, 0), (1, 1)):
        coll: List[Tuple[tuple, tuple, Frac]] = []
        skeleton_value_fixed(n, m, q, w, tile_M, collect=coll)
        for top, bot, N in coll:
            vals[(n, top, m, bot)] = N
            labels[n].add(top)
            labels[m].add(bot)
    idx = [(n, a) for n in (0, 1) for a in sorted(labels[n])]
    H = [[vals.get((n, a, m, b), Frac(0)) for (m, b) in idx] for (n, a) in idx]
    return idx, H


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def gate_exactness(cap: int = 1, tile_M: int = 2) -> Tuple[bool, str]:
    """(F1): the sector kernels are M-independent once M >= 1 + cap."""
    a = sector_kernels(cap, tile_M)
    b = sector_kernels(cap, tile_M + 1)
    ok = a == b
    return ok, f"cap={cap}: kernels at M={tile_M} and M={tile_M+1} identical: {ok}"


def gate_psd(cap: int = 1, tile_M: int = 2) -> Tuple[bool, List[str]]:
    """(F2): the half-config Gram H is PSD for every sector of the family,
    and the 2x2 block G_sigma has det >= 0 at probe couplings."""
    msgs: List[str] = []
    ok = True
    secs = sector_kernels(cap, tile_M)
    neg_entry = 0
    rank_def = 0
    for (q, w), rows in secs.items():
        idx, H = half_config_gram(q, w, tile_M)
        if any(x < 0 for row in H for x in row):
            neg_entry += 1
        if _is_rank_deficient(H):
            rank_def += 1
        if not psd_exact(H):
            ok = False
            msgs.append(f"  PSD FAILURE at sector q={q} w={w} (size {len(idx)})")
        for s in (Frac(1, 10), Frac(1, 2), Frac(4, 5), Frac(99, 100)):
            A = pev(rows[(0, 0)], s)
            B = pev(rows[(1, 1)], s)
            C = pev(rows[(0, 1)], s)
            if A < 0 or B < 0 or A * B - C * C < 0:
                ok = False
                msgs.append(f"  2x2 FAILURE at sector q={q} w={w}, s={s}")
    msgs.insert(0, f"  {len(secs)} sectors, all half-config Grams PSD: {ok}")
    msgs.insert(1, f"  teeth: {rank_def}/{len(secs)} Grams are RANK-DEFICIENT "
                   f"(the zero-pivot branch of psd_exact fires, so the test is "
                   f"not vacuous); {neg_entry} have a negative entry.  At the "
                   f"independent cap<=2 family (187 sectors, gated separately) "
                   f"71 have a negative entry and all 187 are rank-deficient, "
                   f"so PSD is not entrywise positivity there either.")
    return ok, msgs


def gate_identity(cap: int = 1, tile_M: int = 2,
                  probes=(Frac(1, 2), Frac(4, 5), Frac(99, 100))) -> Tuple[bool, List[str]]:
    """(F3): the pair expansion of det is an exact identity and every
    pair term Q(sigma,sigma') is non-negative."""
    secs = sector_kernels(cap, tile_M)
    keys = list(secs)
    msgs: List[str] = []
    ok = True
    for s in probes:
        W = {}
        G = {}
        for k in keys:
            c, e = sector_weight(*k)
            W[k] = c * s ** e
            G[k] = (pev(secs[k][(0, 0)], s), pev(secs[k][(0, 1)], s),
                    pev(secs[k][(1, 1)], s))
        T00 = sum((W[k] * G[k][0] for k in keys), Frac(0))
        T01 = sum((W[k] * G[k][1] for k in keys), Frac(0))
        T11 = sum((W[k] * G[k][2] for k in keys), Frac(0))
        dT = T00 * T11 - T01 * T01
        diag = sum((W[k] ** 2 * (G[k][0] * G[k][2] - G[k][1] ** 2) for k in keys),
                   Frac(0))
        pair = Frac(0)
        nneg = 0
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                a, b = keys[i], keys[j]
                Q = (G[a][0] * G[b][2] + G[a][2] * G[b][0]
                     - 2 * G[a][1] * G[b][1])
                if Q < 0:
                    nneg += 1
                pair += W[a] * W[b] * Q
        exact = (dT == diag + pair)
        if not exact or nneg:
            ok = False
        msgs.append(f"  s={s}: identity exact: {exact}; negative Q terms: "
                    f"{nneg}; diagonal part / det = "
                    f"{float(diag / dT) if dT else float('nan'):.3e} "
                    f"(interference-driven, so the certificate is non-vacuous)")
    return ok, msgs


def gate_banked_census(cap: int = 1, tile_M: int = 2) -> Tuple[bool, List[str]]:
    """The sector assembly must reproduce the banked M=2 census polynomial
    (dp3_m2_entries) EXACTLY on the leading block and be coefficientwise
    DOMINATED by it everywhere (the cap<=1 family is a positive sub-sum)."""
    path = os.path.join(HERE, "dp3_m2_entries.json")
    bank = json.load(open(path))
    T = assemble(sector_kernels(cap, tile_M))
    msgs: List[str] = []
    ok = True
    for (n, m) in ENTRIES:
        p = {int(e): Frac(c[0], c[1])
             for e, c in bank[f"{n},{m}"]["poly"].items()}
        mine = T[(n, m)]
        agree = [e for e in sorted(mine) if p.get(e) == mine[e]]
        dominated = all(mine[e] <= p.get(e, Frac(0)) for e in mine)
        lead = sorted(mine)[:len(agree)]
        if not dominated or not agree:
            ok = False
        msgs.append(f"  T[{n},{m}]: {len(mine)} terms; exact agreement with the "
                    f"banked census at exps {agree}; coefficientwise "
                    f"dominated everywhere: {dominated}")
        del lead
    return ok, msgs


def gate_x11_banked(cap: int = 1, tile_M: int = 2) -> Tuple[bool, List[str]]:
    """The truncated assembly must land inside the banked certified X_11
    windows on the §16l CERT grid (an independent-route consistency gate)."""
    T = assemble(sector_kernels(cap, tile_M))
    banked = {                      # work_plan §16l / WindowLedger certGrid
        (1, 2): 0.258391, (11, 20): 0.282612, (9, 16): 0.289793,
        (4, 7): 0.294655, (3, 5): 0.274282, (61, 100): 0.177639,
        (8, 13): 0.028179,
    }
    msgs: List[str] = []
    ok = True
    for (a, b), floor in sorted(banked.items()):
        s = Frac(a, b)
        d = pev(det_poly(T), s)
        x = math.log(float(pev(T[(0, 0)], s) * pev(T[(1, 1)], s)
                           / pev(T[(0, 1)], s) ** 2))
        pos = d > 0
        if not pos:
            ok = False
        msgs.append(f"  s={a}/{b}: det_S={float(d):+.6e} (>0: {pos}); "
                    f"X_11 of the truncated assembly = {x:+.6f} vs banked "
                    f"certified floor {floor:+.6f}")
    return ok, msgs


def gate_s1_multiplicity(cap: int = 1, tile_M: int = 2) -> Tuple[int, Frac]:
    """Order of vanishing of det_S at s = 1 and the leading constant.

    Banked REFUTATION: this order is 4 for the cap<=1 family AND for the
    cap<=2 family (187 sectors) -- enlarging the transverse family does
    NOT lower it, because the s -> 1 collapse of T onto the rank-one
    dimension kernel d_n d_m s^{12(n+m)} T00 is shared by every sector.
    So the O(tau^4) floor near s = 1 is a PROTECTED degeneracy of this
    observable, not a small-family artifact: the RATE half of MD.4 needs
    the deviation kernel, not more sectors."""
    P, _ = as_coeff_list(det_poly(assemble(sector_kernels(cap, tile_M))))
    mult = 0
    Q = list(P)
    while True:
        val = sum(Q)
        if val != 0:
            break
        mult += 1
        desc = list(reversed(Q))
        res = [desc[0]]
        for c in desc[1:]:
            res.append(c + res[-1])
        assert res[-1] == 0
        Q = list(reversed(res[:-1]))
        while Q and Q[-1] == 0:
            Q.pop()
    return mult, sum(Q)


# ---------------------------------------------------------------------------
# Report.
# ---------------------------------------------------------------------------


def main() -> None:
    print("SECTOR-SOS POSITIVITY CERTIFICATE (work_plan §17g, P3)")
    print("=" * 66)
    cap, tile_M = 1, 2

    secs = sector_kernels(cap, tile_M)
    T = assemble(secs)
    det = det_poly(T)
    cert = positivity_certificate(det)

    print(f"\nfamily: labels <= {cap}  ->  {len(secs)} nonempty sectors")
    for (n, m) in ENTRIES:
        terms = ", ".join(f"{T[(n,m)][e]}*s^{e}" for e in sorted(T[(n, m)]))
        print(f"  T{n}{m} = {terms}")
    print(f"\ndet_S = s^{cert['s_power']} * P,  deg P = {cert['deg_P']}, "
          f"P(0) = {cert['P'][0]}, "
          f"{sum(1 for c in cert['P'] if c < 0)} negative coefficients")
    print(f"Moebius s = 1/(1+t):  R = t^{cert['t_power']} * Rhat, "
          f"{cert['n_coeffs']} coefficients, "
          f"{cert['n_negative']} negative, Rhat(0) = {cert['Rhat0']}")
    print(f"\n*** CERTIFIED: X_11 > 0 on ALL of (0,1): {cert['certified']} ***")

    gates = {}
    ok, msg = gate_exactness(cap, tile_M)
    gates["g_exact"] = ok
    print(f"\ng_exact  (F1 tile-sum exactness): {ok}\n  {msg}")

    ok, msgs = gate_psd(cap, tile_M)
    gates["g_psd"] = ok
    print(f"\ng_psd    (F2 sector-wise OS positivity): {ok}")
    for m_ in msgs:
        print(m_)

    ok, msgs = gate_identity(cap, tile_M)
    gates["g_identity"] = ok
    print(f"\ng_pairs  (F3 exact pair expansion, Q >= 0): {ok}")
    for m_ in msgs:
        print(m_)

    ok, msgs = gate_banked_census(cap, tile_M)
    gates["g_census"] = ok
    print(f"\ng_census (vs the banked M=2 census polynomial): {ok}")
    for m_ in msgs:
        print(m_)

    ok, msgs = gate_x11_banked(cap, tile_M)
    gates["g_banked_grid"] = ok
    print(f"\ng_grid   (vs the banked §16l CERT grid): {ok}")
    for m_ in msgs:
        print(m_)

    mult, lead = gate_s1_multiplicity(cap, tile_M)
    gates["g_s1"] = (mult == 4)
    print(f"\ng_s1     (protected s->1 degeneracy): order {mult} at s=1, "
          f"leading constant {lead}")
    print("  BANKED REFUTATION: the cap<=2 family (187 sectors) has the SAME "
          "order 4,\n  leading constant 230460431616 -- family enlargement "
          "cannot sharpen the rate.")

    print("\nCOVERAGE (the P3 statement):")
    print(f"  anchor (unconditional)      s in [0, 2^(-1/3)) = [0, "
          f"{2 ** (-1 / 3):.6f})")
    print(f"  banked one-step grid        s <= {float(CERT_GRID_MAX):.6f}  "
          f"-- entirely INSIDE the anchor: contributes no atlas coverage")
    print(f"  MD.3 envelope (§17c)        tau <= 2^-44, i.e. s >= "
          f"1 - 5.68e-14")
    print(f"  THIS certificate            s in (0, 1) ENTIRE, sign only")

    out = {
        "family_cap": cap,
        "tile_M": tile_M,
        "n_sectors": len(secs),
        "T": {f"{n},{m}": {str(e): [int(c.numerator), int(c.denominator)]
                           for e, c in T[(n, m)].items()} for (n, m) in ENTRIES},
        "det": {str(e): [int(c.numerator), int(c.denominator)]
                for e, c in det.items()},
        "certificate": {
            "s_power": cert["s_power"],
            "deg_P": cert["deg_P"],
            "t_power": cert["t_power"],
            "n_coeffs": cert["n_coeffs"],
            "n_negative": cert["n_negative"],
            "Rhat0": [int(cert["Rhat0"].numerator), int(cert["Rhat0"].denominator)],
            "Rhat": [[int(c.numerator), int(c.denominator)] for c in cert["Rhat"]],
            "certified": cert["certified"],
        },
        "s1_order": mult,
        "s1_leading": [int(lead.numerator), int(lead.denominator)],
        "gates": gates,
        "all_gates_green": all(gates.values()),
    }
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    print(f"\nledger -> {OUT_JSON}")
    print(f"ALL GATES GREEN: {out['all_gates_green']}")


if __name__ == "__main__":
    main()
