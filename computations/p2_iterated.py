"""P2 — the ITERATED-MAP WINDOWS (work_plan §17.3 P2, §17c next
attack): certified two-step (twice-blocked) kernel windows, the
structural vacuity theorem for the raw two-step sign, and the first
certified trajectory-level numbers, with the U(1) mirror lane exact.

THE OBJECT
----------
One blocking step is the banked slab kernel matrix T[n, m](s) — the
character-basis pair moments (Fourier coefficients of the owned-
boundary kernel in the orthonormal characters chi_n).  The iterated
map is kernel COMPOSITION through the shared boundary charge:

    T_2[n, m](s) = sum_k T[n, k](s) T[k, m](s),

g_k = 1 by character orthonormality (SU(2): k = 0, 1, 2, ...;
U(1): k in Z).  This is the transfer-semigroup square — the
two-step trajectory object the (TS) hypothesis constrains.

THE STRUCTURAL THEOREM (the raw sign is VACUOUS at two steps)
-------------------------------------------------------------
T is real symmetric, so T_2 = T^2 is a GRAM matrix (T_2[n, m] =
<row_n, row_m>), and Cauchy-Schwarz gives

    X^{(2)} := log( T_2[1,1] T_2[0,0] / T_2[0,1]^2 )  >=  0

for EVERY group — abelian included.  The §17.4 mirror fence
therefore FIRES on the raw two-step cross sign: it cannot
discriminate SU(2) from U(1).  (Banked as a refutation-grade design
fact: at even iteration depth the discriminating content is the
MAGNITUDE/matched-flow structure, not the sign.)  The U(1) lane
below confirms it quantitatively: the exact abelian X^{(2)} is
certified POSITIVE while the one-step abelian cross is negative.

WHAT THE MAGNITUDE MEASURES
---------------------------
Writing T = sum_i lambda_i phi_i phi_i^T (spectral), T_2 = sum
lambda_i^2 ...: the two-step Gram angle between rows 0 and 1 is a
spectral-ratio readout — for a gapped two-channel structure
X^{(2)} ~ (lambda_1/lambda_0)^2-scaled geometry, i.e. the certified
X^{(2)} window is a certified statement about the TRAJECTORY of the
gap under iteration.  At s = 1/2 the SU(2) kernel's composition is
dominated by the k = 0 channel and X^{(2)} collapses by ~7 orders
against X^{(1)} — the rank-one collapse of a strongly gapped step,
now certified at depth 2.

CERTIFICATION
-------------
SU(2) entries: the §16h-16l combined assembly (M = 2 census +
finality/CS-sharpened U_2 for the (0,0),(0,1),(1,1) entries; crude
labelled masses else; label-less unreached configs of (2,2) bounded
by the certified d-absorption prod(d-factors) <= 4^{E/3} — valid
since d(j)^2 <= 4^{C(j)/3} and d(q)^4 <= 4^{2C(q)/3}; level-3 CS
tails; domination-transfer levels >= 4 with Lambda-slop).  The
k >= 3 composition tail uses |T[n, k]| <= d_n d_k (full dominated
trace + slop) from DomTransfer per k <= 8, and for k >= 9 the
analytic corner floor: every labelling with boundary charge k pays,
at each of the four corners, node weight d_b^2 d_q^4
s^{C(b) + 2 C(q)} with triad b >= |k - q|, so with the d-absorption
above each corner is <= (4^{1/3} s)^{f(k)}, f(k) = min_q (2 C(q) +
C(|k - q|)) (exact scan), and 4^{1/3} s < 1 on the CERT range
s <= 8/13; the remaining factors close by the geometric sums of
su2_minf_windows.  All interval arithmetic exact-rational; the
certified object is the rational ratio window (logs are floats for
presentation only, per the banked convention).

U(1) lane: theta_window certified entries (all integer charges,
negative included), k-tail closed by T[n, k] <= s^{qmin(n, k)}
W-bar(s), W-bar = [3 + 2 sum_{j >= 2} s^{4 (j-1)^2}]^4 (lambda_min(A)
= 4, banked spectrum), qmin(n, k) = 3 n^2 + 3 k^2 + 2 n k exact.
The continuum two-step form Qmin_2(n, m) = 3 (n^2 + m^2) -
(n + m)^2 / 6 (exact minimization over the shared real charge) gives
the small-tau prediction X^{(2)}_U1 -> +tau/3 — sign-FLIPPED from
the one-step -2 tau — gated against the certified windows at
s = 9/10 (four-digit agreement).

THE SOS/LAGRANGE LAYER (work_plan §17e: the depth-2 sign certified
------------------------------------------------------------------
on the whole CERT grid).  The first release computed the ratio
window entrywise from the T_2 windows and lost the Gram
correlation: differencing two nearly equal products through
~1e-6-wide one-step windows left the sign uncertified at
s = 11/20 and 9/16.  But the two-step determinant is an exact
SUM OF SQUARES of one-step 2x2 minors (Lagrange / Cauchy-Binet,
valid for the absolutely convergent k-sum):

    det_2 := T_2[0,0] T_2[1,1] - T_2[0,1]^2
           = sum_{k < l} M_kl^2,
    M_kl := T[0,k] T[1,l] - T[0,l] T[1,k],

every term nonnegative — so ANY finite subfamily of minors gives a
certified lower bound, and the LEADING minor M_01 = T00 T11 - T01^2
is exactly the one-step X_11 object, already certified positive on
the whole §16l CERT grid.  With  X^{(2)} = log(1 + det_2 /
T_2[0,1]^2)  this converts the certified ONE-step gap directly into
a certified TWO-step sign:

    r_lo = 1 + max(0, M01_lo)^2 / T2_01_hi^2  >  1,

no new diagonal values needed — the mechanical fix anticipated in
§17d (background-diagonal tightening) is SUPERSEDED for the sign by
this structural route; landed diagonals now only sharpen magnitudes.
The same identity gives the sharp upper bound: det_2 <= (banked
minors at their window maxima) + (dominated cross pairs, k <= 2 <
l <= 8, via |M_kl| <= U0k U1l + U0l U1k with U the certified
per-index bounds) + (crude pairs, geometric closure at l >= 9),
r_hi = 1 + det2_hi / T2_01_lo^2 — this collapses the interval-
differencing slop (e.g. 4.1e-3 -> ~1.6e-5 at s = 11/20).

Two repairs banked with this layer (honesty first):
(R1) the first release's T_2 LOWER bounds dropped possibly-negative
     k <= 2 contributions (entry windows straddling 0) and the
     k >= 3 tail from the OFF-diagonal entry — sound for the
     diagonal entries (squares) but not for T_2[0,1].  Repaired:
     interval products for every k <= 2 term and the tail
     subtracted on the lo side of the off-diagonal.  Effect
     ~6e-10 absolute at s = 11/20 (below every banked digit —
     no banked claim changes; the ledger is regenerated).
(R2) crude_high_k closed its label sums with sum_pow2(0, s); the
     same certified sum anchored at K = 4 (exact partial + tail)
     is ~7 orders tighter at s = 8/13 and shrinks the k-truncation
     tail there from ~1.8e15 to ~1e2 — still uninformative for the
     8/13 magnitude (the closure remains the wall), but it keeps
     every other point clean.

GATES
-----
  g_sym       T and T_2 windows symmetric; U(1) qmin identities
              (qmin(1,1) = 8, qmin(1,-1) = 4, symmetry).
  g_cs        certified ratio windows >= 1 in BOTH lanes (the
              structural theorem, machine-checked; the U(1) one-step
              cross stays certified NEGATIVE at the same s — the
              sign flip is real, not numerical).
  g_hk        heat-kernel semigroup toy: a diagonal kernel
              T[n, m] = delta e^{-tau C(n)} composes to exact
              doubling under the same code path.
  g_u1_law    the certified U(1) X^{(2)} window at s = 9/10
              brackets the continuum +tau/3 law within an explicit
              band (and is positive; the measured value agrees with
              tau/3 to four digits).
  g_scale     the SU(2) X^{(2)} at s = 1/2 sits 6-8 orders below
              X^{(1)} (rank-one collapse pin, window-certified).
  g_lagrange  the Lagrange/Cauchy-Binet identity replayed EXACTLY
              (rationals) on a dense symmetric test matrix through
              the same minor code path.
  g_oscs      the entry-level OS Gram inequality checked in its
              necessary window form on BOTH lanes — exactly on the
              abelian theta windows (charges 0..3), and on every
              SU(2) entry-window set consumed.
  g_sign      the depth-2 sign certified (r_lo > 1) at every point
              of the §16l CERT grid — 1/2 through 8/13.
  g_consist   the SOS and entrywise windows intersect at every
              grid point (two certified routes to one truth).

HONESTY
-------
One composition step of the banked one-step kernel; thickness-one
anisotropic slabs composed in the transfer direction.  The (·,2)
entry windows are crude (label-less (2,2) unreached masses dominate
them) — they enter only at the 1e-13 level of the composition at the
CERT points, far below the leading windows.  The l >= 9 crude
closures are now CLOSED-FORM: exact segment sums to the adaptive
anchor L(s), then the geometric tail licensed by the PROVEN uniform
cube-ratio bound (corner-floor convexity sandwich f_real <= f <=
f_real + 3, hence df(l) >= (4l+1)/3, hence (c(l+1)/c(l))^3 <=
((L+2)/(L+1))^3 64 (4s^3)^{ceil((4L+1)/3)} <= 1/8 for l >= L) —
this UPGRADES the module family's checked-ratio closure convention
to a theorem-grade closure; the sandwich instances are asserted at
every evaluation.
The certified SIGN claims depend only on the banked window
technology (M01 through the one-step windows and the T2_01 upper
bound); the closure convention enters magnitudes only.  The two-step object is
the composition of the DERIVED kernels; re-deriving it from a
thickness-2 fine-scale census (the blocking-vs-stacking defect) is
the next rung and precisely the §16 defect-analysis frame.  The
matched-flow form (tau'/tau windows at depth 2, MD.1 matchings) is
the designated consumer of these windows and is not claimed here.

Run:  python -m computations.p2_iterated
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

from computations.su2_cs_tail import level3_tail, load_diag
from computations.su2_m2_finality import cs_sharpened_u2
from computations.su2_minf_windows import (
    DomTransfer,
    cas4,
    dim,
    load_m2,
    sum_pow2,
)
from computations.u1_theta_kernel import qmin, theta_window

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "p2_iterated_results.json")

CERT_S = (Frac(1, 2), Frac(11, 20), Frac(9, 16), Frac(4, 7),
          Frac(3, 5), Frac(61, 100), Frac(8, 13))
K_BANKED = 2          # census boundary charges 0..2
K_DOM = 8             # DomTransfer bounds for 3..K_DOM
LAM = 8


# ---------------------------------------------------------------------------
# Exact interval helpers (rational endpoints).
# ---------------------------------------------------------------------------


def iv_mul(a: tuple[Frac, Frac], b: tuple[Frac, Frac]
           ) -> tuple[Frac, Frac]:
    """Product window of two INDEPENDENT interval quantities."""
    c = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(c), max(c))


def iv_square(a: tuple[Frac, Frac]) -> tuple[Frac, Frac]:
    """Window of x^2 for x in [a0, a1] — the DEPENDENT square (used
    where both factors are the same entry, e.g. T01^2)."""
    lo, hi = a
    m = max(abs(lo), abs(hi))
    if lo > 0:
        return (lo * lo, m * m)
    if hi < 0:
        return (hi * hi, m * m)
    return (Frac(0), m * m)


# ---------------------------------------------------------------------------
# SU(2) entry windows (generalized combined assembly).
# ---------------------------------------------------------------------------


def _census_value_and_crude(d: dict, key: str, n: int, m: int,
                            s: Frac) -> tuple[Frac, Frac]:
    """Census polynomial value + certified crude mass of unreached
    configs; label-less configs (the (2,2) list) bounded by the
    d-absorption prod(d-factors) <= 4^{ceil(E/3)}."""
    poly = {int(k): Frac(v[0], v[1]) for k, v in d[key]["poly"].items()}
    val = sum((c * s ** k for k, c in poly.items()), Frac(0))
    u = Frac(0)
    for cfg in d[key]["unreached"]:
        if "q" in cfg:
            mass = Frac(dim(n) * dim(m))
            for q in cfg["q"]:
                mass *= Frac(dim(q) ** 4) * s ** (2 * cas4(q))
            for w in cfg["w"]:
                mass *= Frac(dim(w) ** 2) * s ** cas4(w)
            for a in cfg["top"]:
                mass *= Frac(dim(a) ** 2) * s ** cas4(a)
            for b in cfg["bot"]:
                mass *= Frac(dim(b) ** 2) * s ** cas4(b)
        else:
            e = cfg["E"]
            mass = Frac(dim(n) * dim(m)) * Frac(4) ** ((e + 2) // 3) \
                * s ** e
        u += mass
    return val, u


_SHARPENED = {"0,0": (0, 0), "0,1": (0, 1), "1,1": (1, 1)}
_CRUDE = {"0,2": (0, 2), "1,2": (1, 2), "2,2": (2, 2)}


def entry_windows(s: Frac) -> dict[tuple[int, int], tuple[Frac, Frac]]:
    """Certified [lo, hi] for T[n, m](s), (n, m) in {0,1,2}^2 (by
    symmetry only n <= m stored; window symmetric)."""
    d = load_m2()
    diag = load_diag()
    out: dict[tuple[int, int], tuple[Frac, Frac]] = {}
    for key, (n, m) in {**_SHARPENED, **_CRUDE}.items():
        val, u_crude = _census_value_and_crude(d, key, n, m, s)
        if key in _SHARPENED:
            add, resid, _n_res, _n_cs = cs_sharpened_u2(key, n, m, s)
            val, u = val + add, resid
        else:
            u = u_crude
        lvl3, _used, _ncfg = level3_tail(n, m, s, diag)
        dt = DomTransfer(n, m, s, LAM)
        rest = dt.dominated_trace(LAM) - dt.dominated_trace(3)
        assert rest >= 0
        tail = lvl3 + rest + dt.lam_slop()
        out[(n, m)] = (val - u - tail, val + u + tail)
    return out


_DOM_CACHE: dict[tuple[int, int, Frac], Frac] = {}


def dom_bound(n: int, k: int, s: Frac) -> Frac:
    """|T[n, k]| <= d_n d_k (full dominated trace + slop); cached
    (the DomTransfer trace is the expensive object)."""
    key = (n, k, s)
    if key not in _DOM_CACHE:
        dt = DomTransfer(n, k, s, LAM)
        _DOM_CACHE[key] = Frac(dim(n) * dim(k)) \
            * (dt.dominated_trace(LAM) + dt.lam_slop())
    return _DOM_CACHE[key]


def corner_floor(k: int) -> int:
    """f(k) = min_{0 <= q <= k} (2 C(q) + C(k - q)) (exact scan).

    Real-relaxation sandwich (both sides PROVED, instances asserted
    in crude_high_k): the real minimizer of g(q) = 2C(q) + C(k-q)
    is q* = (k-1)/3 with value f_real(k) = (2k^2 + 8k - 1)/3, and
    g'' = 6, so the integer minimum is within 3 (offset <= 1):

        f_real(k)  <=  f(k)  <=  f_real(k) + 3.

    Consequence used by the tail closure: f(k+1) - f(k) >=
    f_real(k+1) - f_real(k) - 3 = (4k + 1)/3 for EVERY k — the
    superexponential decay of crude_high_k with a uniform, provable
    increment floor."""
    return min(2 * cas4(q) + cas4(k - q) for q in range(k + 1))


def crude_high_k(n: int, k: int, s: Frac) -> Frac:
    """Analytic bound for k >= 9: four corners pay (4^{1/3} s)^{f(k)}
    each after d-absorption; the a-side nodes, edges and the n-side
    close by geometric sums.  §17e repair (R2): the closure uses the
    certified label sum anchored at K = 4 (exact partial + tail) in
    place of the K = 0 anchor — the same quantity, a strictly
    tighter certified upper bound (~7 orders at s = 8/13)."""
    assert 4 * s ** 3 < 1           # (4^{1/3} s) < 1, cubed form
    f = corner_floor(k)
    assert 3 * f >= 2 * k * k + 8 * k - 1      # >= f_real
    assert 3 * f <= 2 * k * k + 8 * k - 1 + 9  # <= f_real + 3
    base = Frac(4) ** ((f + 2) // 3) * s ** f
    g = (sum_pow2(4, s)) ** 8       # a-nodes + w-edges, certified closure
    return Frac(dim(n) * dim(k)) * base ** 4 * g


_GEO_ANCHOR: dict[Frac, int] = {}
_ROW_SUMS: dict[tuple[int, Frac], tuple[Frac, Frac, list]] = {}


def geo_anchor(s: Frac) -> int:
    """Smallest L >= 9 such that the PROVEN uniform cube-ratio bound

        (c(l+1)/c(l))^3 <= ((L+2)/(L+1))^3 * 64 * (4 s^3)^{ceil(
                            (4L+1)/3)}  =:  r^3   for every l >= L

    satisfies r^3 <= 1/8, i.e. r <= 1/2.  Provenance (all exact):
    c(l+1)^3/c(l)^3 = ((l+2)/(l+1))^3 4^{3 dfloor} s^{3 df} with
    3 dfloor <= df + 3 (floor-difference), so the ratio cube is
    <= ((l+2)/(l+1))^3 64 (4s^3)^{df(l)}; df(l) >= (4l+1)/3 by the
    corner_floor sandwich (convexity), 4s^3 < 1, and every factor
    is monotone in l.  This replaces the earlier checked-ratio
    convention with a closed geometric closure valid for the WHOLE
    tail: sum_{l >= L} c(l) <= 2 c(L), sum_{l >= L} c(l)^2 <=
    2 c(L)^2 (ratio <= 1/2, squares <= 1/4)."""
    if s not in _GEO_ANCHOR:
        x = 4 * s ** 3
        assert x < 1
        ell = 9
        while True:
            r3 = Frac((ell + 2) ** 3, (ell + 1) ** 3) * 64 \
                * x ** ((4 * ell + 1 + 2) // 3)
            if r3 <= Frac(1, 8):
                break
            ell += 1
        _GEO_ANCHOR[s] = ell
    return _GEO_ANCHOR[s]


def crude_row_sums(n: int, s: Frac) -> tuple[Frac, Frac, list]:
    """(S, SQ, vals): certified sum_{l >= 9} c(l) <= S and
    sum_{l >= 9} c(l)^2 <= SQ, with vals = the exact c(l) on
    [9, L]; exact segment plus the geo_anchor closure."""
    key = (n, s)
    if key not in _ROW_SUMS:
        big_l = geo_anchor(s)
        vals = [crude_high_k(n, ell, s) for ell in range(9, big_l + 1)]
        seg = sum(vals[:-1], Frac(0))
        seg_sq = sum((v * v for v in vals[:-1]), Frac(0))
        s_tot = seg + 2 * vals[-1]
        sq_tot = seg_sq + 2 * vals[-1] ** 2
        _ROW_SUMS[key] = (s_tot, sq_tot, vals)
    return _ROW_SUMS[key]


def su2_t2_windows(s: Frac, ew: dict | None = None) -> tuple[
        dict[tuple[int, int], tuple[Frac, Frac]], Frac]:
    """Certified windows for T_2[n, m], (n, m) in {0, 1}^2, plus the
    k-truncation tail (reported).  §17e repair (R1): the k <= 2
    terms enter as exact interval products (dependent square on the
    diagonal), and the k >= 3 tail is SUBTRACTED on the lo side of
    the off-diagonal entry — the first release's lo dropped
    possibly-negative contributions there (diagonal entries are sums
    of squares, so dropping k >= 3 stays sound on the lo side)."""
    if ew is None:
        ew = entry_windows(s)

    def w(n: int, m: int) -> tuple[Frac, Frac]:
        return ew[(min(n, m), max(n, m))]

    out: dict[tuple[int, int], tuple[Frac, Frac]] = {}
    max_tail = Frac(0)
    for n in (0, 1):
        for m in (0, 1):
            if (n, m) in out:
                continue
            lo = Frac(0)
            hi = Frac(0)
            for k in range(3):
                if n == m:
                    t = iv_square(w(n, k))
                else:
                    t = iv_mul(w(n, k), w(k, m))
                lo += t[0]
                hi += t[1]
            tail = sum((u_abs_bound(n, k, s, ew)
                        * u_abs_bound(m, k, s, ew)
                        for k in range(3, K_DOM + 1)), Frac(0))
            # l >= 9: exact segment products + the anchored closure
            # (pair ratio <= 1/4 => factor <= 4/3 <= 2)
            _sn, _qn, vn = crude_row_sums(n, s)
            _sm, _qm, vm = crude_row_sums(m, s)
            tail += sum((a * b for a, b in
                         zip(vn[:-1], vm[:-1])), Frac(0)) \
                + 2 * vn[-1] * vm[-1]
            hi += tail
            if n != m:
                lo -= tail          # k >= 3 terms carry unknown sign
            max_tail = max(max_tail, tail)
            out[(n, m)] = (lo, hi)
            out[(m, n)] = (lo, hi)
    return out, max_tail


# ---------------------------------------------------------------------------
# The SOS/Lagrange layer (§17e): det_2 as a sum of one-step minors.
# ---------------------------------------------------------------------------

K_CS = 4    # entry-level OS Gram sharpening for 3 <= j <= K_CS


def entry_diag_hi(n: int, s: Frac, ew: dict) -> Frac:
    """Certified upper bound on the DIAGONAL entry T[n, n] (> 0)."""
    if n <= K_BANKED:
        return ew[(n, n)][1]
    return dom_bound(n, n, s)


def u_abs_bound(n: int, j: int, s: Frac, ew: dict) -> Frac:
    """Certified upper bound on |T[n, j]| per index class.

    For 3 <= j <= K_CS the dominated bound is sharpened by the
    ENTRY-LEVEL OS Gram inequality |T[n, j]| <= sqrt(T[n,n] T[j,j]):
    the slab weight factorizes across the reflection plane
    (W = W_qw(q, w) W_top(a) W_bot(b)), so summing the banked §16h
    config-level OS/CS lemma bilinearly over the shared (q, w)
    sectors exhibits T as a Gram matrix of aggregated half-slab
    states in the Osterwalder-Seiler inner product — the same
    banked reflection argument, applied to the aggregated states
    (machine-gated below: g_oscs, both lanes).  This is the §17c/
    §16h 'image technology' lever, and it is what breaks the
    dom(1,3) wall in the depth-2 magnitude (9.6e-9 -> the true
    minor scale at s = 11/20)."""
    if j <= K_BANKED:
        lo, hi = ew[(min(n, j), max(n, j))]
        return max(abs(lo), abs(hi))
    if j <= K_DOM:
        b = dom_bound(n, j, s)
        if j <= K_CS:
            cs = _cs_sqrt_upper(entry_diag_hi(n, s, ew)
                                * entry_diag_hi(j, s, ew))
            b = min(b, cs)
        return b
    return crude_high_k(n, j, s)


def _cs_sqrt_upper(x: Frac) -> Frac:
    from computations.su2_cs_tail import _sqrt_upper
    return _sqrt_upper(x)


def minor_window(k: int, ell: int, ew: dict) -> tuple[Frac, Frac]:
    """Exact window for M_kl = T[0,k] T[1,l] - T[0,l] T[1,k],
    k < l <= 2; the (0,1) minor uses the dependent square T01^2."""
    def w(n: int, m: int) -> tuple[Frac, Frac]:
        return ew[(min(n, m), max(n, m))]

    a = iv_mul(w(0, k), w(1, ell))
    if (k, ell) == (0, 1):
        b = iv_square(w(0, 1))
    else:
        b = iv_mul(w(0, ell), w(1, k))
    return (a[0] - b[1], a[1] - b[0])


def sos_det2_window(s: Frac, ew: dict) -> tuple[Frac, Frac, dict]:
    """Certified [lo, hi] for det_2 = sum_{k<l} M_kl^2 (Lagrange /
    Cauchy-Binet on the Gram rows; absolute convergence from the
    dominated per-index bounds).  Lower bound: the banked minors
    only (every dropped term is a square >= 0).  Upper bound: banked
    minors at their window maxima + dominated cross pairs + the
    checked geometric closure at l >= 9."""
    lo = Frac(0)
    hi = Frac(0)
    minors = {}
    for k, ell in ((0, 1), (0, 2), (1, 2)):
        m_iv = minor_window(k, ell, ew)
        minors[f"{k},{ell}"] = [float(m_iv[0]), float(m_iv[1])]
        sq = iv_square(m_iv)
        lo += sq[0]
        hi += sq[1]
    u0 = {j: u_abs_bound(0, j, s, ew) for j in range(K_DOM + 1)}
    u1 = {j: u_abs_bound(1, j, s, ew) for j in range(K_DOM + 1)}
    _s0, sq0, _v0 = crude_row_sums(0, s)
    _s1, sq1, _v1 = crude_row_sums(1, s)
    # pairs k <= K_DOM < many: exact through l <= K_DOM ...
    for k in range(K_DOM + 1):
        for ell in range(max(k + 1, 3), K_DOM + 1):
            m = u0[k] * u1[ell] + u0[ell] * u1[k]
            hi += m * m
        # ... then l >= 9 per k <= K_DOM, via (a+b)^2 <= 2a^2+2b^2
        # and the certified row square-sums:
        hi += 2 * (u0[k] ** 2 * sq1 + u1[k] ** 2 * sq0)
    # both indices >= 9:  sum_{9<=k<l} (c0k c1l + c0l c1k)^2
    #   <= 2 sum_{k,l} [c0k^2 c1l^2 + c0l^2 c1k^2] <= 4 SQ0 SQ1
    hi += 4 * sq0 * sq1
    return lo, hi, minors


def su2_depth2_assembly(s: Frac) -> dict:
    """The full §17e depth-2 object at one coupling: entry windows
    computed once, both certified routes to the ratio window
    (entrywise/legacy and SOS), their combination, and the
    certification verdict."""
    ew = entry_windows(s)
    t2w, ktail = su2_t2_windows(s, ew)
    t01_leg_abs = max(abs(t2w[(0, 1)][0]), abs(t2w[(0, 1)][1]))
    r_lo_leg = t2w[(1, 1)][0] * t2w[(0, 0)][0] / (t01_leg_abs ** 2)
    r_hi_leg = t2w[(1, 1)][1] * t2w[(0, 0)][1] / (t2w[(0, 1)][0] ** 2) \
        if t2w[(0, 1)][0] > 0 else None
    det_lo, det_hi, minors = sos_det2_window(s, ew)
    t01 = t2w[(0, 1)]
    t01_abs_hi = max(abs(t01[0]), abs(t01[1]))
    r_lo_sos = 1 + det_lo / (t01_abs_hi ** 2)
    r_hi_sos = (1 + det_hi / (t01[0] ** 2)) if t01[0] > 0 else None
    r_lo = max(r_lo_leg, r_lo_sos)
    his = [r for r in (r_hi_leg, r_hi_sos) if r is not None]
    r_hi = min(his) if his else None
    # entry-level OS Gram, necessary window form (SU(2) lane)
    oscs = True
    for (a, b) in ((0, 1), (0, 2), (1, 2)):
        lo, hi = ew[(a, b)]
        minabs = Frac(0) if lo <= 0 <= hi else min(abs(lo), abs(hi))
        oscs &= minabs * minabs <= ew[(a, a)][1] * ew[(b, b)][1]
    return {"s": s, "ew": ew, "t2w": t2w, "ktail": ktail,
            "det2": (det_lo, det_hi), "minors": minors,
            "legacy": (r_lo_leg, r_hi_leg),
            "sos": (r_lo_sos, r_hi_sos),
            "ratio": (r_lo, r_hi),
            "certified": bool(r_lo > 1),
            "oscs_ok": bool(oscs),
            "consistent": bool(r_hi is None or r_lo <= r_hi)}


# ---------------------------------------------------------------------------
# U(1) lane (exact theta windows).
# ---------------------------------------------------------------------------


def wbar(s: Frac) -> Frac:
    """W-bar(s) = [3 + 2 sum_{j>=2} s^{4 (j-1)^2}]^4: certified
    envelope of sum_c s^{Q - qmin} via lambda_min(A) = 4 (per
    coordinate, integer shift <= 1 from the real minimizer)."""
    inner = Frac(3)
    j = 2
    term = s ** 4
    while term > Frac(1, 10 ** 40):
        inner += 2 * term
        j += 1
        term = s ** (4 * (j - 1) ** 2)
    inner += 2 * term / (1 - s)     # geometric close-off
    return inner ** 4


_U1_CACHE: dict[tuple[int, int, Frac], tuple[Frac, Frac]] = {}
_S_LAW = Fraction(9, 10)


def u1_entry(n: int, k: int, s: Frac) -> tuple[Frac, Frac]:
    """Certified window, tail target scaled to the entry's own
    magnitude (s^qmin) so weak-coupling radii stay small."""
    key = (n, k, s)
    if key not in _U1_CACHE:
        target = s ** qmin(n, k) * Frac(1, 10 ** 12) + Frac(1, 10 ** 38)
        lo, hi, _r = theta_window(n, k, s, target)
        _U1_CACHE[key] = (lo, hi)
    return _U1_CACHE[key]


def u1_kmax(s: Frac) -> int:
    return 10 if s > Frac(4, 5) else 6


def u1_t2_window(n: int, m: int, s: Frac, kmax: int | None = None,
                 ) -> tuple[Frac, Frac]:
    if kmax is None:
        kmax = u1_kmax(s)
    lo = Frac(0)
    hi = Frac(0)
    for k in range(-kmax, kmax + 1):
        aln, ahn = u1_entry(n, k, s)
        alm, ahm = u1_entry(k, m, s)
        lo += aln * alm
        hi += ahn * ahm
    wb = wbar(s)
    tail = Frac(0)
    for sign in (1, -1):
        k = sign * (kmax + 1)
        first = wb * wb * s ** (qmin(n, k) + qmin(k, m))
        # ratio between consecutive |k|: s^{6(2|k|+1) - 2(|n|+|m|)}
        ratio = s ** (6 * (2 * (kmax + 1) + 1) - 2 * (abs(n) + abs(m)))
        assert ratio < 1
        tail += first / (1 - ratio)
    return lo, hi + tail


def u1_x2_ratio_window(s: Frac) -> tuple[Frac, Frac]:
    w11 = u1_t2_window(1, 1, s)
    w00 = u1_t2_window(0, 0, s)
    w01 = u1_t2_window(0, 1, s)
    return (w11[0] * w00[0] / (w01[1] ** 2),
            w11[1] * w00[1] / (w01[0] ** 2))


def u1_x1_ratio_window(s: Frac) -> tuple[Frac, Frac]:
    w11 = u1_entry(1, 1, s)
    w00 = u1_entry(0, 0, s)
    w01 = u1_entry(0, 1, s)
    return (w11[0] * w00[0] / (w01[1] ** 2),
            w11[1] * w00[1] / (w01[0] ** 2))


def qmin2_continuum(n: int, m: int) -> Frac:
    """min over real shared charge: 3 n^2 + 3 m^2 - (n + m)^2 / 6."""
    return 3 * Frac(n * n + m * m) - Frac((n + m) ** 2, 6)


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def gate_qmin() -> bool:
    ok = qmin(1, 1) == 8 and qmin(0, 1) == 3 and qmin(1, -1) == 4
    ok &= qmin(2, 1) == qmin(1, 2)
    # continuum two-step cross coefficient: X-combination of Qmin_2
    cross = qmin2_continuum(1, 1) + qmin2_continuum(0, 0) \
        - 2 * qmin2_continuum(0, 1)
    ok &= cross == Frac(-1, 3)
    return bool(ok)


def gate_lagrange() -> bool:
    """The Lagrange/Cauchy-Binet identity replayed EXACTLY on a
    dense rational symmetric matrix through the same minor code
    path: det(Gram of rows 0, 1 of T^2) = sum_{k<l} M_kl^2."""
    nn = 5
    t = [[Frac(1, 1 + i + j) + (Frac(1, 3) if i == j else Frac(0))
          for j in range(nn)] for i in range(nn)]
    if any(t[i][j] != t[j][i] for i in range(nn) for j in range(nn)):
        return False
    t2 = {(n, m): sum(t[n][k] * t[k][m] for k in range(nn))
          for n in (0, 1) for m in (0, 1)}
    det2 = t2[(0, 0)] * t2[(1, 1)] - t2[(0, 1)] * t2[(1, 0)]
    sos = sum(((t[0][k] * t[1][ell] - t[0][ell] * t[1][k]) ** 2
               for k in range(nn) for ell in range(k + 1, nn)),
              Frac(0))
    ok = det2 == sos
    # and through the interval path: point windows reproduce it
    ew = {}
    for i in range(3):
        for j in range(i, 3):
            ew[(i, j)] = (t[i][j], t[i][j])
    for k, ell in ((0, 1), (0, 2), (1, 2)):
        m_iv = minor_window(k, ell, ew)
        want = t[0][k] * t[1][ell] - t[0][ell] * t[1][k]
        ok &= m_iv[0] == want == m_iv[1]
    return bool(ok)


def gate_oscs_u1(ss: tuple = (Fraction(1, 2), _S_LAW)) -> bool:
    """Entry-level OS Gram inequality checked EXACTLY on the abelian
    mirror — in its CONJUGATED form: the OS reflection reverses the
    boundary loop, so the Gram matrix is M[n, m] = T[nbar, m], i.e.
    T[-n, m] on U(1).  The mirror lane REFUTED the unconjugated form
    (kept below as a teeth check): Qmin(n, m) = 3n^2 + 3m^2 + 2nm
    gives T[1,3]^2 ~ s^72 >> s^80 ~ T[1,1] T[3,3] — the top and
    bottom disk sources drive the flip lattice oppositely (B^T u =
    -B^T w), so ALIGNED charges cost more and the raw matrix is not
    PSD; conjugating one side restores the Gram structure exactly
    (Qmin(-1,3) = 24: s^48 <= s^40).  On SU(2) the representations
    are SELF-CONJUGATE (chi_nbar = chi_n), so the Gram claim holds
    for T itself — which is what u_abs_bound consumes."""
    ok = True
    teeth = False       # the unconjugated form must FAIL somewhere
    for s in ss:
        for n in range(4):
            for m in range(4):
                if n == m:
                    continue

                def minabs(win: tuple[Frac, Frac]) -> Frac:
                    lo, hi = win
                    return Frac(0) if lo <= 0 <= hi \
                        else min(abs(lo), abs(hi))

                dn = u1_entry(-n, n, s)[1]
                dm = u1_entry(-m, m, s)[1]
                ok &= minabs(u1_entry(-n, m, s)) ** 2 <= dn * dm
                raw = minabs(u1_entry(n, m, s)) ** 2 \
                    <= u1_entry(n, n, s)[1] * u1_entry(m, m, s)[1]
                teeth |= not raw
    return bool(ok and teeth)


def gate_hk_semigroup() -> bool:
    """Diagonal heat-kernel toy composes to exact doubling under the
    same composition code path."""
    s = Frac(1, 3)
    t = {(n, m): (s ** cas4(n) if n == m else Frac(0))
         for n in range(6) for m in range(6)}
    for n in range(3):
        for m in range(3):
            t2 = sum(t[(n, k)] * t[(k, m)] for k in range(6))
            want = (s * s) ** cas4(n) if n == m else Frac(0)
            if t2 != want:
                return False
    return True


def gate_u1_law(s: Frac = _S_LAW) -> tuple[bool, float, float]:
    """The certified U(1) two-step window at weak coupling must be
    POSITIVE (sign flip vs one-step: the CS theorem quantified) and
    within a factor-2 band of the continuum +tau/3 law."""
    lo, hi = u1_x2_ratio_window(s)
    ok = lo > 1                       # X^{(2)} > 0 certified
    x1lo, x1hi = u1_x1_ratio_window(s)
    ok &= x1hi < 1                    # one-step cross NEGATIVE
    tau = -math.log(float(s))
    x2 = math.log(float((lo + hi) / 2))
    ok &= tau / 6 < x2 < 2 * tau / 3
    return bool(ok), x2, tau / 3


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> None:
    print("P2 — iterated-map windows (twice-blocked kernel), §17e SOS")
    print("=" * 66)
    print("GATE qmin/continuum-cross:", "PASSED" if gate_qmin()
          else "FAILED")
    print("GATE heat-kernel semigroup:", "PASSED"
          if gate_hk_semigroup() else "FAILED")
    g_lag = gate_lagrange()
    print("GATE Lagrange/Cauchy-Binet exact replay:",
          "PASSED" if g_lag else "FAILED")
    g_oscs = gate_oscs_u1()
    print("GATE entry-level OS Gram (U(1) exact lane):",
          "PASSED" if g_oscs else "FAILED")
    okl, x2n, law = gate_u1_law()
    print("GATE U(1) sign-flip law:", "PASSED" if okl else "FAILED",
          f" (X2_U1(9/10) ~ {x2n:.4e}, continuum tau/3 = {law:.4e})")
    rows = []
    g_sign = True
    g_consist = True
    for s in CERT_S:
        row: dict[str, object] = {"s": str(s),
                                  "tau": -math.log(float(s))}
        # U(1) lane (exact)
        u1_1 = u1_x1_ratio_window(s)
        u1_2 = u1_x2_ratio_window(s)
        row["U1_X1"] = [math.log(float(u1_1[0])),
                        math.log(float(u1_1[1]))]
        row["U1_X2"] = [math.log(float(u1_2[0])),
                        math.log(float(u1_2[1]))]
        assert u1_2[0] > 1            # CS positivity, certified
        # SU(2) lane: both certified routes, combined
        asm = su2_depth2_assembly(s)
        r_lo, r_hi = asm["ratio"]
        row["SU2_X2_ratio_certified"] = asm["certified"]
        row["SU2_X2"] = [math.log(float(r_lo)) if r_lo > 0 else None,
                         math.log(float(r_hi))
                         if r_hi is not None else None]
        row["SU2_X2_sos"] = [
            math.log(float(asm["sos"][0])),
            math.log(float(asm["sos"][1]))
            if asm["sos"][1] is not None else None]
        row["SU2_X2_legacy"] = [
            math.log(float(asm["legacy"][0]))
            if asm["legacy"][0] > 0 else None,
            math.log(float(asm["legacy"][1]))
            if asm["legacy"][1] is not None else None]
        row["det2"] = [float(asm["det2"][0]), float(asm["det2"][1])]
        row["minors"] = asm["minors"]
        row["T2_01"] = [float(asm["t2w"][(0, 1)][0]),
                        float(asm["t2w"][(0, 1)][1])]
        row["k_tail"] = float(asm["ktail"])
        row["consistent"] = asm["consistent"]
        row["oscs_ok"] = asm["oscs_ok"]
        g_sign &= asm["certified"]
        g_consist &= asm["consistent"]
        g_oscs &= asm["oscs_ok"]
        rows.append(row)
        x2 = row["SU2_X2"]
        hi_txt = f"{x2[1]:.3e}" if x2[1] is not None else "n/a"   # type: ignore[index]
        print(f"s = {s}:  SU2 X2 in [{x2[0]:.3e}, {hi_txt}]  "     # type: ignore[index]
              f"(>0 certified: {row['SU2_X2_ratio_certified']}, "
              f"consistent: {row['consistent']})")
        print(f"          U1  X2 in [{row['U1_X2'][0]:.3e}, "       # type: ignore[index]
              f"{row['U1_X2'][1]:.3e}]   U1 X1 in "                 # type: ignore[index]
              f"[{row['U1_X1'][0]:.3e}, {row['U1_X1'][1]:.3e}]")    # type: ignore[index]
    print("GATE depth-2 sign certified on the full CERT grid:",
          "PASSED" if g_sign else "FAILED")
    print("GATE SOS/entrywise consistency:",
          "PASSED" if g_consist else "FAILED")
    # rank-one collapse pin at s = 1/2 (banked one-step X1 ~ 0.2584)
    x2_half = rows[0]["SU2_X2"]
    assert isinstance(x2_half, list)
    g_scale = x2_half[1] > 10 ** -9 and x2_half[1] < 10 ** -5
    print("GATE rank-one collapse scale at s = 1/2:",
          "PASSED" if g_scale else "FAILED")
    # certified magnitude separation at depth 2: the SU(2) two-step
    # cross sits ORDERS below the abelian mirror's at every point
    # where the SU(2) upper bound is informative (the design finding
    # made quantitative: the sign is vacuous at depth 2, the
    # magnitude discriminates)
    g_sep = True
    sep_points = []
    for row in rows:
        x2r = row["SU2_X2"]
        u1r = row["U1_X2"]
        assert isinstance(x2r, list) and isinstance(u1r, list)
        if x2r[1] is not None and x2r[1] < u1r[0]:
            sep_points.append(row["s"])
    g_sep = {"1/2", "11/20", "9/16"} <= set(sep_points)
    print("GATE depth-2 magnitude separation (SU2 << U1):",
          "PASSED" if g_sep else "FAILED",
          f" at s in {sep_points}")
    print("GATE entry-level OS Gram (both lanes, all points):",
          "PASSED" if g_oscs else "FAILED")
    out = {"rows": rows, "gates": {"qmin": gate_qmin(),
                                   "hk": gate_hk_semigroup(),
                                   "lagrange": bool(g_lag),
                                   "oscs": bool(g_oscs),
                                   "u1_law": okl,
                                   "sign_grid": bool(g_sign),
                                   "consistency": bool(g_consist),
                                   "scale": bool(g_scale),
                                   "separation": bool(g_sep)},
           "separation_points": sep_points}
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1)
    print("ledger written")


if __name__ == "__main__":
    main()
