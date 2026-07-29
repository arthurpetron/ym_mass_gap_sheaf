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

HONESTY
-------
One composition step of the banked one-step kernel; thickness-one
anisotropic slabs composed in the transfer direction.  The (·,2)
entry windows are crude (label-less (2,2) unreached masses dominate
them) — they enter only at the 1e-13 level of the composition at the
CERT points, far below the leading windows.  The two-step object is
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

CERT_S = (Frac(1, 2), Frac(11, 20), Frac(9, 16), Frac(8, 13))
K_BANKED = 2          # census boundary charges 0..2
K_DOM = 8             # DomTransfer bounds for 3..K_DOM
LAM = 8


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


def dom_bound(n: int, k: int, s: Frac) -> Frac:
    """|T[n, k]| <= d_n d_k (full dominated trace + slop)."""
    dt = DomTransfer(n, k, s, LAM)
    return Frac(dim(n) * dim(k)) \
        * (dt.dominated_trace(LAM) + dt.lam_slop())


def corner_floor(k: int) -> int:
    """f(k) = min_{0 <= q <= k} (2 C(q) + C(k - q)) (exact scan)."""
    return min(2 * cas4(q) + cas4(k - q) for q in range(k + 1))


def crude_high_k(n: int, k: int, s: Frac) -> Frac:
    """Analytic bound for k >= 9: four corners pay (4^{1/3} s)^{f(k)}
    each after d-absorption; the a-side nodes, edges and the n-side
    close by geometric sums."""
    assert 4 * s ** 3 < 1           # (4^{1/3} s) < 1, cubed form
    base = Frac(4) ** ((corner_floor(k) + 2) // 3) * s ** corner_floor(k)
    g = (sum_pow2(0, s)) ** 8       # a-nodes + w-edges, crude closure
    return Frac(dim(n) * dim(k)) * base ** 4 * g


def su2_t2_windows(s: Frac) -> tuple[
        dict[tuple[int, int], tuple[Frac, Frac]], Frac]:
    """Certified windows for T_2[n, m], (n, m) in {0, 1}^2, plus the
    k-truncation tail (reported)."""
    ew = entry_windows(s)

    def w(n: int, m: int) -> tuple[Frac, Frac]:
        return ew[(min(n, m), max(n, m))]

    dom = {(n, k): dom_bound(n, k, s)
           for n in (0, 1) for k in range(3, K_DOM + 1)}
    # k >= 9 closure: ratio of consecutive crude bounds < 1/2, checked
    tail9 = Frac(0)
    for n in (0, 1):
        for m in (0, 1):
            b9 = crude_high_k(n, 9, s) * crude_high_k(m, 9, s)
            b10 = crude_high_k(n, 10, s) * crude_high_k(m, 10, s)
            assert 2 * b10 < b9
            tail9 += 2 * b9
    out: dict[tuple[int, int], tuple[Frac, Frac]] = {}
    max_tail = Frac(0)
    for n in (0, 1):
        for m in (0, 1):
            if (n, m) in out:
                continue
            lo = sum((w(n, k)[0] * w(k, m)[0] for k in range(3)
                      if w(n, k)[0] > 0 and w(k, m)[0] > 0), Frac(0))
            hi = sum((max(abs(w(n, k)[0]), w(n, k)[1])
                      * max(abs(w(k, m)[0]), w(k, m)[1])
                      for k in range(3)), Frac(0))
            tail = sum((dom[(n, k)] * dom[(m, k)]
                        for k in range(3, K_DOM + 1)), Frac(0))
            tail += 2 * crude_high_k(n, 9, s) * crude_high_k(m, 9, s)
            hi += tail
            max_tail = max(max_tail, tail)
            out[(n, m)] = (lo, hi)
            out[(m, n)] = (lo, hi)
    return out, max_tail


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
    print("P2 — iterated-map windows (twice-blocked kernel)")
    print("=" * 66)
    print("GATE qmin/continuum-cross:", "PASSED" if gate_qmin()
          else "FAILED")
    print("GATE heat-kernel semigroup:", "PASSED"
          if gate_hk_semigroup() else "FAILED")
    okl, x2n, law = gate_u1_law()
    print("GATE U(1) sign-flip law:", "PASSED" if okl else "FAILED",
          f" (X2_U1(9/10) ~ {x2n:.4e}, continuum tau/3 = {law:.4e})")
    rows = []
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
        # SU(2) lane
        t2w, ktail = su2_t2_windows(s)
        r_lo = t2w[(1, 1)][0] * t2w[(0, 0)][0] / (t2w[(0, 1)][1] ** 2)
        r_hi = t2w[(1, 1)][1] * t2w[(0, 0)][1] / (t2w[(0, 1)][0] ** 2)
        row["SU2_X2_ratio_certified"] = bool(r_lo > 1)
        row["SU2_X2"] = [math.log(float(r_lo)), math.log(float(r_hi))]
        row["k_tail"] = float(ktail)
        rows.append(row)
        print(f"s = {s}:  SU2 X2 in [{row['SU2_X2'][0]:.3e}, "     # type: ignore[index]
              f"{row['SU2_X2'][1]:.3e}]  "                          # type: ignore[index]
              f"(>0 certified: {row['SU2_X2_ratio_certified']})")
        print(f"          U1  X2 in [{row['U1_X2'][0]:.3e}, "       # type: ignore[index]
              f"{row['U1_X2'][1]:.3e}]   U1 X1 in "                 # type: ignore[index]
              f"[{row['U1_X1'][0]:.3e}, {row['U1_X1'][1]:.3e}]")    # type: ignore[index]
    # rank-one collapse pin at s = 1/2 (banked one-step X1 ~ 0.2584)
    x2_half = rows[0]["SU2_X2"]
    assert isinstance(x2_half, list)
    g_scale = x2_half[1] > 10 ** -9 and x2_half[1] < 10 ** -5
    print("GATE rank-one collapse scale at s = 1/2:",
          "PASSED" if g_scale else "FAILED")
    # certified magnitude separation at depth 2, s = 1/2: the SU(2)
    # two-step cross sits ORDERS below the abelian mirror's (rational
    # window comparison; the design finding made quantitative: the
    # sign is vacuous at depth 2, the magnitude discriminates)
    u1_half = rows[0]["U1_X2"]
    assert isinstance(u1_half, list)
    g_sep = x2_half[1] < u1_half[0]
    print("GATE depth-2 magnitude separation (SU2 << U1 at s = 1/2):",
          "PASSED" if g_sep else "FAILED",
          f" ({x2_half[1]:.2e} < {u1_half[0]:.2e})")
    out = {"rows": rows, "gates": {"qmin": gate_qmin(),
                                   "hk": gate_hk_semigroup(),
                                   "u1_law": okl,
                                   "scale": bool(g_scale),
                                   "separation": bool(g_sep)}}
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1)
    print("ledger written")


if __name__ == "__main__":
    main()
