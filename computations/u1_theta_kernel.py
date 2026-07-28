"""MD.2 — exact M = infinity U(1) slab kernel by theta-resummation.

**Why (work_plan §16a, MD.2 protocol discovery).**  Fixed-M ladders
cannot reach the s -> 1 dichotomy regime: at s = 99/100 the U(1)
pair01 tau'/tau still falls 19.55 -> 12.03 -> 7.88 across M = 3, 4, 5.
But the abelian owned-boundary kernel needs no truncation at all: its
configuration set is exactly (particular disk solution) + (rank-4
cube-flip lattice), so the M = infinity kernel is the quadratic-form
theta series

    T[n,m](s) = sum_{c in Z^4} s^{Q(c; n, m)},
    Q(c; n, m) = |k0(n,m) + B c|^2 = c^T A c + b(n,m).c + |k0|^2,

with  A = B^T B = 6 I - Adj(C_4)   (each cube shares one wall with
each cyclic neighbour), spectrum {4, 6, 6, 8} (exact, from the
factored characteristic polynomial), and  b(n,m) = 2 B^T k0 =
2(n-m)(1,1,1,1)  (B^T u = (1,1,1,1) = -B^T w for the unit top/bottom
disk solutions u, w).  Every quantity in this module is an exact
integer/rational; kernel values at rational s are certified rational
WINDOWS [partial sum, partial sum + tail bound] with the tail bound
proved from lambda_min(A) = 4 and the shell count
(2r+1)^4 - (2r-1)^4 <= 80 r^3.

**The exact asymptotic flow law.**  Completing the square,

    Qmin(n,m) := min_{c in R^4} Q(c; n, m)
              = |k0|^2 - (1/4) b^T A^{-1} b
              = 3 n^2 + 3 m^2 + 2 n m        (exact; grid-verified),

a quadratic form because k0 is linear in (n, m).  As tau = -log s -> 0
the theta sum satisfies (Poisson summation; corrections
O(e^{-pi^2 lambda / tau}))

    T[n,m](s) = Theta_0(tau) e^{-tau Qmin(n,m)} (1 + O(e^{-c/tau})),

with Theta_0 independent of (n, m).  Hence on the flowed envelope
v_n = sum_m T[n,m] s^{C(m)} over any charge-conjugation-symmetric
coarse basis, every D2-family observable has the SAME limit:

    pair(a,b):  tau'/tau -> [ mean_m Qmin(b,m) - mean_m Qmin(a,m) ]
                            / (C(b) - C(a))
                          =  alpha (b^2 - a^2) / (b^2 - a^2)
                          =  alpha = 3,

because mean_m over a symmetric basis kills the cross term gamma n m,
and C(n) = n^2 matches the n^2 shape of the mean exactly.  The legacy
least-squares fit has the same limit (slope of alpha n^2 + const
against n^2).  So the U(1) one-step envelope-matched flow exponent is

    E* = alpha = |u|^2 - (B^T u)^T A^{-1} (B^T u) = 4 - 1 = 3,

the 2D disk value 4 screened by exactly 1 unit through the flip
lattice.  E* < 4: the abelian anti-renormalization SURVIVES to
s -> 1 with exact deficit 1, and the limit is scheme-covariant across
the whole D2 family (all pairs, and the fit) — the §16 fence holds AT
the limit for this family.  The separator observable (D1) degenerates
here instead: G(s) ~ Theta_0 (J - tau Qmin + ...) with J the all-ones
matrix, so lambda_1/lambda_0 = O(tau) and the matched tau'/tau
diverges like log(1/tau)/tau — the connected one-step content
vanishes linearly in tau, so D1 needs a tau-rescaled matching to be a
dichotomy coordinate at one step (recorded, not repaired, here).

**Caveats (honesty).**  This is the ONE-STEP, thickness-one,
anisotropic (2x2x1) blocking map of the heat-kernel U(1) theory on
the DP.2 slab — not yet an iterated isotropic RG trajectory.  E* = 3
is an exact statement about this instrument, on the same geometry
where SU(2) must now be measured (the SU(2) analogue needs the
fixed-tile machinery with eps_slab-style tail control; that is the
open half of MD.2).  Under iteration-naive reading, tau' = E* tau
gives tau(a) ~ a^{log2 E*} = a^{1.585}, which fails (TS)'s linear
floor — for U(1), as the discriminator demands.

Run:  python -m computations.u1_theta_kernel
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
Frac = Fraction
OUT_JSON = os.path.join(HERE, "u1_theta_results.json")

sys.set_int_max_str_digits(0)      # exact windows carry huge integers


def dec_bracket(lo: Frac, hi: Frac, digits: int = 40) -> List[str]:
    """Outward-rounded decimal bracket strings: lo rounded DOWN, hi
    rounded UP to `digits` significant decimals — the printed bracket
    still certifiably contains [lo, hi]."""
    def sig(x: Frac, up: bool) -> str:
        if x == 0:
            return "0"
        neg = x < 0
        if neg:
            x = -x
            up = not up
        e = 0
        while x < 1:
            x *= 10
            e -= 1
        while x >= 10:
            x /= 10
            e += 1
        scaled = x * 10 ** (digits - 1)
        n = scaled.numerator // scaled.denominator
        if up and scaled != n:
            n += 1
        mant = str(n)
        if len(mant) > digits:          # rounding overflow 9.99 -> 10.0
            mant = mant[:-1]
            e += 1
        return ("-" if neg else "") + mant[0] + "." + mant[1:] \
            + f"e{e}"
    return [sig(lo, False), sig(hi, True)]

# ---------------------------------------------------------------------------
# Exact lattice data, imported from the certified slab geometry.
# ---------------------------------------------------------------------------

from computations.dp6_u1_slab_blocking import (  # noqa: E402
    _B,
    _particular,
    NF,
    certify_kernel_basis,
    kernel_entry_u1,
)

A_MAT: List[List[int]] = [
    [sum(_B[i][f] * _B[j][f] for f in range(NF)) for j in range(4)]
    for i in range(4)
]
LAMBDA_MIN = 4          # exact: A = 6I - Adj(C4), spectrum {4, 6, 6, 8}


def _check_spectrum() -> bool:
    """charpoly(A) must equal (x-4)(x-6)^2(x-8) exactly."""
    # expand (x-4)(x-6)^2(x-8) = x^4 - 24x^3 + 212x^2 - 816x + 1152
    want = [Frac(1152), Frac(-816), Frac(212), Frac(-24), Frac(1)]
    from computations.flow_matching import charpoly
    got = charpoly([[Frac(x) for x in row] for row in A_MAT])
    return list(reversed(got)) == list(reversed(want))


def qform_data(n: int, m: int):
    """(c0, b) with Q(c) = c^T A c + b.c + c0, all integers."""
    k0 = _particular(n, m)
    c0 = sum(x * x for x in k0)
    b = [2 * sum(_B[i][f] * k0[f] for f in range(NF)) for i in range(4)]
    return c0, b


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
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def qmin(n: int, m: int) -> Frac:
    """Exact real minimum of Q(.; n, m): |k0|^2 - b^T A^{-1} b / 4."""
    c0, b = qform_data(n, m)
    x = _solve(A_MAT, [Frac(bi, 2) for bi in b])   # A x = b/2
    return Frac(c0) - sum(Frac(bi) * xi for bi, xi in zip(b, x)) / 2


ALPHA = qmin(1, 0)          # = 3
BETA = qmin(0, 1)           # = 3
GAMMA = qmin(1, 1) - ALPHA - BETA   # = 2
E_STAR = ALPHA              # the exact asymptotic flow exponent


# ---------------------------------------------------------------------------
# Certified theta windows.
# ---------------------------------------------------------------------------


def tail_bound(n: int, m: int, s: Frac, R: int) -> Frac:
    """Exact bound on sum over |c|_inf > R of s^{Q(c)}.

    Q(c) >= lambda_min |c|_2^2 + b.c + c0 >= 4 r^2 - |b|_1 r + c0
    (r = |c|_inf).  Require R >= |b|_1/2 so that for r > R,
    4r^2 - |b|_1 r >= 2 r^2 >= 2 (R+1) r.  With q = s^{2(R+1)} and
    shell count <= 80 r^3:
        tail <= s^{c0} * 80 * sum_{r > R} r^3 q^r
             <= s^{c0} * 80 * q^{R+1} (R+1)^3 * 6 / (1-q)^4,
    using sum_{j>=0} (j+1)^3 q^j = (1 + 4q + q^2)/(1-q)^4 <= 6/(1-q)^4
    and r^3 <= (R+1)^3 (1 + j/(R+1))^3 <= (R+1)^3 (j+1)^3 at
    r = R+1+j.  All exact rational arithmetic."""
    c0, b = qform_data(n, m)
    b1 = sum(abs(x) for x in b)
    assert 2 * R >= b1, f"R = {R} too small for |b|_1 = {b1}"
    q = s ** (2 * (R + 1))
    assert q < 1
    return (s ** c0) * 80 * q ** (R + 1) * Frac((R + 1) ** 3) \
        * 6 / (1 - q) ** 4


def _partial_sum_exponents(n: int, m: int, R: int) -> Dict[int, int]:
    """Histogram {Q(c): count} over the box |c_i| <= R (exact ints).
    Vectorized with numpy when available; pure-python fallback."""
    c0, b = qform_data(n, m)
    try:
        import numpy as np
        rng = np.arange(-R, R + 1, dtype=np.int64)
        c3, c4 = np.meshgrid(rng, rng, indexing="ij")
        c3 = c3.ravel()
        c4 = c4.ravel()
        A = A_MAT
        hist: Dict[int, int] = {}
        for c1 in range(-R, R + 1):
            for c2 in range(-R, R + 1):
                # Q = cT A c + b.c + c0 with c = (c1, c2, c3, c4)
                qq = (A[0][0] * c1 * c1 + A[1][1] * c2 * c2
                      + 2 * A[0][1] * c1 * c2
                      + b[0] * c1 + b[1] * c2 + c0)
                lin3 = 2 * (A[0][2] * c1 + A[1][2] * c2) + b[2]
                lin4 = 2 * (A[0][3] * c1 + A[1][3] * c2) + b[3]
                Q = (qq
                     + A[2][2] * c3 * c3 + A[3][3] * c4 * c4
                     + 2 * A[2][3] * c3 * c4
                     + lin3 * c3 + lin4 * c4)
                vals, counts = np.unique(Q, return_counts=True)
                for v, cnt in zip(vals.tolist(), counts.tolist()):
                    hist[v] = hist.get(v, 0) + cnt
        return hist
    except ImportError:
        import itertools
        hist = {}
        for c in itertools.product(range(-R, R + 1), repeat=4):
            Q = c0
            for i in range(4):
                Q += b[i] * c[i]
                for j in range(4):
                    Q += A_MAT[i][j] * c[i] * c[j]
            hist[Q] = hist.get(Q, 0) + 1
        return hist


def _eval_hist(hist: Dict[int, int], s: Frac) -> Frac:
    """Exact sum count * s^E by incremental big-integer recurrence:
    with ascending exponents E_1 < ... < E_k,
        A_i = A_{i-1} * den^{E_i - E_{i-1}} + h_i * num^{E_i},
    every step is big x small; the result is A_k / den^{E_k}."""
    num, den = s.numerator, s.denominator
    exps = sorted(hist)
    acc = 0
    prev = 0
    pow_n = 1                  # num^prev
    for E in exps:
        gap = E - prev
        pow_n *= num ** gap
        acc = acc * den ** gap + hist[E] * pow_n
        prev = E
    return Frac(acc, den ** prev)


def theta_window(n: int, m: int, s: Frac, tail_target: Frac,
                 R_max: int = 200) -> Tuple[Frac, Frac, int]:
    """Certified window [lo, hi] for T_inf[n,m](s), plus the radius
    used.  hi - lo <= tail_target guaranteed on success."""
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
    return part, part + tail_bound(n, m, s, R), R


# ---------------------------------------------------------------------------
# Flowed-envelope observables from windows (interval arithmetic).
# ---------------------------------------------------------------------------


def flow_windows(N: int, s: Frac, rel_target: Frac = Frac(1, 10 ** 6)):
    """Windows for v_n (n = 0..N) over the symmetric coarse basis
    |m| <= N, then windows for the pairwise matched exponents

        tau'_{ab}/tau = log(s'_{ab}) / log(s)
                      = [log(v_a) - log(v_b)] / (tau (C(b) - C(a)))

    reported as float brackets of the exact window endpoints (the
    exact objects are the v-windows and their rational quotients)."""
    # scale the absolute tail target to the smallest expected v-term:
    # v_n >= T[n,n] s^{C(n)} >= s^{Qmin(n,n) + C(n)} crude floor
    out: Dict[int, Tuple[Frac, Frac]] = {}
    for n in range(0, N + 1):
        lo = Frac(0)
        hi = Frac(0)
        for m in range(-N, N + 1):
            floor = s ** (int(qmin(max(abs(n), abs(m)),
                                   max(abs(n), abs(m)))) + 40)
            tl, th, _R = theta_window(n, m, s, floor * rel_target)
            w = Frac(1) * s ** (m * m)
            lo += tl * w
            hi += th * w
        out[n] = (lo, hi)
    ratios = {}
    for a in range(0, N + 1):
        for b in range(a + 1, N + 1):
            k = b * b - a * a
            # window for (v_b/v_a)
            rlo = out[b][0] / out[a][1]
            rhi = out[b][1] / out[a][0]
            lt = math.log(float(s))
            ratios[f"{a},{b}"] = (
                math.log(float(rhi)) / (lt * k),
                math.log(float(rlo)) / (lt * k),
            )
    return out, ratios


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def gates(s: Frac = Frac(1, 2)) -> None:
    assert certify_kernel_basis(), "flip-lattice certificate FAILED"
    assert _check_spectrum(), "A spectrum gate FAILED"
    assert (ALPHA, BETA, GAMMA) == (Frac(3), Frac(3), Frac(2))
    # Qmin is exactly the quadratic form on a grid
    for n in range(-3, 4):
        for m in range(-3, 4):
            assert qmin(n, m) == ALPHA * n * n + BETA * m * m \
                + GAMMA * n * m
    # theta window sandwiches the truncated kernels monotonically
    for (n, m) in [(0, 0), (1, 0), (1, 1), (1, -1), (2, 2)]:
        lo, hi, _R = theta_window(n, m, s, Frac(1, 10 ** 30))
        prev = None
        for M in (3, 4, 5, 6):
            tm = sum(c * s ** p
                     for p, c in kernel_entry_u1(n, m, M).items())
            if prev is not None:
                assert tm >= prev, "T_M not monotone"
            prev = tm
            assert tm <= hi, f"T_M={M} exceeds theta hi at ({n},{m})"
        assert hi - prev <= Frac(1, 10 ** 6), (
            f"theta window far from T_M=6 at ({n},{m}): {float(hi-prev)}")


def main() -> None:
    print("MD.2 U(1) theta-resummation — exact M = infinity kernel")
    print(f"A = {A_MAT}; spectrum (4, 6, 6, 8) verified: "
          f"{_check_spectrum()}")
    print(f"Qmin(n,m) = {ALPHA} n^2 + {BETA} m^2 + {GAMMA} n m (exact)")
    print(f"E* = alpha = |u|^2 - (B^T u)^T A^-1 (B^T u) = 4 - 1 = "
          f"{E_STAR}")
    print("gates (certificate, spectrum, Qmin grid, monotone "
          "sandwich at s = 1/2)...", flush=True)
    gates()
    print("  gates PASSED", flush=True)

    results = {"E_star": str(E_STAR),
               "Qmin_form": [str(ALPHA), str(BETA), str(GAMMA)],
               "rows": []}
    for s in (Frac(1, 2), Frac(3, 4), Frac(9, 10), Frac(99, 100)):
        print(f"  s = {s} ...", flush=True)
        v, ratios = flow_windows(2, s)
        tau = -math.log(float(s))
        row = {"s": str(s), "tau": tau,
               "v_windows": {n: dec_bracket(a, b) for n, (a, b)
                             in v.items()},
               "tau_ratio_brackets": ratios}
        results["rows"].append(row)
        pr = ", ".join(f"[{a:.4f}, {b:.4f}]" for a, b in
                       (ratios["0,1"], ratios["0,2"], ratios["1,2"]))
        print(f"    tau'/tau brackets (pairs 01, 02, 12): {pr}   "
              f"(E* = {E_STAR}, 2D rule = 4)")
    with open(OUT_JSON, "w") as fh:
        json.dump(results, fh, indent=1, default=str)
    print(f"exact ledger written to {OUT_JSON}")


if __name__ == "__main__":
    main()
