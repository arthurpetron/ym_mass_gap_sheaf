"""MD.2/MD.3 — the exact asymptotic flow curve of the U(1) slab step.

**Upgrade over §16b.**  The theta-resummation gave the limit
tau'/tau -> E* = 3.  This module upgrades the limit to an EXACT
ASYMPTOTIC CURVE with a certified error bound, and extracts the
subleading slope in closed form — the object the SU(2) half of MD.2
must be compared against.

**Theta-factor separation (the lemma).**  Q(c; n, m) =
(c - c*)^T A (c - c*) + Qmin(n, m) with real minimizer c*(n, m), so

    T[n,m](s) = s^{Qmin(n,m)} * Theta_{c*}(s),
    Theta_{c*}(s) = sum_{c in Z^4} s^{(c - c*)^T A (c - c*)}.

By Poisson summation the c*-dependence of Theta_{c*} sits entirely in
dual phases:  |Theta_{c*}/Theta_0 - 1| <= 2 sum_{k != 0}
e^{-pi^2 k^T A^{-1} k / tau} =: slack(tau), and with
k^T A^{-1} k >= |k|^2 / 8 (lambda_max(A) = 8) and the shell count
<= 80 r^3 the slack is bounded by an explicit geometric series.  A
RATIONAL upper bound uses pi^2 >= 9869/1000 and
e^{-x} <= 1 / (sum_{j<=6} x^j/j!): every slack number below is a
certified rational.  Hence

    v_n(s) = sum_m T[n,m] s^{C(m)}
           = Theta_0(s) * s^{alpha n^2} * P_n(s) * (1 + O(slack)),
    P_n(s) := sum_{|m| <= N} s^{gamma n m + (alpha + 1) m^2}
            = sum_m s^{2 n m + 4 m^2}                (alpha=3, gamma=2)

and every pair observable has the exact asymptotic closed form

    tau'_{ab}/tau = E*_{ab}(s)
        = 3 + [log P_a(s) - log P_b(s)] / (tau (C(b) - C(a)))
          + O(slack/tau),

with P_n integer polynomials in s.  The theta factor — the divergent,
group-blind bulk — cancels IDENTICALLY in every observable; all
remaining s-dependence is the finite coarse-basis sum.

**Subleading slope in closed form.**  Cumulant expansion of the
finite sums gives

    E*_{ab}(tau) = 3 - (gamma^2 Var_N(m) / 2) tau + O(tau^2),

with Var_N(m) the variance of m over the symmetric basis: the slope
is PAIR-INDEPENDENT (scheme-covariant at subleading order) and equals
-4 at N = 2 (Var = 2), -8 at N = 3 (Var = 4).  Structure worth
stating loudly: the slope is driven entirely by gamma^2 — the SQUARE
of the abelian cross term.  The flat-limit argument for SU(2) (see
notes/su2-flat-limit-scope.md) kills the LINEAR cross term by
realness of characters, so the SU(2) subleading slope has no
gamma^2-artifact contribution: whatever c_SU2 is measured/derived to
be, it is honest next-order heat-kernel dynamics, not basis
bookkeeping.

Run:  python -m computations.flow_asymptotic
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction
from typing import Dict, List, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
Frac = Fraction
OUT_JSON = os.path.join(HERE, "flow_asymptotic_results.json")

sys.set_int_max_str_digits(0)

from computations.u1_theta_kernel import (  # noqa: E402
    ALPHA,
    BETA,
    GAMMA,
    qmin,
    flow_windows,
)

N_BASIS = 2


# ---------------------------------------------------------------------------
# The finite-basis polynomials P_n and the exact pair curves.
# ---------------------------------------------------------------------------


def basis_exponents(n: int, N: int = N_BASIS) -> List[int]:
    """E_m = Qmin(n,m) + m^2 - alpha n^2 = gamma n m + (alpha+1) m^2."""
    out = []
    for m in range(-N, N + 1):
        e = qmin(n, m) + m * m - ALPHA * n * n
        assert e == GAMMA * n * m + (ALPHA + 1) * m * m
        assert e.denominator == 1
        out.append(int(e))
    return out


def p_poly(n: int, N: int = N_BASIS) -> Dict[int, int]:
    """P_n(s) as {exponent: count} (exponents may repeat)."""
    out: Dict[int, int] = {}
    for e in basis_exponents(n, N):
        out[e] = out.get(e, 0) + 1
    return out


def eval_poly(p: Dict[int, int], s: Frac) -> Frac:
    return sum((c * s ** k for k, c in p.items()), Frac(0))


def pair_curve(a: int, b: int, s: Frac, N: int = N_BASIS) -> float:
    """The exact asymptotic curve E*_{ab}(s) (float image; the exact
    object is the rational P_a(s)/P_b(s))."""
    tau = -math.log(float(s))
    pa = eval_poly(p_poly(a, N), s)
    pb = eval_poly(p_poly(b, N), s)
    k = b * b - a * a
    return float(ALPHA) + math.log(float(pa) / float(pb)) / (tau * k)


# ---------------------------------------------------------------------------
# Exact cumulant coefficients: E*(tau) = 3 + c1 tau + c2 tau^2 + ...
# ---------------------------------------------------------------------------


def cumulants(vals: List[int], order: int = 3) -> List[Frac]:
    K = len(vals)
    mean = Frac(sum(vals), K)
    mu = [Frac(sum((v - mean) ** j for v in vals), K)
          for j in range(2, order + 1)]
    # kappa_2 = mu_2, kappa_3 = mu_3 (central moments up to order 3)
    return [mean] + mu


def pair_coeffs(a: int, b: int, N: int = N_BASIS) -> Tuple[Frac, Frac]:
    """(c1, c2) with E*_{ab}(tau) = 3 + c1 tau + c2 tau^2 + O(tau^3).

    log P_n(e^-tau) = log K - tau mean_n + tau^2 kappa2_n / 2
                      - tau^3 kappa3_n / 6 + ...
    and E*_{ab} = 3 + [log P_a - log P_b] / (tau (C(b)-C(a)))."""
    ka = cumulants(basis_exponents(a, N))
    kb = cumulants(basis_exponents(b, N))
    k = b * b - a * a
    # mean_a - mean_b contributes at order tau^0: must vanish for the
    # E* law; assert it (mean_n = (alpha+1) Var-free: gamma mean(m)=0)
    assert ka[0] == kb[0], "mean law violated"
    c1 = (ka[1] - kb[1]) / (2 * k)
    c2 = -(ka[2] - kb[2]) / (6 * k)
    return c1, c2


def slope_closed_form(N: int = N_BASIS) -> Frac:
    """c1 = -gamma^2 Var_N(m) / 2, pair-independent."""
    K = 2 * N + 1
    var_m = Frac(sum(m * m for m in range(-N, N + 1)), K)
    return -GAMMA ** 2 * var_m / 2


# ---------------------------------------------------------------------------
# Certified slack bound for the theta-factor separation.
# ---------------------------------------------------------------------------


def _exp_upper(x: Frac) -> Frac:
    """Rational upper bound on e^{-x}, x > 0: 1/(partial e^x series)."""
    assert x > 0
    ser = sum(x ** j / math.factorial(j) for j in range(7))
    return 1 / ser


def slack_bound(s: Frac) -> Frac:
    """Certified rational bound on the c*-dependence of Theta:
    2 sum_{k != 0} e^{-pi^2 k^T A^{-1} k / tau}, with
    k^T A^{-1} k >= |k|^2/8, pi^2 >= 9869/1000, shells <= 80 r^3,
    and tau = -log s >= 1 - s."""
    tau_hi = -Frac(math.floor(math.log(float(s)) * 10 ** 12), 10 ** 12)
    # certified: tau = -log s <= tau_hi needs care; use tau <= s^-1 - 1
    tau_ub = 1 / s - 1          # -log s <= 1/s - 1 exactly
    x1 = Frac(9869, 1000) / (8 * tau_ub)   # min dual exponent, r = 1
    q = _exp_upper(x1)          # e^{-x1} upper bound, ratio per r^2 step
    # sum_{r>=1} 80 r^3 (q)^{r^2} <= 80 q sum_{r>=1} r^3 q^{r-1}
    #   <= 80 q * 6 / (1-q)^4   (q < 1)
    assert q < 1
    return 2 * 80 * q * 6 / (1 - q) ** 4


# ---------------------------------------------------------------------------
# Verification against the certified theta windows.
# ---------------------------------------------------------------------------


def verify(s: Frac, N: int = N_BASIS) -> dict:
    """Compare the closed-form curve with the certified windows of
    §16b at coupling s.  Returns per-pair (curve, window, agree)."""
    _v, ratios = flow_windows(N, s)
    out = {"s": str(s), "slack_bound": float(slack_bound(s)), "pairs": {}}
    tau = -math.log(float(s))
    for key in ratios:
        a, b = map(int, key.split(","))
        curve = pair_curve(a, b, s, N)
        lo, hi = ratios[key]
        # the windows carry the FULL kernel; the curve drops only the
        # exponentially small slack: they must agree to
        # ~ slack/(tau * (C(b)-C(a))) plus window width
        tol = out["slack_bound"] / (tau * (b * b - a * a)) + (hi - lo) \
            + 1e-9
        out["pairs"][key] = {
            "curve": curve,
            "window": [lo, hi],
            "diff": curve - (lo + hi) / 2,
            "tol": tol,
            "agree": abs(curve - (lo + hi) / 2) <= tol,
        }
    return out


def main() -> None:
    print("MD.2/MD.3 — exact asymptotic flow curve, U(1) slab step")
    print(f"P_n(s) = sum_m s^(2nm + 4m^2), |m| <= {N_BASIS}")
    for n in range(0, 3):
        print(f"  P_{n}: exponents {sorted(basis_exponents(n))}")
    c1 = slope_closed_form()
    print(f"closed-form slope c1 = -gamma^2 Var(m)/2 = {c1}  (N = 2)")
    print(f"  N = 1: {slope_closed_form(1)}   N = 3: {slope_closed_form(3)}")
    for (a, b) in ((0, 1), (0, 2), (1, 2)):
        p1, p2 = pair_coeffs(a, b)
        print(f"  pair {a},{b}: c1 = {p1}, c2 = {p2}")
        assert p1 == c1, "pair-independence of the slope FAILED"

    print("\nverification against certified windows:")
    results = {"c1_N2": str(c1), "rows": []}
    for s in (Frac(3, 4), Frac(9, 10), Frac(99, 100)):
        r = verify(s)
        results["rows"].append(r)
        for key, e in r["pairs"].items():
            print(f"  s={s} pair {key}: curve {e['curve']:.6f} vs "
                  f"window [{e['window'][0]:.6f}, {e['window'][1]:.6f}] "
                  f" diff {e['diff']:+.2e}  (tol {e['tol']:.1e})  "
                  f"{'AGREE' if e['agree'] else 'DISAGREE'}")
    with open(OUT_JSON, "w") as fh:
        json.dump(results, fh, indent=1, default=str)
    print(f"\nledger written to {OUT_JSON}")

    # the curve extended to tau -> 0: E*(tau) = 3 - 4 tau + c2 tau^2
    print("\nasymptotic expansion check at tau = 0.01005 (s = 99/100):")
    c1v, c2v = pair_coeffs(0, 1)
    tau = 0.010050335853501441
    print(f"  3 + c1 tau + c2 tau^2 = {3 + float(c1v)*tau + float(c2v)*tau*tau:.6f}"
          f"   (measured window ~ 2.9620)")


if __name__ == "__main__":
    main()
