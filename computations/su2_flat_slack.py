"""Certificate-grade SU(2) image slack — the per-face bound that
upgrades the §16d flat representation from numerically gated to
certified (work_plan §16f residual (c)).

**The object.**  §16d banked (87-digit gate) the exact image-sum
representation

    K(phi; tau) = e^tau sqrt(pi)/(4 tau^{3/2} sin phi)
                  * sum_{j in Z} (phi - 2 pi j) e^{-(phi-2pi j)^2/4tau},

K_0 the j = 0 term (the dressed flat Gaussian the §16e/§16f engine
expands).  This module certifies, in EXACT RATIONALS, the relative
image bound

    |K(phi) - K_0(phi)| / K_0(phi)  <=  eps_img(tau, delta)
                    for all  phi in (0, pi - delta],

with the j-pair cancellation at phi -> 0 handled by a mean-value
bound (each +-j pair vanishes linearly at phi = 0, exactly like K_0).

**Structure of the bound.**  For a = 2 pi j and pair_j(phi) =
(phi - a) e^{-(phi-a)^2/4tau} + (phi + a) e^{-(phi+a)^2/4tau}:

  - on [0, phi_0]:   |pair_j| <= phi * sup |pair_j'|, and
        sup_{[0,phi_0]} |pair_j'| <= (1 + (a+phi_0)^2/(2 tau))
                                     * e^{-(a-phi_0)^2/4tau},
        K_0-denominator >= phi e^{-phi_0^2/4tau} * (positive const),
  - on [phi_0, pi - delta]:  term-by-term with 1/phi <= 1/phi_0 and
        e^{-(phi-a)^2/4tau} <= e^{-a^2/4tau} e^{a(pi-delta)/2tau}.

Both regimes give explicit rationals via pi in [PI_LO, PI_HI],
exp(-x) <= 1/T_N(x) (partial series) and e^y <= EU^{ceil(y)}
(EU a rational upper bound on e).  The j-sum closes with a certified
geometric ratio.  The dominant scale is e^{-pi delta / tau}: the
certificate degrades only at the cut locus phi -> pi, exactly where
the compact geometry must take over.

**Scope (recorded honestly).**  This is the PER-FACE certificate:
on the event that every slab face angle lies in [0, pi - delta], the
flat-model integrand ratio satisfies
(1 - eps)^20 <= prod_f K/K_0 <= (1 + eps)^20 — certified here.  The
remaining glue — a certified upper bound on the T-mass of the
large-angle region {some phi_f > pi - delta} — is the SAME object as
the M -> infinity spin tail (large angle <-> large spin duality) and
is carried by the su2_minf_windows level bounds; until that junction
is formalized, the network-level statement stays flagged, and the
tau-series COEFFICIENTS (which the images cannot touch at any finite
order, being e^{-c/tau}) are unaffected.

Run:  python -m computations.su2_flat_slack
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction
from typing import Tuple

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "su2_flat_slack_results.json")

sys.set_int_max_str_digits(0)

# certified rational pi window and e upper bound
PI_LO = Frac(3141592653589793, 10 ** 15)
PI_HI = Frac(3141592653589794, 10 ** 15)
E_UP = Frac(271828182845905, 10 ** 14)   # e <= E_UP
E_LO = Frac(271828182845904, 10 ** 14)   # e >= E_LO


def exp_neg_upper(x: Frac, order: int = 12) -> Frac:
    """Certified upper bound on e^{-x}, x >= 0.

    For the integer part n = floor(x): e^{-x} <= e^{-n} <= E_LO^{-n}
    (E_LO <= e); the fractional part is bounded by the partial-series
    reciprocal 1/T_N (T_N(x) <= e^x).  The combination stays tight
    for LARGE x, where the partial series alone collapses."""
    assert x >= 0
    n = int(x)
    frac_part = x - n
    ser = Frac(0)
    term = Frac(1)
    for k in range(order + 1):
        if k:
            term = term * frac_part / k
        ser += term
    return (1 / E_LO ** n) / ser


def exp_pos_upper(y: Frac) -> Frac:
    """Certified upper bound on e^{y}, y >= 0: E_UP^{ceil(y)}."""
    assert y >= 0
    n = int(y) + (0 if y == int(y) else 1)
    return E_UP ** n


def pair_bound_small(a: Frac, tau: Frac, phi0: Frac) -> Frac:
    """|pair_j|/(phi e^{-phi^2/4tau}) on [0, phi_0] via mean value."""
    sup_d = (1 + (a + phi0) ** 2 / (2 * tau)) \
        * exp_neg_upper((a - phi0) ** 2 / (4 * tau))
    return sup_d * exp_pos_upper(phi0 ** 2 / (4 * tau))


def pair_bound_large(a: Frac, tau: Frac, phi0: Frac,
                     delta: Frac) -> Frac:
    """|pair_j|/(phi e^{-phi^2/4tau}) on [phi_0, pi - delta]."""
    top = PI_HI - delta
    grow = exp_pos_upper(a * top / (2 * tau))
    return (a + PI_HI) * (grow + 1) \
        * exp_neg_upper(a * a / (4 * tau)) / phi0


def eps_img(tau: Frac, delta: Frac, phi0: Frac = None,
            jmax: int = 4) -> Frac:
    """Certified rational bound on |K - K_0|/K_0 on (0, pi - delta].

    Sums j = 1..jmax explicitly and closes the tail with a certified
    geometric ratio (the j -> j+1 factor is bounded by
    e^{-(2j+1)(2 pi)^2/(4 tau) + 2 pi (pi - delta)/(2 tau)} x
    polynomial growth, bounded crudely but certifiably)."""
    assert 0 < delta < 1
    if phi0 is None:
        phi0 = Frac(1, 2)
    tot = Frac(0)
    per_j = []
    for j in range(1, jmax + 1):
        a_lo = 2 * PI_LO * j          # a >= a_lo in decay bounds
        a_hi = 2 * PI_HI * j          # a <= a_hi in growth bounds
        b_small = (1 + (a_hi + phi0) ** 2 / (2 * tau)) \
            * exp_neg_upper((a_lo - phi0) ** 2 / (4 * tau)) \
            * exp_pos_upper(phi0 ** 2 / (4 * tau))
        top = PI_HI - delta
        b_large = (a_hi + PI_HI) \
            * (exp_pos_upper(a_hi * top / (2 * tau)) + 1) \
            * exp_neg_upper(a_lo * a_lo / (4 * tau)) / phi0
        b = max(b_small, b_large)
        per_j.append(b)
        tot += b
    # geometric closure: ratio between consecutive j at j >= jmax:
    # the dominant exponent difference is
    #   [a_{j+1}^2 - a_j^2]/(4 tau) - [a_{j+1}-a_j](pi-delta)/(2 tau)
    #   >= (2j+1)(2 pi_lo)^2/(4 tau) - 2 pi_hi * pi_hi/(2 tau),
    # polynomial prefactor growth bounded by factor 4.
    j = jmax
    dec = ((2 * j + 1) * (2 * PI_LO) ** 2 / (4 * tau)
           - 2 * PI_HI * PI_HI / (2 * tau))
    assert dec > 0, "increase jmax for this tau"
    q = 4 * exp_neg_upper(dec)
    assert q < 1, "increase jmax for this tau"
    tail = per_j[-1] * q / (1 - q)
    return tot + tail


def network_ratio_window(tau: Frac, delta: Frac,
                         faces: int = 20) -> Tuple[Frac, Frac]:
    """Certified window for prod_f K/K_0 over `faces` faces on the
    event max_f phi_f <= pi - delta."""
    e = eps_img(tau, delta)
    lo = (1 - e) ** faces if e < 1 else Frac(0)
    hi = (1 + e) ** faces
    return lo, hi


def numeric_gate(digits: int = 30) -> bool:
    """mpmath check that eps_img really dominates |K-K_0|/K_0 on a
    grid, and is not vacuous (bound within ~e^{-pi delta/tau} scale)."""
    import mpmath as mp

    mp.mp.dps = digits + 20
    ok = True
    for tau_q in (Frac(1, 10), Frac(1, 5), Frac(3, 10)):
        for delta_q in (Frac(1, 2), Frac(1, 4)):
            bound = eps_img(tau_q, delta_q)
            tau = mp.mpf(tau_q.numerator) / tau_q.denominator
            delta = mp.mpf(delta_q.numerator) / delta_q.denominator
            worst = mp.mpf(0)
            for t in range(1, 40):
                phi = (mp.pi - delta) * t / 39
                k0 = phi * mp.e ** (-phi * phi / (4 * tau))
                img = mp.mpf(0)
                for j in range(1, 60):
                    a = 2 * mp.pi * j
                    img += ((phi - a) * mp.e ** (-(phi - a) ** 2
                                                 / (4 * tau))
                            + (phi + a) * mp.e ** (-(phi + a) ** 2
                                                   / (4 * tau)))
                worst = max(worst, abs(img) / k0)
            b = mp.mpf(bound.numerator) / bound.denominator
            ok &= bool(worst <= b)
    return ok


def main() -> None:
    print("Certificate-grade SU(2) image slack (per-face lemma)")
    print("=" * 72)
    ok = numeric_gate()
    print(f"GATE — mpmath domination check on a (tau, delta) grid: "
          f"{'PASSED' if ok else 'FAILED'}")
    rows = []
    for tau in (Frac(1, 20), Frac(1, 10), Frac(1, 5), Frac(3, 10),
                Frac(2, 5)):
        for delta in (Frac(1, 2), Frac(1, 4)):
            e = eps_img(tau, delta)
            lo, hi = network_ratio_window(tau, delta)

            def fl(x):
                try:
                    return float(x)
                except OverflowError:
                    return float("inf")

            rows.append({"tau": str(tau), "delta": str(delta),
                         "eps_img": str(e) if e < 10 ** 6 else "huge",
                         "eps_float": fl(e),
                         "net20_lo": fl(lo), "net20_hi": fl(hi)})
            print(f"  tau={tau}  delta={delta}:  eps_img = {fl(e):.3e}"
                  f"   20-face window [{fl(lo):.6f}, {fl(hi):.6f}]")
    with open(OUT_JSON, "w") as fh:
        json.dump({"gate": ok, "rows": rows}, fh, indent=1)
    print(f"\nledger written to {OUT_JSON}")


if __name__ == "__main__":
    main()
