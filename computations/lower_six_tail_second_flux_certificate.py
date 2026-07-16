#!/usr/bin/env python3
"""Exact Bernstein certificates for the lower-six local second-flux envelope.

This is a derivation/checking script, not a numerical scout.  Every
coefficient is an exact Python integer or ``fractions.Fraction``.

Variable convention
-------------------

``D`` is the harmonic denominator ``k + 2`` and ``n`` is the mode.  Put
``m = 2*n + 1`` and

    C_j(m) = m*(m-1)*...*(m-j+1)/j!.

``U8num / D^8`` is the even Taylor upper bound for ``(1-1/D)^m``;
``L9num / D^9`` is the odd Taylor lower bound.  ``Up8num/(D+1)^8`` is
the corresponding next-scale upper bound.

The common positive denominator used below is

    DEN = D^18 * (D^2 - 1)^4 * (D + 1)^15.

For ``A = U8num`` (respectively ``L9num``), ``envelope_numerator`` is
exactly ``DEN`` times ``E8`` (respectively ``E9``), where

    E_q = T_q(D,n)^2*K + Base,
    K = P(D,n+1) - 60*D^2*J(D,n+1),
    Base = -P(D,n) + 15630*D^4
           + 60*D^2*(48*D^4*Clo + J(D,n) - 6*D^3).

Here ``J`` and ``P`` are the existing Lean polynomials
``lowerSixDiscreteHermiteFluxPoly`` and
``lowerSixHermiteSecondFluxPoly``, and ``Clo`` is the one-sided
slope-square envelope described by ``low_carrier_numerator``.

Two exact projective charts cover the natural corridor:

* chart A: ``n >= 64`` and ``n^2 <= D <= 2*n^2``.  Set
  ``s=1/n``, ``r=(D-n^2)/n^2``, ``x=64*s``.  Thus ``x,r in [0,1]``.
* chart B: ``n >= 91`` and ``n/2 <= D <= n^2``.  Set
  ``s=1/n``, ``r=D/n^2`` and
  ``r=z+(s/2)*(1-z)``, ``x=91*s``.  Thus ``x,z in [0,1]``.

After multiplying by ``s^89``, the transformed numerators have
nonnegative tensor-product Bernstein coefficients at the native degrees:

    chart A: E8 degree (83,44), E9 degree (87,44)
    chart B: E8 degree (85,44), E9 degree (87,44).

The sign-safe step split uses two further exact certificates:

* for ``D >= 8191`` and ``0 <= n <= D``, ``T9(D,n) >= 0``;
  the chart ``h=x/8191``, ``t=n/D=z`` has Bernstein degree ``(8,9)``;
* for ``D >= 8191`` and ``D <= n <= 2D``, ``Base >= 0``;
  the chart ``h=x/8191``, ``t=n/D=1+z`` has degree ``(41,22)``.

Finally, the next-slope Taylor floor ``L1`` is nonnegative on both
corridor charts: degree ``(15,8)`` and homogeneous clearing exponent 16.

Run this file to recompute and assert all four certificates.
"""

from __future__ import annotations

from fractions import Fraction
import gc
from math import comb

import sympy as sp


D, n = sp.symbols("D n")
m = 2 * n + 1


def falling_binomial(j: int) -> sp.Expr:
    return sp.prod(m - i for i in range(j)) / sp.factorial(j)


def alternating_taylor_numerator(base: sp.Expr, order: int) -> sp.Expr:
    """Numerator of T_order(1/base,m) over base^order."""
    return sp.Poly(
        sum(
            (-1) ** j * falling_binomial(j) * base ** (order - j)
            for j in range(order + 1)
        ),
        D,
        n,
    ).as_expr()


U8NUM = alternating_taylor_numerator(D, 8)
L9NUM = alternating_taylor_numerator(D, 9)
UP8NUM = alternating_taylor_numerator(D + 1, 8)

R = D**2 - 1
H = 2 * R + 1

# If v=1/R and e=2v+v^2, then
# F=1+n^2*e+C_2(n^2)*e^2 = FNUM/R^4.
FNUM = sp.expand(
    R**4
    + n**2 * H * R**2
    + (n**2 * (n**2 - 1) / 2) * H**2
)

# L1=n-(n+1)T8(1/(D+1)); U0=n-(n+1)T9(1/D).
L1NUM = sp.expand(n * (D + 1) ** 8 - (n + 1) * UP8NUM)
U0NUM = sp.expand(n * D**9 - (n + 1) * L9NUM)

# 4*L1^2-(12/(D+1)+1/(D+1)^3)n^2 over (D+1)^16.
NEXT_BRACKET_NUM = sp.expand(
    4 * L1NUM**2
    - n**2 * (12 * (D + 1) ** 2 + 1) * (D + 1) ** 13
)

# 4*U0^2-(12/D+1/D^3)n^2 over D^18.
OLD_BRACKET_NUM = sp.expand(
    4 * U0NUM**2 - n**2 * (12 * D**2 + 1) * D**15
)

DEN = D**18 * R**4 * (D + 1) ** 15

# DEN*Clo.  (The minimal common denominator of Clo has D^17; the extra
# factor D is retained so that both E8 and E9 use exactly DEN.)
LOW_CARRIER_NUM = sp.Poly(
    D**18 * FNUM * NEXT_BRACKET_NUM
    - D * R**4 * (D + 1) ** 15 * OLD_BRACKET_NUM,
    D,
    n,
)


def J(x: sp.Expr) -> sp.Expr:
    return (
        192 * x * D**4
        + 384 * x**3 * D**3
        - 6 * x * D**3
        - 384 * x**5 * D**2
        + 576 * x**4 * D**2
        + 184 * x**3 * D**2
        + 224 * x**5 * D
        - 256 * x**7
        + 576 * x**6
        + 3 * D**3
    )


def P(x: sp.Expr) -> sp.Expr:
    return (
        -15750 * x * D**4
        - 45560 * x**3 * D**3
        + 10976 * x**5 * D**2
        - 30848 * x**7 * D
        - 4608 * x**9
    )


K = sp.Poly(sp.expand(P(n + 1) - 60 * D**2 * J(n + 1)), D, n)
BASE_POLY = sp.Poly(
    sp.expand(-P(n) + 15630 * D**4 + 60 * D**2 * (J(n) - 6 * D**3)),
    D,
    n,
)
DEN_POLY = sp.Poly(DEN, D, n)


def envelope_numerator(taylor_num: sp.Expr, denominator_power: int) -> sp.Poly:
    """Return DEN*E8 or DEN*E9 as a polynomial in (D,n)."""
    return (
        sp.Poly(taylor_num**2, D, n)
        * K
        * sp.Poly(sp.cancel(DEN / D**denominator_power), D, n)
        + BASE_POLY * DEN_POLY
        + LOW_CARRIER_NUM.mul_ground(2880) * sp.Poly(D**6, D, n)
    )


E8_NUM = envelope_numerator(U8NUM, 16)
E9_NUM = envelope_numerator(L9NUM, 18)
BASE_FULL_NUM = (
    BASE_POLY * DEN_POLY
    + LOW_CARRIER_NUM.mul_ground(2880) * sp.Poly(D**6, D, n)
)


def exact_fraction(c: sp.Expr) -> Fraction:
    """Convert a SymPy rational without truncating its denominator."""
    return Fraction(int(c.p), int(c.q))


def chart_a_power_coefficients(poly: sp.Poly) -> tuple[dict[tuple[int, int], Fraction], int]:
    """Coefficients after D=n^2(1+r), n=1/s, x=64s, times s^M."""
    terms = [
        (ij, exact_fraction(c)) for ij, c in poly.terms()
    ]
    M = max(2 * i + j for (i, j), _ in terms)
    out: dict[tuple[int, int], Fraction] = {}
    for (i, j), c in terms:
        sx = M - (2 * i + j)
        for rp in range(i + 1):
            key = (sx, rp)
            out[key] = out.get(key, Fraction(0)) + c * Fraction(
                comb(i, rp), 64**sx
            )
    return {key: value for key, value in out.items() if value}, M


def chart_b_power_coefficients(poly: sp.Poly) -> tuple[dict[tuple[int, int], Fraction], int]:
    """Coefficients after D=r/s^2, n=1/s and r=z+x/182*(1-z), x=91s."""
    terms = [
        (ij, exact_fraction(c)) for ij, c in poly.terms()
    ]
    M = max(2 * i + j for (i, j), _ in terms)
    out: dict[tuple[int, int], Fraction] = {}
    for (i, j), c in terms:
        spow = M - (2 * i + j)
        # r^i = sum_l C(i,l) z^(i-l) [x/182*(1-z)]^l.
        for ell in range(i + 1):
            prefactor = c * Fraction(
                comb(i, ell), 91**spow * 182**ell
            )
            xpow = spow + ell
            for q in range(ell + 1):
                zpow = i - ell + q
                value = prefactor * comb(ell, q) * (-1) ** q
                key = (xpow, zpow)
                out[key] = out.get(key, Fraction(0)) + value
    return {key: value for key, value in out.items() if value}, M


def low_step_power_coefficients(poly: sp.Poly) -> tuple[dict[tuple[int, int], Fraction], int]:
    """D=1/h, n=t/h, h=x/8191, t=z; used for T9 on n<=D."""
    terms = [(ij, exact_fraction(c)) for ij, c in poly.terms()]
    M = max(i + j for (i, j), _ in terms)
    out: dict[tuple[int, int], Fraction] = {}
    for (i, j), c in terms:
        xpow = M - i - j
        key = (xpow, j)
        out[key] = out.get(key, Fraction(0)) + c * Fraction(1, 8191**xpow)
    return {key: value for key, value in out.items() if value}, M


def high_base_power_coefficients(poly: sp.Poly) -> tuple[dict[tuple[int, int], Fraction], int]:
    """D=1/h, n=t/h, h=x/8191, t=1+z; used for Base on D<=n<=2D."""
    terms = [(ij, exact_fraction(c)) for ij, c in poly.terms()]
    M = max(i + j for (i, j), _ in terms)
    out: dict[tuple[int, int], Fraction] = {}
    for (i, j), c in terms:
        xpow = M - i - j
        for zpow in range(j + 1):
            key = (xpow, zpow)
            out[key] = out.get(key, Fraction(0)) + c * Fraction(
                comb(j, zpow), 8191**xpow
            )
    return {key: value for key, value in out.items() if value}, M


def bernstein_coefficients(
    power: dict[tuple[int, int], Fraction], degree_x: int, degree_y: int
) -> dict[tuple[int, int], Fraction]:
    """Tensor Bernstein coefficients, with binomial factors in the basis."""
    answer: dict[tuple[int, int], Fraction] = {}
    for i in range(degree_x + 1):
        for j in range(degree_y + 1):
            value = Fraction(0)
            for (a, b), coefficient in power.items():
                if a <= i and b <= j:
                    value += (
                        coefficient
                        * Fraction(comb(i, a), comb(degree_x, a))
                        * Fraction(comb(j, b), comb(degree_y, b))
                    )
            answer[i, j] = value
    return answer


def check(label: str, poly: sp.Poly, chart: str, expected_M: int = 89) -> None:
    transform = {
        "A": chart_a_power_coefficients,
        "B": chart_b_power_coefficients,
        "T": low_step_power_coefficients,
        "C": high_base_power_coefficients,
    }[chart]
    power, M = transform(poly)
    degree_x = max(a for a, _ in power)
    degree_y = max(b for _, b in power)
    bernstein = bernstein_coefficients(power, degree_x, degree_y)
    assert M == expected_M
    assert all(value >= 0 for value in bernstein.values())
    minimum = min(bernstein.items(), key=lambda item: item[1])
    print(
        f"{label} chart {chart}: M={M}, degree=({degree_x},{degree_y}), "
        f"power_terms={len(power)}, bernstein_min={minimum}",
        flush=True,
    )
    del bernstein
    del power
    gc.collect()


def main() -> None:
    check("E8", E8_NUM, "A")
    gc.collect()
    check("E9", E9_NUM, "A")
    gc.collect()
    check("E8", E8_NUM, "B")
    gc.collect()
    check("E9", E9_NUM, "B")
    gc.collect()
    check("T9", sp.Poly(L9NUM, D, n), "T", 9)
    gc.collect()
    check("Base", BASE_FULL_NUM, "C", 50)
    gc.collect()
    check("L1", sp.Poly(L1NUM, D, n), "A", 16)
    gc.collect()
    check("L1", sp.Poly(L1NUM, D, n), "B", 16)


if __name__ == "__main__":
    main()
