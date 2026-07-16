#!/usr/bin/env python3
"""Emit small exact raw factors used by the staged Base bridge."""

from __future__ import annotations

import sympy as sp

import lower_six_tail_second_flux_certificate as source


def print_raw(name: str, expression: sp.Expr) -> None:
    poly = sp.Poly(sp.expand(expression), source.D, source.n)
    terms: list[tuple[int, int, int]] = []
    for (d_exponent, n_exponent), coefficient in poly.terms():
        value = source.exact_fraction(coefficient)
        assert value.denominator == 1
        terms.append((n_exponent, d_exponent, value.numerator))
    terms.sort()
    print(f"def {name} : RingNormaliser.RawPoly := [")
    for n_exponent, d_exponent, coefficient in terms:
        if d_exponent == 0 and n_exponent == 0:
            monomial = "[]"
        elif d_exponent == 0:
            monomial = f"[{n_exponent}]"
        else:
            monomial = f"[{n_exponent}, {d_exponent}]"
        print(f"  ({monomial}, {coefficient}),")
    print("]")
    print()


def main() -> None:
    print("/- Exact generated raw factors for the Base semantic bridge. -/")
    print()
    print("import YMGap.Continuum.RingNormaliser")
    print()
    print("namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticFactors")
    print()
    print("open YMGap.Continuum")
    print()
    print_raw("tailBaseSemanticL1Raw", 2520 * source.L1NUM)
    print_raw("tailBaseSemanticTwoFRaw", 2 * source.FNUM)
    print("end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticFactors")


if __name__ == "__main__":
    main()
