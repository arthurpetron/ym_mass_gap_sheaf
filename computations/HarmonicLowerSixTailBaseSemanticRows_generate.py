#!/usr/bin/env python3
"""Emit sparse N-exponent rows for the exact Base semantic bridge.

The five rows are the integer factorization used by
``HarmonicLowerSixTailBaseSemanticBridge.lean``.  Their exact sum is checked
against ``178605 * BASE_FULL_NUM`` before any Lean source is printed.
"""

from __future__ import annotations

import sympy as sp

import lower_six_tail_second_flux_certificate as source


CLEAR_SCALE = 178605


def as_poly(expression: sp.Expr) -> sp.Poly:
    return sp.Poly(sp.expand(expression), source.D, source.n)


def pieces() -> list[sp.Poly]:
    D = source.D
    n = source.n
    dp = D + 1
    r = source.R
    two_f = 2 * source.FNUM
    l1_cleared = 2520 * source.L1NUM
    u0_cleared = 22680 * source.U0NUM
    return [
        as_poly(CLEAR_SCALE * source.BASE_POLY.as_expr() * source.DEN),
        as_poly(162 * D**18 * two_f * l1_cleared**2 * D**6),
        as_poly(
            -257191200
            * D**18
            * two_f
            * n**2
            * (12 * dp**2 + 1)
            * dp**13
            * D**6
        ),
        as_poly(-4 * D * r**4 * dp**15 * u0_cleared**2 * D**6),
        as_poly(
            514382400
            * D
            * r**4
            * dp**15
            * n**2
            * (12 * D**2 + 1)
            * D**15
            * D**6
        ),
    ]


def row_terms(poly: sp.Poly, n_exponent: int) -> list[tuple[int, int]]:
    terms: list[tuple[int, int]] = []
    for (d_exponent, n_degree), coefficient in poly.terms():
        if n_degree != n_exponent:
            continue
        value = source.exact_fraction(coefficient)
        assert value.denominator == 1
        terms.append((d_exponent, value.numerator))
    return sorted(terms)


def print_rows(name: str, poly: sp.Poly) -> None:
    print(f"def {name} : List RingNormaliser.RawPoly := [")
    for n_exponent in range(23):
        terms = row_terms(poly, n_exponent)
        rendered = ", ".join(
            f"([%d, %d], %d)" % (n_exponent, d_exponent, coefficient)
            for d_exponent, coefficient in terms
        )
        print(f"  [{rendered}],")
    print("]")
    print()


def main() -> None:
    component_polys = pieces()
    total = sum(component_polys[1:], component_polys[0])
    expected = source.BASE_FULL_NUM.mul_ground(CLEAR_SCALE)
    difference = total - expected
    if not difference.is_zero:
        print("semantic-row factorization mismatch", difference.terms()[:8])
        raise AssertionError("semantic-row factorization mismatch")
    assert [len(poly.terms()) for poly in component_polys] == [
        200,
        357,
        66,
        682,
        26,
    ]
    assert len(expected.terms()) == 691

    print("/- Exact generated sparse rows for the Base semantic bridge. -/")
    print()
    print("import YMGap.Continuum.RingNormaliser")
    print()
    print("namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows")
    print()
    print("open YMGap.Continuum")
    print()
    for index, poly in enumerate(component_polys):
        print_rows(f"tailBaseSemanticPiece{index}Rows", poly)
    print_rows("tailBaseSemanticTotalRows", expected)
    print("end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows")


if __name__ == "__main__":
    main()
