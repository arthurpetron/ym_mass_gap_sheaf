#!/usr/bin/env python3
"""Exact Bernstein scout for the heat-weighted SU(2) fusion box.

For a cutoff ``N`` and channel ``s``, form the integer-coefficient polynomial

    boxSum(w,N,s+1)^2 - boxSum(w,N,s) boxSum(w,N,s+2).

Every exponent is even.  After the physical change of variables ``u=4*w^2``
the script elevates the polynomial to its full standard Bernstein degree and
checks every coefficient with exact ``Fraction`` arithmetic.  A successful
run is finite evidence for the certificate family; it is not a Lean proof.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from math import comb
from typing import DefaultDict, Iterable

Polynomial = dict[int, int]


def c4(label: int) -> int:
    return label * (label + 2)


def fusion_ok(left: int, right: int, channel: int) -> bool:
    return (
        abs(left - right) <= channel <= left + right
        and (left + right + channel) % 2 == 0
    )


def box_polynomial(cutoff: int, channel: int) -> Polynomial:
    """Return ``boxSum`` as ``exponent -> integer coefficient``."""
    result: DefaultDict[int, int] = defaultdict(int)
    for left in range(cutoff + 1):
        for right in range(cutoff + 1):
            if fusion_ok(left, right, channel):
                result[c4(left) + c4(right)] += (left + 1) * (right + 1)
    return dict(result)


def multiply(left: Polynomial, right: Polynomial) -> Polynomial:
    result: DefaultDict[int, int] = defaultdict(int)
    for left_degree, left_coefficient in left.items():
        for right_degree, right_coefficient in right.items():
            result[left_degree + right_degree] += (
                left_coefficient * right_coefficient
            )
    return dict(result)


def box_difference_polynomial(cutoff: int, channel: int) -> Polynomial:
    middle_square = multiply(
        box_polynomial(cutoff, channel + 1),
        box_polynomial(cutoff, channel + 1),
    )
    outer_product = multiply(
        box_polynomial(cutoff, channel),
        box_polynomial(cutoff, channel + 2),
    )
    degrees = middle_square.keys() | outer_product.keys()
    return {
        degree: middle_square.get(degree, 0) - outer_product.get(degree, 0)
        for degree in degrees
    }


def physical_bernstein_row(polynomial: Polynomial) -> list[Fraction]:
    """Elevate an even polynomial to Bernstein form in ``u=4*w^2``.

    If ``P(w)=sum a_(2k) w^(2k)=sum a_(2k) 4^(-k) u^k`` and ``D`` is
    the largest ``k``, its standard degree-``D`` Bernstein coefficient is

        beta_j = sum_(k<=j) a_(2k) 4^(-k) C(j,k)/C(D,k).
    """
    if not polynomial:
        return [Fraction(0)]
    odd_degrees = [degree for degree in polynomial if degree % 2 != 0]
    if odd_degrees:
        raise ValueError(f"odd heat exponents encountered: {odd_degrees[:4]}")
    degree = max(polynomial) // 2
    return [
        sum(
            (
                Fraction(polynomial.get(2 * power, 0), 4**power)
                * Fraction(comb(index, power), comb(degree, power))
                for power in range(index + 1)
            ),
            Fraction(0),
        )
        for index in range(degree + 1)
    ]


def cutoffs(args: argparse.Namespace) -> Iterable[int]:
    if args.cutoff is not None:
        return [args.cutoff]
    return range(args.min_cutoff, args.max_cutoff + 1)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, help="check one cutoff N")
    parser.add_argument("--min-cutoff", type=int, default=1)
    parser.add_argument("--max-cutoff", type=int, default=12)
    args = parser.parse_args()
    if args.cutoff is not None and args.cutoff < 0:
        parser.error("--cutoff must be nonnegative")
    if args.min_cutoff < 0 or args.max_cutoff < args.min_cutoff:
        parser.error("invalid cutoff interval")

    all_nonnegative = True
    print("N  modes  max-degree  negative-coefficients")
    for cutoff in cutoffs(args):
        negative = 0
        max_degree = 0
        for channel in range(max(0, 2 * cutoff - 1)):
            row = physical_bernstein_row(
                box_difference_polynomial(cutoff, channel)
            )
            max_degree = max(max_degree, len(row) - 1)
            negative += sum(coefficient < 0 for coefficient in row)
        all_nonnegative = all_nonnegative and negative == 0
        print(
            f"{cutoff:>2}  {max(0, 2 * cutoff - 1):>5}"
            f"  {max_degree:>10}  {negative:>21}"
        )
    return 0 if all_nonnegative else 1


if __name__ == "__main__":
    raise SystemExit(main())
