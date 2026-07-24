#!/usr/bin/env python3
"""Exact Bernstein-basis scout for the physical Core-B quotient.

Put ``u = 4 w^2``.  On the physical interval ``0 <= w <= 1/2`` we have
``0 <= u <= 1``, while the fixed endpoint satisfies ``wH^2 = 1/4``.
For one canonical cell

    (s, r) = (step + 1, length - 1 - step),

this module expands the *actual eleven-family square-gap quotient* from
``CoreBUniversalSquareGap`` as an exact rational polynomial in ``u``.  It
then removes the forced lowest power of ``u`` and changes the remaining
polynomial from the power basis to the Bernstein basis on ``[0,1]``.

If

    P(u) = sum_{k=0}^d b_k * C(d,k) * u^k * (1-u)^(d-k)

and every ``b_k >= 0``, then ``P`` is nonnegative throughout the physical
interval.  The conversion used here is exact:

    b_k = sum_{i=0}^k a_i * C(k,i) / C(d,i)

for ``P(u) = sum_i a_i u^i``.

The striking finite observation is that every *individual canonical cell*
tested by this scout has nonnegative Bernstein coefficients.  Thus the
positivity appears before diagonal summation, not only after cancellation.
If this pattern admits an all-index proof, it would bypass the much coarser
reserve-versus-adverse-tail budget.

This is an exact finite computational scout, not a Lean theorem and not an
all-length proof.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import cache
from math import comb
from typing import TYPE_CHECKING

import sympy as sp

if TYPE_CHECKING:
    from computations.core_b_atomwise_tail_scout import (
        canonical_content,
        predicted_content_shift,
        specialized_components,
    )
else:
    try:
        from computations.core_b_atomwise_tail_scout import (
            canonical_content,
            predicted_content_shift,
            specialized_components,
        )
    except ModuleNotFoundError:
        # Support direct execution as
        # ``python3 computations/core_b_bernstein_scout.py``.
        from core_b_atomwise_tail_scout import (
            canonical_content,
            predicted_content_shift,
            specialized_components,
        )


u_symbol = sp.symbols("u", nonnegative=True)
_endpoint_square = sp.Rational(1, 4)
_physical_square = u_symbol / 4


def _hom_chain(base: int, length: int) -> sp.Expr:
    """The exact homogeneous chain at ``(wH^2, w^2)``."""
    return sp.Add(
        *(
            _endpoint_square ** (base + length - 1 - index)
            * _physical_square ** (base + index)
            for index in range(length)
        )
    )


def _oriented_chain(numerator_half: int, midpoint_half: int) -> sp.Expr:
    """Mirror ``CoreBUniversalSquareGap.orientedHomChain`` exactly."""
    if midpoint_half <= numerator_half:
        return _hom_chain(
            midpoint_half, numerator_half - midpoint_half
        )
    return -_hom_chain(
        numerator_half, midpoint_half - numerator_half
    )


def canonical_cell_quotient(length: int, step: int) -> sp.Poly:
    """Exact quotient polynomial of one canonical residual cell.

    The pure window/window component pair ``(0,0)`` is omitted exactly as in
    ``CoreBStructuralRecurrence``.  All other four-by-three component pairs
    are the eleven quotient families.
    """
    if length < 1:
        raise ValueError("length must be positive")
    if not 0 <= step < length:
        raise ValueError("step must satisfy 0 <= step < length")

    row = step + 1
    offset = length - 1 - step
    numerator_components, midpoint_components = specialized_components(
        row, offset
    )
    quotient = sp.Integer(0)
    for numerator_index, numerator in enumerate(numerator_components):
        for midpoint_index, midpoint in enumerate(midpoint_components):
            if (numerator_index, midpoint_index) == (0, 0):
                continue
            for numerator_coefficient, numerator_exponent in numerator:
                for midpoint_coefficient, midpoint_exponent in midpoint:
                    if numerator_exponent % 2 or midpoint_exponent % 2:
                        raise AssertionError("canonical atom exponent is odd")
                    quotient += (
                        numerator_coefficient
                        * midpoint_coefficient
                        * _oriented_chain(
                            numerator_exponent // 2,
                            midpoint_exponent // 2,
                        )
                    )
    return sp.Poly(sp.expand(quotient), u_symbol, domain=sp.QQ)


def canonical_cumulative_quotient(length: int) -> sp.Poly:
    """Exact row-one-origin quotient polynomial at one positive length."""
    if length < 1:
        raise ValueError("length must be positive")
    return sp.Poly(
        sp.expand(
            sum(
                (
                    canonical_cell_quotient(length, step).as_expr()
                    for step in range(length)
                ),
                sp.Integer(0),
            )
        ),
        u_symbol,
        domain=sp.QQ,
    )


def forced_zero_order(poly: sp.Poly) -> int:
    """Lowest nonzero power; zero for a nonzero constant polynomial."""
    if poly.is_zero:
        raise ValueError("the zero polynomial has no finite zero order")
    return int(min(monomial[0] for monomial, _ in poly.terms()))


def remove_forced_zero_power(poly: sp.Poly) -> tuple[int, sp.Poly]:
    """Return ``(m, P)`` with ``poly = u^m P`` and ``P(0) != 0``."""
    order = forced_zero_order(poly)
    reduced = sp.Poly(
        sp.cancel(poly.as_expr() / u_symbol**order),
        u_symbol,
        domain=sp.QQ,
    )
    if reduced.eval(0) == 0:
        raise AssertionError("failed to remove the complete zero power")
    return order, reduced


def power_to_bernstein(poly: sp.Poly) -> tuple[sp.Rational, ...]:
    """Exact degree-preserving power-to-Bernstein conversion on ``[0,1]``."""
    if poly.is_zero:
        return (sp.Rational(0),)
    degree = poly.degree()
    power_coefficients = [
        sp.Rational(poly.nth(index)) for index in range(degree + 1)
    ]
    return tuple(
        sp.factor(
            sum(
                (
                    power_coefficients[index]
                    * sp.Rational(comb(k, index), comb(degree, index))
                    for index in range(k + 1)
                ),
                sp.Rational(0),
            )
        )
        for k in range(degree + 1)
    )


def bernstein_reconstruction(
    coefficients: tuple[sp.Rational, ...],
) -> sp.Poly:
    """Reconstruct a polynomial from its Bernstein coefficients."""
    degree = len(coefficients) - 1
    return sp.Poly(
        sp.expand(
            sum(
                (
                    coefficient
                    * comb(degree, index)
                    * u_symbol**index
                    * (1 - u_symbol) ** (degree - index)
                    for index, coefficient in enumerate(coefficients)
                ),
                sp.Integer(0),
            )
        ),
        u_symbol,
        domain=sp.QQ,
    )


@dataclass(frozen=True)
class BernsteinCertificate:
    """Exact finite certificate data for one quotient polynomial."""

    zero_order: int
    reduced_degree: int
    coefficients: tuple[sp.Rational, ...]
    reconstruction_exact: bool
    nonnegative: bool
    strictly_positive: bool


def bernstein_certificate(poly: sp.Poly) -> BernsteinCertificate:
    """Compute and independently reconstruct an exact Bernstein certificate."""
    order, reduced = remove_forced_zero_power(poly)
    coefficients = power_to_bernstein(reduced)
    return BernsteinCertificate(
        zero_order=order,
        reduced_degree=reduced.degree(),
        coefficients=coefficients,
        reconstruction_exact=(
            bernstein_reconstruction(coefficients) == reduced
        ),
        nonnegative=all(coefficient >= 0 for coefficient in coefficients),
        strictly_positive=all(coefficient > 0 for coefficient in coefficients),
    )


def canonical_high_degree(length: int) -> int:
    """The observed/proved atom endpoint-degree ceiling ``(n+2)(n+4)``."""
    if length < 1:
        raise ValueError("length must be positive")
    return (length + 2) * (length + 4)


def predicted_cell_zero_order(length: int, step: int) -> int:
    """Centered-content prediction for the forced physical-square power."""
    if length < 1:
        raise ValueError("length must be positive")
    if not 0 <= step < length:
        raise ValueError("step must satisfy 0 <= step < length")
    center, parity = divmod(length, 2)
    row = step + 1
    return (
        canonical_content(length)
        + predicted_content_shift(parity, center, row)
    ) // 2


def cleared_unnormalized_bernstein_row(
    length: int, step: int
) -> tuple[int, ...]:
    """Integer coefficients in the unnormalised Bernstein basis.

    ``4^(2 H)`` clears every endpoint and physical-square denominator, where
    ``H = (length+2)(length+4)``.  Multiplication by ``C(D,j)`` changes the
    normalized Bernstein coefficient ``b_j`` to the coefficient of
    ``u^j (1-u)^(D-j)``.  This is the natural row to formalize in Lean,
    because its positivity is an integer statement.
    """
    certificate = bernstein_certificate(
        canonical_cell_quotient(length, step)
    )
    degree = certificate.reduced_degree
    clearing_factor = 4 ** (2 * canonical_high_degree(length))
    row: list[int] = []
    for index, coefficient in enumerate(certificate.coefficients):
        cleared = sp.cancel(
            coefficient * comb(degree, index) * clearing_factor
        )
        if not cleared.is_Integer:
            raise AssertionError("the claimed Bernstein clearing is not integral")
        row.append(int(cleared))
    return tuple(row)


@cache
def direct_cleared_unnormalized_bernstein_row(
    length: int, step: int
) -> tuple[int, ...]:
    """Build the same cleared row directly from the actual atom ledger.

    This avoids polynomial expansion and basis conversion.  One oriented
    chain monomial with physical exponent ``e`` and total squared degree
    ``E`` contributes

    ``sign * pair_coefficient * 4^(2H-E) * C(D-(e-L), j-(e-L))``

    to unnormalised Bernstein coordinate ``j``.  This is exactly the finite
    integer sum that the Lean classifier/reconstruction theorem should use.
    """
    if length < 1:
        raise ValueError("length must be positive")
    if not 0 <= step < length:
        raise ValueError("step must satisfy 0 <= step < length")
    high = canonical_high_degree(length)
    low = predicted_cell_zero_order(length, step)
    degree = high - low
    row = [0] * (degree + 1)
    numerator_components, midpoint_components = specialized_components(
        step + 1, length - 1 - step
    )
    for numerator_index, numerator in enumerate(numerator_components):
        for midpoint_index, midpoint in enumerate(midpoint_components):
            if (numerator_index, midpoint_index) == (0, 0):
                continue
            for numerator_coefficient, numerator_exponent in numerator:
                for midpoint_coefficient, midpoint_exponent in midpoint:
                    numerator_half = numerator_exponent // 2
                    midpoint_half = midpoint_exponent // 2
                    if midpoint_half <= numerator_half:
                        sign = 1
                        base = midpoint_half
                        chain_length = numerator_half - midpoint_half
                    else:
                        sign = -1
                        base = numerator_half
                        chain_length = midpoint_half - numerator_half
                    total_degree = (
                        numerator_half + midpoint_half - 1
                    )
                    atom_scale = 4 ** (2 * high - total_degree)
                    pair_coefficient = (
                        numerator_coefficient * midpoint_coefficient
                    )
                    for chain_index in range(chain_length):
                        physical_exponent = base + chain_index
                        if not low <= physical_exponent <= high:
                            raise AssertionError(
                                "atom power lies outside the claimed degree range"
                            )
                        shifted_exponent = physical_exponent - low
                        for bernstein_index in range(
                            shifted_exponent, degree + 1
                        ):
                            row[bernstein_index] += (
                                sign
                                * pair_coefficient
                                * atom_scale
                                * comb(
                                    degree - shifted_exponent,
                                    bernstein_index - shifted_exponent,
                                )
                            )
    return tuple(row)


def pascal_degree_elevate(
    row: tuple[int, ...], extra_degree: int
) -> tuple[int, ...]:
    """Elevate an unnormalised Bernstein row by Pascal convolution.

    If ``row`` has degree ``D``, its entries multiply
    ``u^j (1-u)^(D-j)`` without binomial normalisation.  Multiplication by
    ``(u + (1-u))^extra_degree = 1`` gives the same polynomial in degree
    ``D + extra_degree`` and changes the row by

    ``elevated[j] = sum_q C(extra_degree,q) * row[j-q]``.

    This identity is exact for every integer row; it is not a finite-grid
    observation.
    """
    if extra_degree < 0:
        raise ValueError("extra_degree must be nonnegative")
    return tuple(
        sum(
            (
                row[index] * comb(extra_degree, target - index)
                for index in range(
                    max(0, target - extra_degree),
                    min(target, len(row) - 1) + 1,
                )
            ),
            0,
        )
        for target in range(len(row) + extra_degree)
    )


def predicted_pascal_step_direction(length: int, step: int) -> int:
    """Observed sign of the next-step row difference.

    The return value is ``+1`` on the increasing side of the conjectured
    Pascal-unimodal step profile and ``-1`` on its decreasing side.  The
    finite checker below tests this prediction exactly, but this function
    does not assert an all-index proof.
    """
    if length < 2:
        raise ValueError("length must have two cells")
    if not 0 <= step + 1 < length:
        raise ValueError("step must have a successor cell")
    center, parity = divmod(length, 2)
    if parity == 0:
        return 1 if step < center - 1 else -1
    return 1 if step < center else -1


def signed_pascal_step_difference(
    length: int, step: int
) -> tuple[int, ...]:
    """Exact signed adjacent-cell difference at the target cell's degree.

    The earlier row is first elevated to the later row's degree.  Multiplying
    by the predicted direction makes the conjectured recurrence remainder
    positive.
    """
    direction = predicted_pascal_step_direction(length, step)
    current = direct_cleared_unnormalized_bernstein_row(length, step)
    following = direct_cleared_unnormalized_bernstein_row(length, step + 1)
    extra_degree = len(following) - len(current)
    if extra_degree < 0:
        raise AssertionError("canonical cell degree unexpectedly decreased")
    elevated = pascal_degree_elevate(current, extra_degree)
    return tuple(
        direction * (right - left)
        for left, right in zip(elevated, following, strict=True)
    )


def verify_cellwise_bernstein(maximum_length: int) -> bool:
    """Check exact reconstruction and nonnegativity for every requested cell."""
    return all(
        certificate.reconstruction_exact and certificate.nonnegative
        for length in range(1, maximum_length + 1)
        for certificate in (
            bernstein_certificate(
                canonical_cell_quotient(length, step)
            )
            for step in range(length)
        )
    )


def verify_direct_integer_rows(maximum_length: int) -> bool:
    """Fast extended falsification grid for the direct actual-atom row."""
    return all(
        all(
            coefficient > 0
            for coefficient in direct_cleared_unnormalized_bernstein_row(
                length, step
            )
        )
        for length in range(1, maximum_length + 1)
        for step in range(length)
    )


def verify_pascal_step_unimodality(maximum_length: int) -> bool:
    """Finite exact falsification grid for the step-direction conjecture."""
    return all(
        all(
            coefficient > 0
            for coefficient in signed_pascal_step_difference(length, step)
        )
        for length in range(2, maximum_length + 1)
        for step in range(length - 1)
    )


def _report(maximum_length: int) -> None:
    for length in range(1, maximum_length + 1):
        certificates = [
            bernstein_certificate(canonical_cell_quotient(length, step))
            for step in range(length)
        ]
        cumulative = bernstein_certificate(
            canonical_cumulative_quotient(length)
        )
        cleared_positive = all(
            all(
                value > 0
                for value in cleared_unnormalized_bernstein_row(length, step)
            )
            for step in range(length)
        )
        direct_rows_match = all(
            direct_cleared_unnormalized_bernstein_row(length, step)
            == cleared_unnormalized_bernstein_row(length, step)
            for step in range(length)
        )
        print(
            f"length={length:2d} "
            f"cells={len(certificates):2d} "
            f"zero_orders="
            f"{min(c.zero_order for c in certificates)}.."
            f"{max(c.zero_order for c in certificates)} "
            f"degrees="
            f"{min(c.reduced_degree for c in certificates)}.."
            f"{max(c.reduced_degree for c in certificates)} "
            f"cell_nonnegative={all(c.nonnegative for c in certificates)} "
            f"cell_strict={all(c.strictly_positive for c in certificates)} "
            f"cleared_integer_positive={cleared_positive} "
            f"direct_rows_match={direct_rows_match} "
            f"cumulative_nonnegative={cumulative.nonnegative}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-length", type=int, default=8)
    args = parser.parse_args()
    if args.max_length < 1:
        parser.error("--max-length must be positive")
    _report(args.max_length)


if __name__ == "__main__":
    main()
