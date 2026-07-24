#!/usr/bin/env python3
"""Exact scout for diagonal-cumulative Core-B payments.

The all-row scout found that the constant-reserve tactic fails at ``(s, 0)``
from row four onward.  The proved recurrence

    C(s, r, n) = sum_{t < n} R(s+t, r+n-1-t)

allows those residuals to be paid together along a diagonal.  This module
forms the exact sparse quotient of that cumulative sum and tests the same
physical-simplex payment used by the finite-cell proofs: discard positive
nonconstant monomials and bound ``w^a h^b <= 4^-(a+b)``.

The script also checks the sharper consumer-only family ``C(1,0,n)`` at the
actual worst endpoint ``wH=1/2``.  That check uses the correct discount
``2^-(a+b)`` and exposes positive collected reserves in both parities.

This is a falsification/design scout, not a proof of the all-index formula.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import cache

try:
    from computations.CoreBResidualAllRows_scout import (
        families_for,
        integer_at,
        specialized_quotient,
    )
except ModuleNotFoundError:
    from CoreBResidualAllRows_scout import (  # type: ignore[import-not-found]
        families_for,
        integer_at,
        specialized_quotient,
    )

Monomial = tuple[int, int]
SparsePolynomial = dict[Monomial, int]


@cache
def residual_quotient(row: int, offset: int) -> tuple[int, tuple[tuple[Monomial, int], ...]]:
    """Return a cached sparse quotient and its common ``(wh)`` content."""
    if row < 1:
        raise ValueError("the diagonal scout starts at row one")
    if offset < 0:
        raise ValueError("offset must be nonnegative")
    content, quotient = specialized_quotient(families_for(row)[0], offset)
    data = tuple(sorted(((monomial, int(value)) for monomial, value in quotient.as_dict().items())))
    return content, data


def cumulative_quotient(row: int, offset: int, length: int) -> tuple[int, SparsePolynomial]:
    """Form the exact quotient of ``C(row, offset, length)`` sparsely."""
    if length < 1:
        raise ValueError("cumulative length must be positive")
    parts = [residual_quotient(row + step, offset + length - 1 - step) for step in range(length)]
    common_content = min(content for content, _ in parts)
    combined: defaultdict[Monomial, int] = defaultdict(int)
    for content, data in parts:
        shift = content - common_content
        for (width_power, height_power), coefficient in data:
            combined[(width_power + shift, height_power + shift)] += coefficient
    return common_content, {
        monomial: coefficient for monomial, coefficient in combined.items() if coefficient != 0
    }


@dataclass(frozen=True)
class CumulativePaymentReport:
    """Exact constant-reserve payment data for one diagonal cumulative."""

    row: int
    offset: int
    length: int
    content: int
    term_count: int
    adverse_count: int
    reserve: int
    discounted_adverse: Fraction

    @property
    def paid(self) -> bool:
        """Whether the constant reserve pays every adverse monomial."""
        return self.reserve >= 0 and self.discounted_adverse <= self.reserve


@dataclass(frozen=True)
class CanonicalConsumerReport:
    """Payment ledger for the only row-one diagonal used by Core B.

    The cross-ratio consumer asks for ``offsetDelta(wH, h, s, 0)``.  After
    the exact root split, its sole analytic cumulative is therefore
    ``C(1, 0, n)``.  Since the larger endpoint is ``wH = 1/2``, adverse
    quotient monomials are discounted by ``2^-(a+b)``, not by the stronger
    ``4^-(a+b)`` cap used in the earlier physical-simplex scout.
    """

    length: int
    content: int
    term_count: int
    adverse_count: int
    reserve: int
    discounted_adverse_at_half: Fraction
    uncancelled_adverse_at_half: Fraction
    atomwise_adverse_at_half: Fraction

    @property
    def paid_at_worst_endpoint(self) -> bool:
        """Whether the constant reserve pays the adverse block at ``wH``."""
        return self.reserve >= 0 and self.discounted_adverse_at_half <= self.reserve

    @property
    def paid_with_sixfold_slack(self) -> bool:
        """Whether even six copies of the endpoint debt fit in the reserve."""
        return (
            self.reserve >= 0
            and 6 * self.discounted_adverse_at_half <= self.reserve
        )

    @property
    def uncancelled_paid_with_fourfold_slack(self) -> bool:
        """Pay four copies even before cancellations between residual cells."""
        return (
            self.reserve >= 0
            and 4 * self.uncancelled_adverse_at_half <= self.reserve
        )

    @property
    def atomwise_paid_with_twofold_slack(self) -> bool:
        """Pay twice the adverse mass before any polynomial collection."""
        return (
            self.reserve >= 0
            and 2 * self.atomwise_adverse_at_half <= self.reserve
        )


def payment_report(row: int, offset: int, length: int) -> CumulativePaymentReport:
    """Compute the exact physical-simplex payment ledger."""
    content, data = cumulative_quotient(row, offset, length)
    adverse = [
        (monomial, -coefficient) for monomial, coefficient in data.items() if coefficient < 0
    ]
    discounted = sum(
        (
            Fraction(coefficient, 4 ** (width_power + height_power))
            for (width_power, height_power), coefficient in adverse
        ),
        Fraction(0),
    )
    return CumulativePaymentReport(
        row=row,
        offset=offset,
        length=length,
        content=content,
        term_count=len(data),
        adverse_count=len(adverse),
        reserve=data.get((0, 0), 0),
        discounted_adverse=discounted,
    )


def predicted_canonical_consumer_content(length: int) -> int:
    """Observed common ``(wh)`` content of the canonical ``C(1,0,n)``.

    Written by parity, the exact checked formulas are
    ``n=2k: 4k^2+16k+12`` and ``n=2k+1: 4k^2+20k+22``.
    """
    if length < 1:
        raise ValueError("canonical consumer length must be positive")
    quotient, parity = divmod(length, 2)
    if parity == 0:
        return 4 * quotient**2 + 16 * quotient + 12
    return 4 * quotient**2 + 20 * quotient + 22


def predicted_canonical_consumer_reserve(length: int) -> int:
    """Observed constant reserve of the canonical ``C(1,0,n)`` quotient."""
    if length < 1:
        raise ValueError("canonical consumer length must be positive")
    if length == 1:
        return 11232
    quotient, parity = divmod(length, 2)
    if parity == 0:
        k = quotient
        return 4 * (k + 1) * (k + 2) ** 6 * (k + 3)
    k = quotient
    return (
        8
        * (k + 2) ** 2
        * (k + 3) ** 2
        * (2 * (k + 2) ** 3 * (k + 4) - (2 * k + 5))
    )


def canonical_consumer_report(length: int) -> CanonicalConsumerReport:
    """Form the exact ``C(1,0,n)`` quotient and its fixed-``wH`` payment."""
    content, data = cumulative_quotient(1, 0, length)
    adverse = [
        (monomial, -coefficient)
        for monomial, coefficient in data.items()
        if coefficient < 0
    ]
    discounted = sum(
        (
            Fraction(coefficient, 2 ** (width_power + height_power))
            for (width_power, height_power), coefficient in adverse
        ),
        Fraction(0),
    )
    # A deliberately coarser ledger: retain the cancellations internal to
    # each residual quotient, but discard every cancellation between distinct
    # cells of the cumulative diagonal.  Its simpler cellwise structure is a
    # better candidate for a uniform Lean estimate.
    uncancelled = Fraction(0)
    for step in range(length):
        part_content, part_data = residual_quotient(1 + step, length - 1 - step)
        shift = part_content - content
        uncancelled += sum(
            (
                Fraction(-coefficient, 2 ** (width_power + height_power + 2 * shift))
                for (width_power, height_power), coefficient in part_data
                if coefficient < 0
            ),
            Fraction(0),
        )
    # The coarsest useful triangle ledger: split every determinant family
    # before *any* equal-monomial collection.  An adverse orientation with
    # exponent gap 2*l contributes l homogeneous-chain monomials, all having
    # the same total endpoint degree after the global content is removed.
    atomwise = Fraction(0)
    for step in range(length):
        offset = length - 1 - step
        for family in families_for(1 + step)[0]:
            a_exponent = integer_at(family.a_exponent, offset)
            m_exponent = integer_at(family.m_exponent, offset)
            if a_exponent >= m_exponent:
                continue
            gap = m_exponent - a_exponent
            if gap % 2:
                raise AssertionError("canonical family exponent gap must be even")
            endpoint_degree = a_exponent + m_exponent - 2 - 2 * content
            if endpoint_degree < 0:
                raise AssertionError("global content exceeds an adverse family")
            atomwise += Fraction(
                integer_at(family.coefficient, offset) * (gap // 2),
                2**endpoint_degree,
            )
    return CanonicalConsumerReport(
        length=length,
        content=content,
        term_count=len(data),
        adverse_count=len(adverse),
        reserve=data.get((0, 0), 0),
        discounted_adverse_at_half=discounted,
        uncancelled_adverse_at_half=uncancelled,
        atomwise_adverse_at_half=atomwise,
    )


def verify_canonical_consumer(length: int) -> bool:
    """Check the parity formulas and the sixfold endpoint reserve payment."""
    report = canonical_consumer_report(length)
    return (
        report.content == predicted_canonical_consumer_content(length)
        and report.reserve == predicted_canonical_consumer_reserve(length)
        and report.paid_with_sixfold_slack
        and report.uncancelled_paid_with_fourfold_slack
        and report.atomwise_paid_with_twofold_slack
    )


def predicted_payment_length(row: int, offset: int) -> int:
    """The all-row formula suggested by the exact scout."""
    if row < 1:
        raise ValueError("the diagonal scout starts at row one")
    if offset < 0:
        raise ValueError("offset must be nonnegative")
    return max(1, row - offset - 2)


def predicted_low_region_content(row: int) -> int:
    """Common ``(wh)`` content observed on the predicted low diagonal."""
    if row < 3:
        raise ValueError("the low-diagonal content formula begins at row three")
    return 4 * row**2 + 4 * row - 2


def predicted_low_region_reserve(row: int) -> int:
    """Closed-form constant reserve observed on the predicted low diagonal."""
    if row < 3:
        raise ValueError("the low-diagonal reserve formula begins at row three")
    return 4 * row**5 * (row + 1) ** 2 * (row + 2)


def even_low_diagonal_offset(row: int, length: int) -> int:
    """Starting offset of the adjacent even low-diagonal prefix.

    The odd predicted family has ``offset = row-length-2``.  Moving to the
    adjacent diagonal gives ``offset = row-length-3`` and exposes the parity
    case that the root cumulative consumer also needs.
    """
    if row < 4:
        raise ValueError("the even low-diagonal family begins at row four")
    if length < 1 or length > row - 3:
        raise ValueError("even low-diagonal length must satisfy 1 <= n <= row-3")
    return row - length - 3


def predicted_even_low_region_content(row: int) -> int:
    """Common content observed on the adjacent even low diagonal."""
    if row < 4:
        raise ValueError("the even low-diagonal content formula begins at row four")
    return 4 * row**2 - 4


def verify_even_low_region_prefix(row: int, length: int) -> bool:
    """Check the even-prefix content, zero reserve, and payment obstruction."""
    report = payment_report(row, even_low_diagonal_offset(row, length), length)
    return (
        report.content == predicted_even_low_region_content(row)
        and report.reserve == 0
        and not report.paid
    )


def verify_predicted_minimum(row: int, offset: int) -> bool:
    """Check payment at the predicted length and failure of every shorter one.

    Minimality refers only to this deliberately crude constant-reserve tactic;
    it is not a claim that the shorter cumulative is negative.
    """
    length = predicted_payment_length(row, offset)
    return payment_report(row, offset, length).paid and all(
        not payment_report(row, offset, shorter).paid for shorter in range(1, length)
    )


def verify_low_region_closed_forms(row: int, offset: int) -> bool:
    """Check the common-content and reserve formulas where ``r <= s-3``."""
    if row < 3 or offset < 0 or offset > row - 3:
        raise ValueError("closed forms require row >= 3 and 0 <= offset <= row-3")
    report = payment_report(row, offset, predicted_payment_length(row, offset))
    return (
        report.content == predicted_low_region_content(row)
        and report.reserve == predicted_low_region_reserve(row)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, nargs="+", default=list(range(1, 9)))
    parser.add_argument(
        "--max-offset",
        type=int,
        default=4,
        help="largest low-region offset checked in each requested row",
    )
    parser.add_argument(
        "--check-even-prefixes",
        action="store_true",
        help="also check every adjacent even low-diagonal prefix in each row",
    )
    parser.add_argument(
        "--check-canonical-consumer",
        type=int,
        metavar="MAX_LENGTH",
        help="check C(1,0,n) through this length at the true endpoint wH=1/2",
    )
    args = parser.parse_args()

    all_ok = True
    for row in args.rows:
        print(f"\n== Core-B diagonal cumulative: s={row} ==")
        for offset in range(args.max_offset + 1):
            length = predicted_payment_length(row, offset)
            report = payment_report(row, offset, length)
            minimal = verify_predicted_minimum(row, offset)
            closed_form = row >= 3 and offset <= row - 3
            formulas_ok = not closed_form or verify_low_region_closed_forms(row, offset)
            all_ok &= minimal
            all_ok &= formulas_ok
            print(
                f"  r={offset}: n={length}, content=(wh)^{report.content}, "
                f"terms={report.term_count}, adverse={report.adverse_count}, "
                f"reserve={report.reserve}, payment={'PASS' if report.paid else 'FAIL'}, "
                f"tested-minimal={'PASS' if minimal else 'FAIL'}, "
                f"closed-forms={'PASS' if formulas_ok else 'FAIL'}"
            )

        if args.check_even_prefixes and row >= 4:
            print("  adjacent even low-diagonal prefixes:")
            for length in range(1, row - 2):
                offset = even_low_diagonal_offset(row, length)
                report = payment_report(row, offset, length)
                even_ok = verify_even_low_region_prefix(row, length)
                all_ok &= even_ok
                print(
                    f"    n={length}, r={offset}, content=(wh)^{report.content}, "
                    f"reserve={report.reserve}, "
                    "constant-payment="
                    f"{'EXPECTED-FAIL' if not report.paid else 'UNEXPECTED-PASS'}, "
                    f"even-form={'PASS' if even_ok else 'FAIL'}"
                )

    if args.check_canonical_consumer is not None:
        if args.check_canonical_consumer < 1:
            raise ValueError("canonical consumer maximum length must be positive")
        print("\n== Canonical Core-B consumer C(1,0,n), endpoint wH=1/2 ==")
        for length in range(1, args.check_canonical_consumer + 1):
            report = canonical_consumer_report(length)
            formulas_ok = (
                report.content == predicted_canonical_consumer_content(length)
                and report.reserve == predicted_canonical_consumer_reserve(length)
            )
            consumer_ok = formulas_ok and report.paid_with_sixfold_slack
            all_ok &= consumer_ok
            ratio = report.discounted_adverse_at_half / report.reserve
            uncancelled_ratio = report.uncancelled_adverse_at_half / report.reserve
            atomwise_ratio = report.atomwise_adverse_at_half / report.reserve
            print(
                f"  n={length}: content=(wh)^{report.content}, "
                f"terms={report.term_count}, adverse={report.adverse_count}, "
                f"reserve={report.reserve}, adverse/reserve={float(ratio):.6f}, "
                f"uncancelled/reserve={float(uncancelled_ratio):.6f}, "
                f"atomwise/reserve={float(atomwise_ratio):.6f}, "
                f"parity-formulas={'PASS' if formulas_ok else 'FAIL'}, "
                f"wH-payment={'PASS' if report.paid_at_worst_endpoint else 'FAIL'}, "
                f"sixfold-slack={'PASS' if report.paid_with_sixfold_slack else 'FAIL'}, "
                f"uncancelled-fourfold="
                f"{'PASS' if report.uncancelled_paid_with_fourfold_slack else 'FAIL'}, "
                f"atomwise-twofold="
                f"{'PASS' if report.atomwise_paid_with_twofold_slack else 'FAIL'}"
            )

    print("\nDIAGONAL FORMULA SURVIVES" if all_ok else "\nDIAGONAL FORMULA REFUTED")


if __name__ == "__main__":
    main()
