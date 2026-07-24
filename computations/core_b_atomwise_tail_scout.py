#!/usr/bin/env python3
"""Exact atomwise-tail scout for the canonical Core-B cumulative.

The canonical consumer is ``C(1, 0, n)``.  Before collecting equal
monomials, an adverse determinant family with exponents ``a < m`` contributes

    coefficient * ((m - a) / 2) * 2^-(a + m - 2 - 2 * content(n))

at the worst endpoint ``wH = 1/2``.  This module groups that ledger by

* parity ``n = 2*k`` or ``n = 2*k+1``;
* residual distance from the parity centre; and
* the endpoint exponent gap ``g = a + m - 2 - 2*content(n)``.

The implementation has two complementary paths:

* a fast integer specialization of
  ``CoreBResidualAllRows_scout.families_for`` for falsification grids; and
* an exact symbolic finite classification through endpoint gap ``20``.

For the symbolic path write ``n = 2*k+parity`` and parameterize every window
index as ``p = k+u``.  A window term at shift ``t`` is then

    (k+u+1) * (k+parity+t-u+1)
    * x^[c4(k+u) + c4(k+parity+t-u)].

The eleven surviving ``A_i * M_j`` component pairs therefore have explicit
quadratic exponent gaps and degree-eight coefficient polynomials.  Solving
those quadratic inequalities through gap ``20`` leaves a finite list of
residual distances and ``u`` offsets, which :func:`exact_low_gap_groups`
sums directly.  No interpolation is used in that calculation.

What is checked mechanically here
----------------------------------

For every low gap through ``20``, the exact symbolic classifier:

1. uses the quadratic minimum-gap formulas to exclude every noncentral
   residual distance;
2. enumerates the resulting finite window-offset classes; and
3. expands and factors their coefficient masses identically in ``k``.

The older interpolation path remains as an independent check.  For every
requested low gap, it:

1. interpolates a candidate degree-eight polynomial ``P_g(k)`` from nine
   exact values;
2. validates ``M_g(k) = P_g(k)`` on a larger, still finite exact range;
3. checks the finite boundary prefix is no larger than ``P_g``; and
4. proves the *polynomial* inequality ``P_g(k) <= L_g * reserve(k)`` on the
   infinite stable range, because the shifted difference has nonnegative
   coefficients.

Item 4 is an exact symbolic certificate, while finite interpolation and
validation alone do not prove a counting identity.  The direct classifier
supplies that missing symbolic identity through gap ``20`` on its stated
stable range.  This remains exact Python/SymPy computational evidence, not a
Lean-kernel proof.

What is *not* proved here
-------------------------

Two formalization steps remain before this becomes a Lean all-index proof:

* formalize the finite low-gap classification in Lean; and
* prove a uniform all-gap tail estimate.  The very simple candidate

    M_g(k) <= g^3 * reserve(k)

passes every exact specialization exercised by this scout.  If established
for even ``g >= 22``, beyond the exact low-gap block, its complete geometric
tail is

    sum_{even g >= 22} g^3 / 2^g = 3311 / 884736.

Together with the exact symbolic low-gap envelopes this is far below ``1/2``
in both parities.  The script deliberately reports the complete result as
*conditional*: the finite symbolic computation is not yet formalized in
Lean, and a finite tail falsification grid is not an all-index tail proof.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from math import ceil
from typing import DefaultDict, Iterable

import sympy as sp


Term = tuple[int, int]  # (coefficient, exponent)
GapKey = tuple[int, int]  # (residual distance, endpoint gap)

k_symbol = sp.symbols("k", integer=True, positive=True)
x_symbol = sp.symbols("x", integer=True, nonnegative=True)


def c4(index: int) -> int:
    """The Casimir exponent ``index * (index + 2)``."""
    return index * (index + 2)


def collect_terms(terms: Iterable[Term]) -> list[Term]:
    """Collect integer terms with equal specialized exponents."""
    by_exponent: DefaultDict[int, int] = defaultdict(int)
    for coefficient, exponent in terms:
        by_exponent[exponent] += coefficient
    return [
        (coefficient, exponent)
        for exponent, coefficient in sorted(by_exponent.items())
        if coefficient
    ]


def multiply(left: Iterable[Term], right: Iterable[Term]) -> list[Term]:
    return collect_terms(
        (left_coefficient * right_coefficient, left_exponent + right_exponent)
        for left_coefficient, left_exponent in left
        for right_coefficient, right_exponent in right
    )


def window_terms(row: int, offset: int) -> list[Term]:
    """Specialized monomials of ``W_row(offset)``."""
    return collect_terms(
        (
            (index + 1) * (offset + row - index + 1),
            c4(index) + c4(offset + row - index),
        )
        for index in range(row + 1)
    )


def edge_terms(row: int, offset: int) -> list[Term]:
    return [
        (
            (row + 2) * (offset + 1),
            c4(row + 1) + c4(offset),
        )
    ]


def specialized_components(row: int, offset: int) -> tuple[list[list[Term]], list[list[Term]]]:
    """Return the four A-components and three M-components at integer offset."""
    w1, w2, w3 = (window_terms(row, offset + shift) for shift in (1, 2, 3))
    e0, e1, e2 = (edge_terms(row, offset + shift) for shift in (0, 1, 2))
    a_components = [
        multiply(w1, w3),
        multiply(w1, e2),
        multiply(e0, w3),
        multiply(e0, e2),
    ]
    m_components = [
        multiply(w2, w2),
        [(2 * coefficient, exponent) for coefficient, exponent in multiply(w2, e1)],
        multiply(e1, e1),
    ]
    return a_components, m_components


def canonical_content(length: int) -> int:
    """Common ``(wh)`` content of ``C(1,0,length)``."""
    if length < 1:
        raise ValueError("length must be positive")
    k, parity = divmod(length, 2)
    if parity == 0:
        return 4 * k**2 + 16 * k + 12
    return 4 * k**2 + 20 * k + 22


def canonical_reserve(length: int) -> int:
    """Constant reserve of the canonical quotient."""
    if length < 1:
        raise ValueError("length must be positive")
    if length == 1:
        return 11232
    k, parity = divmod(length, 2)
    if parity == 0:
        return 4 * (k + 1) * (k + 2) ** 6 * (k + 3)
    return (
        8
        * (k + 2) ** 2
        * (k + 3) ** 2
        * (2 * (k + 2) ** 3 * (k + 4) - (2 * k + 5))
    )


def symbolic_reserve(parity: int) -> sp.Expr:
    """Parity reserve as a polynomial in ``k``."""
    k = k_symbol
    if parity == 0:
        return sp.expand(4 * (k + 1) * (k + 2) ** 6 * (k + 3))
    if parity == 1:
        return sp.expand(
            8
            * (k + 2) ** 2
            * (k + 3) ** 2
            * (2 * (k + 2) ** 3 * (k + 4) - (2 * k + 5))
        )
    raise ValueError("parity must be zero or one")


@cache
def atomwise_groups(length: int) -> tuple[tuple[GapKey, int], ...]:
    """Aggregate adverse family mass by residual distance and endpoint gap."""
    if length < 1:
        raise ValueError("length must be positive")
    content = canonical_content(length)
    centre = length // 2
    grouped: DefaultDict[GapKey, int] = defaultdict(int)
    for step in range(length):
        row = step + 1
        offset = length - 1 - step
        a_components, m_components = specialized_components(row, offset)
        for a_component_index, a_component in enumerate(a_components):
            for m_component_index, m_component in enumerate(m_components):
                # This is exactly the pure window/window determinant removed
                # by CoreBStructuralRecurrence.
                if (a_component_index, m_component_index) == (0, 0):
                    continue
                for a_coefficient, a_exponent in a_component:
                    for m_coefficient, m_exponent in m_component:
                        if a_exponent >= m_exponent:
                            continue
                        exponent_gap = m_exponent - a_exponent
                        if exponent_gap % 2:
                            raise AssertionError("adverse exponent difference is not even")
                        endpoint_gap = (
                            a_exponent + m_exponent - 2 - 2 * content
                        )
                        if endpoint_gap < 0:
                            raise AssertionError("canonical content exceeds an adverse atom")
                        grouped[(row - centre, endpoint_gap)] += (
                            a_coefficient
                            * m_coefficient
                            * (exponent_gap // 2)
                        )
    return tuple(sorted(grouped.items()))


def gap_masses(length: int) -> dict[int, int]:
    """Aggregate the distance-refined ledger by endpoint gap alone."""
    result: DefaultDict[int, int] = defaultdict(int)
    for (_, gap), mass in atomwise_groups(length):
        result[gap] += mass
    return dict(result)


def atomwise_debt(length: int) -> Fraction:
    """Exact adverse family debt at ``wH=1/2``."""
    return sum(
        (Fraction(mass, 2**gap) for gap, mass in gap_masses(length).items()),
        Fraction(0),
    )


def predicted_content_shift(parity: int, centre: int, row: int) -> int:
    """Exact residual content shift above the canonical global content."""
    if row >= centre:
        return 0
    distance = centre - row
    if parity == 0:
        return 4 * distance**2
    return 4 * distance * (distance + 1)


def predicted_minimum_gap(parity: int, distance: int) -> int:
    """Observed exact minimum endpoint gap at a residual distance.

    Here ``distance = row-centre``.  These formulas are independently checked
    against the atom ledger by :func:`verify_distance_formulas`.
    """
    if parity == 0:
        if distance < 0:
            d = -distance
            return 8 * d**2 + 4 * d + 2
        if distance <= 1:
            return 4
        return 2 * distance**2
    if distance < 0:
        d = -distance
        return 8 * d**2 + 12 * d + 4
    if distance == 0:
        return 4
    if distance == 1:
        return 2
    return 2 * distance**2 - 2 * distance - 2


_LOW_GAP_WINDOW_BOUNDS_AT_20: dict[int, dict[int, tuple[int, int]]] = {
    # parity -> distance -> inclusive window-offset bounds for p = k + u.
    0: {
        -1: (-1, -1),
        0: (-2, 0),
        1: (-2, 1),
        2: (-1, 2),
        3: (0, 2),
    },
    1: {
        0: (-1, 0),
        1: (-1, 1),
        2: (-1, 2),
        3: (-1, 3),
    },
}


def exact_low_gap_stable_start(parity: int) -> int:
    """First ``k`` for which every gap-at-most-20 distance exists.

    Even length needs ``k >= 3`` because its rightmost low-gap residual is
    ``row = k+3 <= 2*k``.  Odd length needs only ``k >= 2``.
    """
    if parity == 0:
        return 3
    if parity == 1:
        return 2
    raise ValueError("parity must be zero or one")


def exact_low_gap_distances(parity: int, maximum_gap: int = 20) -> tuple[int, ...]:
    """Residual distances which can contribute through endpoint gap ``20``.

    This function intentionally supports only the fully classified cutoff.
    Completeness follows from the exact quadratic minimum-gap formulas:

    * even: the first excluded distances ``-2`` and ``4`` have minima
      ``42`` and ``32``;
    * odd: the first excluded distances ``-1`` and ``4`` have minima
      ``24`` and ``22``.

    The formulas are increasing farther into either tail.
    """
    if maximum_gap != 20:
        raise ValueError("the exact finite classification is currently for gap 20")
    if parity not in (0, 1):
        raise ValueError("parity must be zero or one")
    distances = tuple(_LOW_GAP_WINDOW_BOUNDS_AT_20[parity])
    if parity == 0:
        assert predicted_minimum_gap(parity, -2) > maximum_gap
        assert predicted_minimum_gap(parity, 4) > maximum_gap
        assert distances == (-1, 0, 1, 2, 3)
    else:
        assert predicted_minimum_gap(parity, -1) > maximum_gap
        assert predicted_minimum_gap(parity, 4) > maximum_gap
        assert distances == (0, 1, 2, 3)
    return distances


def _collect_symbolic_terms(
    terms: Iterable[tuple[sp.Expr, sp.Expr]],
) -> list[tuple[sp.Expr, sp.Expr]]:
    """Collect a finite symbolic monomial list by its exact exponent."""
    by_exponent: DefaultDict[sp.Expr, sp.Expr] = defaultdict(lambda: sp.Integer(0))
    for coefficient, exponent in terms:
        by_exponent[sp.expand(exponent)] += sp.expand(coefficient)
    return [
        (sp.factor(coefficient), exponent)
        for exponent, coefficient in sorted(
            by_exponent.items(), key=lambda item: sp.default_sort_key(item[0])
        )
        if coefficient != 0
    ]


def _multiply_symbolic_terms(
    left: Iterable[tuple[sp.Expr, sp.Expr]],
    right: Iterable[tuple[sp.Expr, sp.Expr]],
    scale: int = 1,
) -> list[tuple[sp.Expr, sp.Expr]]:
    return _collect_symbolic_terms(
        (
            sp.expand(scale * left_coefficient * right_coefficient),
            sp.expand(left_exponent + right_exponent),
        )
        for left_coefficient, left_exponent in left
        for right_coefficient, right_exponent in right
    )


@cache
def exact_low_gap_groups(
    parity: int, maximum_gap: int = 20
) -> tuple[tuple[GapKey, sp.Expr], ...]:
    """Direct symbolic family classification through endpoint gap ``20``.

    The result is grouped by ``(distance, gap)`` and is an identity in
    :data:`k_symbol` on the stable range returned by
    :func:`exact_low_gap_stable_start`.  The finite ``u`` bounds below are the
    integer solutions of the eleven component-pair quadratic inequalities
    ``endpoint_gap <= 20``.  Since each omitted branch is past the vertex of
    its positive quadratic, the next omitted integer already exceeds the
    cutoff and all farther integers do as well.

    This is exact SymPy algebra, not a Lean-kernel proof.
    """
    distances = exact_low_gap_distances(parity, maximum_gap)
    k = k_symbol
    length = 2 * k + parity
    content = (
        4 * k**2 + 16 * k + 12
        if parity == 0
        else 4 * k**2 + 20 * k + 22
    )
    grouped: DefaultDict[GapKey, sp.Expr] = defaultdict(lambda: sp.Integer(0))

    for distance in distances:
        lower_u, upper_u = _LOW_GAP_WINDOW_BOUNDS_AT_20[parity][distance]
        if upper_u > distance:
            raise AssertionError("window index exceeds its residual row")

        def window(shift: int) -> list[tuple[sp.Expr, sp.Expr]]:
            terms = []
            for u in range(lower_u, upper_u + 1):
                left_index = k + u
                right_index = length + shift - left_index
                terms.append(
                    (
                        sp.expand((left_index + 1) * (right_index + 1)),
                        sp.expand(
                            left_index * (left_index + 2)
                            + right_index * (right_index + 2)
                        ),
                    )
                )
            return _collect_symbolic_terms(terms)

        def edge(shift: int) -> list[tuple[sp.Expr, sp.Expr]]:
            row = k + distance
            offset = length - row
            return [
                (
                    sp.expand((row + 2) * (offset + shift + 1)),
                    sp.expand(
                        (row + 1) * (row + 3)
                        + (offset + shift) * (offset + shift + 2)
                    ),
                )
            ]

        w1, w2, w3 = (window(shift) for shift in (1, 2, 3))
        e0, e1, e2 = (edge(shift) for shift in (0, 1, 2))
        a_components = [
            _multiply_symbolic_terms(w1, w3),
            _multiply_symbolic_terms(w1, e2),
            _multiply_symbolic_terms(e0, w3),
            _multiply_symbolic_terms(e0, e2),
        ]
        m_components = [
            _multiply_symbolic_terms(w2, w2),
            _multiply_symbolic_terms(w2, e1, 2),
            _multiply_symbolic_terms(e1, e1),
        ]

        for a_component_index, a_component in enumerate(a_components):
            for m_component_index, m_component in enumerate(m_components):
                if (a_component_index, m_component_index) == (0, 0):
                    continue
                for a_coefficient, a_exponent in a_component:
                    for m_coefficient, m_exponent in m_component:
                        exponent_difference = sp.expand(a_exponent - m_exponent)
                        endpoint_gap = sp.expand(
                            a_exponent + m_exponent - 2 - 2 * content
                        )
                        if exponent_difference.has(k) or endpoint_gap.has(k):
                            raise AssertionError(
                                "central family exponent data must be k-independent"
                            )
                        difference = int(exponent_difference)
                        gap = int(endpoint_gap)
                        if difference >= 0 or gap > maximum_gap:
                            continue
                        if difference % 2:
                            raise AssertionError("family exponent difference is not even")
                        grouped[(distance, gap)] += sp.expand(
                            a_coefficient
                            * m_coefficient
                            * (-difference // 2)
                        )

    return tuple(
        (key, sp.factor(value))
        for key, value in sorted(grouped.items())
        if value != 0
    )


def exact_low_gap_masses(
    parity: int, maximum_gap: int = 20
) -> dict[int, sp.Expr]:
    """Aggregate the exact symbolic distance ledger by endpoint gap."""
    result: DefaultDict[int, sp.Expr] = defaultdict(lambda: sp.Integer(0))
    for (_, gap), mass in exact_low_gap_groups(parity, maximum_gap):
        result[gap] += mass
    return {gap: sp.factor(mass) for gap, mass in sorted(result.items())}


def verify_exact_low_gap_classification(max_k: int = 8) -> bool:
    """Compare the symbolic classification with exact specialized ledgers.

    The comparison is a regression test, not the reason the identities hold:
    :func:`exact_low_gap_groups` constructs them by direct symbolic summation.
    Boundary values before the stable range are required only to be
    overestimated by the stable polynomial.
    """
    for parity in (0, 1):
        symbolic = exact_low_gap_masses(parity)
        stable_start = exact_low_gap_stable_start(parity)
        for k in range(1, max_k + 1):
            actual = gap_masses(2 * k + parity)
            for gap in range(2, 21, 2):
                predicted = int(
                    symbolic.get(gap, sp.Integer(0)).subs(k_symbol, k)
                )
                observed = actual.get(gap, 0)
                if k < stable_start:
                    if predicted < observed:
                        return False
                elif predicted != observed:
                    return False
    return True


def verify_distance_formulas(max_k: int = 20) -> bool:
    """Check the exact quadratic minimum-gap formulas on a finite range."""
    for parity in (0, 1):
        for k in range(1, max_k + 1):
            length = 2 * k + parity
            by_distance: DefaultDict[int, list[int]] = defaultdict(list)
            for (distance, gap), _ in atomwise_groups(length):
                by_distance[distance].append(gap)
            for distance, gaps in by_distance.items():
                if min(gaps) != predicted_minimum_gap(parity, distance):
                    return False
    return True


@dataclass(frozen=True)
class GapPolynomialCertificate:
    parity: int
    gap: int
    stable_start: int
    polynomial: sp.Expr
    symbolic_identity_exact: bool
    envelope: int
    shifted_difference_coefficients: tuple[int, ...]
    prefix_overestimate: bool
    validation_exact: bool

    @property
    def candidate_polynomial_envelope_proved(self) -> bool:
        """Exact coefficientwise nonnegativity certificate for ``polynomial``."""
        return all(coefficient >= 0 for coefficient in self.shifted_difference_coefficients)


def interpolate_gap_polynomial(
    parity: int,
    gap: int,
    *,
    stable_start: int = 4,
    validation_stop: int = 24,
) -> GapPolynomialCertificate:
    """Construct and analyze one stable degree-eight gap mass.

    Through gap ``20`` the polynomial comes from the direct exact symbolic
    classifier.  Above that cutoff, nine consecutive values determine an
    interpolation candidate.  Exact validation is performed on a finite
    range in either case.  The prefix is allowed to be boundary-special, but
    the stable polynomial must overestimate it.
    """
    if stable_start < 1:
        raise ValueError("stable_start must be positive")
    if gap < 0 or gap % 2:
        raise ValueError("gap must be a nonnegative even integer")
    exact = exact_low_gap_masses(parity)
    symbolic_identity_exact = gap <= 20 and gap in exact
    if symbolic_identity_exact:
        polynomial = exact[gap]
    else:
        samples = []
        for k in range(stable_start, stable_start + 9):
            samples.append((k, gap_masses(2 * k + parity).get(gap, 0)))
        polynomial = sp.factor(sp.interpolate(samples, k_symbol))
    if sp.Poly(polynomial, k_symbol).degree() > 8:
        raise AssertionError("gap mass polynomial has degree greater than eight")

    validation_exact = all(
        int(polynomial.subs(k_symbol, k))
        == gap_masses(2 * k + parity).get(gap, 0)
        for k in range(stable_start, validation_stop + 1)
    )
    prefix_overestimate = all(
        int(polynomial.subs(k_symbol, k))
        >= gap_masses(2 * k + parity).get(gap, 0)
        for k in range(1, stable_start)
    )

    reserve = symbolic_reserve(parity)
    leading_ratio = Fraction(
        int(sp.Poly(polynomial, k_symbol).LC()),
        int(sp.Poly(reserve, k_symbol).LC()),
    )
    envelope = ceil(leading_ratio)
    shifted = sp.Poly(
        sp.expand(
            (envelope * reserve - polynomial).subs(
                k_symbol, x_symbol + stable_start
            )
        ),
        x_symbol,
    )
    coefficients = tuple(
        int(shifted.coeff_monomial(x_symbol**degree))
        for degree in range(shifted.degree() + 1)
    )
    return GapPolynomialCertificate(
        parity=parity,
        gap=gap,
        stable_start=stable_start,
        polynomial=polynomial,
        symbolic_identity_exact=symbolic_identity_exact,
        envelope=envelope,
        shifted_difference_coefficients=coefficients,
        prefix_overestimate=prefix_overestimate,
        validation_exact=validation_exact,
    )


def low_gap_certificates(
    parity: int,
    maximum_gap: int = 20,
    *,
    stable_start: int = 4,
    validation_stop: int = 24,
) -> list[GapPolynomialCertificate]:
    """Build certificates for every nonzero even gap through ``maximum_gap``."""
    result = []
    for gap in range(2, maximum_gap + 1, 2):
        if any(
            gap_masses(2 * k + parity).get(gap, 0)
            for k in range(stable_start, stable_start + 9)
        ):
            result.append(
                interpolate_gap_polynomial(
                    parity,
                    gap,
                    stable_start=stable_start,
                    validation_stop=validation_stop,
                )
            )
    return result


def envelope_sum(certificates: Iterable[GapPolynomialCertificate]) -> Fraction:
    return sum(
        (Fraction(certificate.envelope, 2**certificate.gap) for certificate in certificates),
        Fraction(0),
    )


def cubic_even_tail(first_gap: int = 20) -> Fraction:
    """Exact ``sum g^3/2^g`` over even gaps from ``first_gap`` onward."""
    if first_gap < 0 or first_gap % 2:
        raise ValueError("first_gap must be a nonnegative even integer")
    first_index = first_gap // 2
    # For z=1/4, sum_{m>=a} m^3 z^m is evaluated exactly by SymPy.
    m = sp.symbols("m", integer=True, nonnegative=True)
    value = sp.summation(8 * m**3 / 4**m, (m, first_index, sp.oo))
    return Fraction(int(sp.numer(value)), int(sp.denom(value)))


@dataclass(frozen=True)
class EmpiricalTailReport:
    parity: int
    max_k: int
    first_gap: int
    worst_ratio_to_cubic_envelope: Fraction
    worst_location: tuple[int, int]

    @property
    def cubic_envelope_passes_checked_range(self) -> bool:
        return self.worst_ratio_to_cubic_envelope <= 1


def empirical_cubic_tail_report(
    parity: int, max_k: int = 40, first_gap: int = 20
) -> EmpiricalTailReport:
    """Falsify, but do not prove, ``M_g <= g^3 R`` on an exact grid."""
    worst = Fraction(0)
    worst_location = (1, first_gap)
    for k in range(1, max_k + 1):
        reserve = canonical_reserve(2 * k + parity)
        for gap, mass in gap_masses(2 * k + parity).items():
            if gap < first_gap:
                continue
            ratio = Fraction(mass, gap**3 * reserve)
            if ratio > worst:
                worst = ratio
                worst_location = (k, gap)
    return EmpiricalTailReport(
        parity=parity,
        max_k=max_k,
        first_gap=first_gap,
        worst_ratio_to_cubic_envelope=worst,
        worst_location=worst_location,
    )


def print_report(max_k: int, maximum_gap: int) -> None:
    print(f"distance formulas through k={max_k}: {verify_distance_formulas(max_k)}")
    for parity, name in ((0, "even"), (1, "odd")):
        certificates = low_gap_certificates(
            parity,
            maximum_gap,
            stable_start=4,
            validation_stop=max(24, max_k),
        )
        print(f"\n{name} n=2k+{parity}")
        for certificate in certificates:
            status = (
                certificate.validation_exact
                and certificate.prefix_overestimate
                and certificate.candidate_polynomial_envelope_proved
            )
            source = (
                "EXACT-SYMBOLIC"
                if certificate.symbolic_identity_exact
                else "INTERPOLATED"
            )
            print(
                f"  g={certificate.gap:2d} L={certificate.envelope:3d} "
                f"{source} CHECK={status}: P_g(k) = {certificate.polynomial}"
            )
        low = envelope_sum(certificates)
        tail = cubic_even_tail(maximum_gap + 2)
        empirical = empirical_cubic_tail_report(
            parity, max_k=max_k, first_gap=maximum_gap + 2
        )
        print(
            "  low-gap polynomial envelope "
            "(exact-symbolic through g=20): "
            f"{low} = {float(low):.9f} R"
        )
        print(
            "  conditional cubic tail: "
            f"{tail} = {float(tail):.9f} R"
        )
        print(
            "  conditional total: "
            f"{low + tail} = {float(low + tail):.9f} R "
            f"(< 1/2: {low + tail < Fraction(1, 2)})"
        )
        print(
            "  exact cubic-tail falsification grid: "
            f"k<= {empirical.max_k}, worst={float(empirical.worst_ratio_to_cubic_envelope):.6f} "
            f"at (k,g)={empirical.worst_location}, "
            f"PASS={empirical.cubic_envelope_passes_checked_range}"
        )
    print(
        "\nREMAINING FORMALIZATION: (1) translate the exact finite low-gap "
        "classification into Lean; (2) prove M_g(k)<=g^3*R(k) on the "
        "undisplayed tail. Without the tail lemma this is not an all-k proof."
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=20)
    parser.add_argument("--maximum-gap", type=int, default=18)
    args = parser.parse_args()
    if args.max_k < 4:
        parser.error("--max-k must be at least 4")
    if args.maximum_gap < 2 or args.maximum_gap % 2:
        parser.error("--maximum-gap must be a positive even integer")
    print_report(args.max_k, args.maximum_gap)


if __name__ == "__main__":
    main()
