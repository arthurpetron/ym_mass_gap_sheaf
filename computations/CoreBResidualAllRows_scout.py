#!/usr/bin/env python3
"""Exact scout for an all-row Core-B boundary-residual proof.

This generalizes the row-one scouts to fixed rows ``s = 1, 2, ...`` while
keeping the offset ``r`` symbolic.  It is a faithful sparse-monomial replica
of ``CoreBStructuralRecurrence``:

  W_s(k) = acN x (s+1) (s+k),
  E_s(k) = coeffW x (s+1) * coeffW x k,
  R(s,r) = sum_(i,j)!=(0,0) det(A_i(w), A_i(h), M_j(w), M_j(h)).

For each requested row the scout checks, with exact integer/rational
arithmetic:

* the collected elementary-family count and index scheme;
* evenness of every exponent delta (individual divisibility by w^2-h^2);
* the first offset at which every family has a fixed sign;
* the pure-boundary anchor, coordinatewise domination of every eventual
  adverse quotient chain, and the exact discounted payment inequality;
* the two-step cumulative recurrence schema; and
* sufficient reserve-vs-adverse-mass payments for the finite prefix.

This is a design/falsification scout, not a proof.  Its output is intended to
decide whether the Lean proof should be symbolic in both ``s`` and ``r``.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import cached_property
from typing import Dict, Iterable, List, Tuple

import sympy as sp


r = sp.symbols("r", integer=True, nonnegative=True)
w, h = sp.symbols("w h", nonnegative=True)


@dataclass(frozen=True)
class Term:
    coefficient: sp.Expr
    exponent: sp.Expr


@dataclass(frozen=True)
class Family:
    i: int
    j: int
    a_index: int
    m_index: int
    coefficient: sp.Expr
    a_exponent: sp.Expr
    m_exponent: sp.Expr

    @cached_property
    def delta(self) -> sp.Expr:
        return sp.expand(self.a_exponent - self.m_exponent)


def c4(p: sp.Expr) -> sp.Expr:
    return sp.expand(p * (p + 2))


def collect_terms(terms: Iterable[Term]) -> List[Term]:
    by_exponent: Dict[sp.Expr, sp.Expr] = defaultdict(lambda: sp.Integer(0))
    for term in terms:
        by_exponent[sp.expand(term.exponent)] += sp.expand(term.coefficient)
    return [
        Term(sp.factor(coefficient), exponent)
        for exponent, coefficient in sorted(
            by_exponent.items(), key=lambda item: sp.default_sort_key(item[0])
        )
        if coefficient != 0
    ]


def multiply(left: Iterable[Term], right: Iterable[Term]) -> List[Term]:
    return collect_terms(
        Term(sp.expand(a.coefficient * b.coefficient), sp.expand(a.exponent + b.exponent))
        for a in left
        for b in right
    )


def scale(c: int, terms: Iterable[Term]) -> List[Term]:
    return [Term(sp.expand(c * term.coefficient), term.exponent) for term in terms]


def window_terms(s: int, offset: int) -> List[Term]:
    """Monomials of W_s(r+offset), valid for every natural r."""
    terms = []
    for p in range(s + 1):
        q = r + s + offset - p
        # q >= r + offset >= 0 for every offset used below.
        coefficient = (p + 1) * (q + 1)
        terms.append(Term(sp.expand(coefficient), sp.expand(c4(p) + c4(q))))
    return collect_terms(terms)


def boundary_terms(s: int, offset: int) -> List[Term]:
    return [
        Term(
            sp.expand((s + 2) * (r + offset + 1)),
            sp.expand(c4(s + 1) + c4(r + offset)),
        )
    ]


def components(s: int) -> Tuple[List[List[Term]], List[List[Term]]]:
    w1, w2, w3 = (window_terms(s, offset) for offset in (1, 2, 3))
    e0, e1, e2 = (boundary_terms(s, offset) for offset in (0, 1, 2))
    a_terms = [
        multiply(w1, w3),
        multiply(w1, e2),
        multiply(e0, w3),
        multiply(e0, e2),
    ]
    m_terms = [
        multiply(w2, w2),
        scale(2, multiply(w2, e1)),
        multiply(e1, e1),
    ]
    return a_terms, m_terms


def families_for(s: int) -> Tuple[List[Family], List[int], List[int]]:
    a_terms, m_terms = components(s)
    families = []
    for i, a_component in enumerate(a_terms):
        for j, m_component in enumerate(m_terms):
            if (i, j) == (0, 0):
                continue
            for ai, a_term in enumerate(a_component):
                for mi, m_term in enumerate(m_component):
                    families.append(
                        Family(
                            i,
                            j,
                            ai,
                            mi,
                            sp.factor(a_term.coefficient * m_term.coefficient),
                            a_term.exponent,
                            m_term.exponent,
                        )
                    )
    return families, [len(x) for x in a_terms], [len(x) for x in m_terms]


def eventual_sign_and_threshold(expr: sp.Expr) -> Tuple[int, int]:
    """Return (eventual sign, first r with that strict sign forever)."""
    poly = sp.Poly(sp.expand(expr), r)
    if poly.is_zero:
        return 0, 0
    if poly.degree() > 1:
        raise AssertionError(f"expected affine exponent delta, got {expr}")
    leading = int(poly.LC())
    eventual_sign = 1 if leading > 0 else -1
    threshold = 0
    while True:
        value = int(expr.subs(r, threshold))
        if value * eventual_sign > 0:
            # An affine function cannot cross back after it has the leading sign.
            return eventual_sign, threshold
        threshold += 1


def nonnegative_from(expr: sp.Expr, threshold: int) -> bool:
    """Decide an affine expression is >= 0 on every integer r >= threshold."""
    poly = sp.Poly(sp.expand(expr), r)
    if poly.degree() > 1:
        raise AssertionError(f"expected affine margin, got {expr}")
    slope = int(poly.coeff_monomial(r))
    return slope >= 0 and int(expr.subs(r, threshold)) >= 0


def integer_at(expr: sp.Expr, value: int) -> int:
    result = sp.expand(expr).subs(r, value)
    if not result.is_Integer:
        raise AssertionError(f"noninteger specialization {expr} at r={value}: {result}")
    return int(result)


def discounted_sum(
    adverse: Iterable[Family], anchor_m: sp.Expr, anchor_total: sp.Expr, value: int
) -> Fraction:
    total = Fraction(0)
    for family in adverse:
        delta = -integer_at(family.delta, value)
        assert delta > 0 and delta % 2 == 0
        chain_length = delta // 2
        quotient_total = integer_at(family.a_exponent + family.m_exponent - 2, value)
        gap = quotient_total - integer_at(anchor_total, value)
        low = integer_at(family.a_exponent, value)
        assert low >= integer_at(anchor_m, value)
        assert gap >= 0
        total += Fraction(integer_at(family.coefficient, value) * chain_length, 4**gap)
    return total


def specialized_quotient(families: Iterable[Family], value: int) -> Tuple[int, sp.Poly]:
    """Return the content exponent and sparse quotient by w^2-h^2."""
    raw: Dict[Tuple[int, int], int] = defaultdict(int)
    for family in families:
        coefficient = integer_at(family.coefficient, value)
        ea = integer_at(family.a_exponent, value)
        em = integer_at(family.m_exponent, value)
        raw[(ea, em)] += coefficient
        raw[(em, ea)] -= coefficient
    raw = {monomial: coefficient for monomial, coefficient in raw.items() if coefficient}
    content = min(min(a, b) for a, b in raw)
    shifted = {(a - content, b - content): c for (a, b), c in raw.items()}
    numerator = sp.Poly.from_dict(shifted, (w, h), domain=sp.ZZ)
    quotient, remainder = sp.div(numerator, sp.Poly(w**2 - h**2, w, h, domain=sp.ZZ))
    if not remainder.is_zero:
        raise AssertionError(f"R(s,r={value}) is not divisible by w^2-h^2")
    return content, quotient


def simplex_sweep(quotient: sp.Poly) -> Tuple[int, int]:
    """Exact-rational sign sweep of a quotient on 0 < h <= w <= 1/4."""
    data = {(a, b): int(c) for (a, b), c in quotient.as_dict().items()}
    widths = [Fraction(1, 4), Fraction(1, 5), Fraction(1, 8), Fraction(1, 16)]
    tested = negatives = 0
    for width in widths:
        for numerator in range(1, 17):
            height = width * Fraction(numerator, 16)
            value = sum(coefficient * width**a * height**b for (a, b), coefficient in data.items())
            tested += 1
            negatives += value < 0
    return tested, negatives


def residual_value(s: int, offset: int, width: Fraction, height: Fraction) -> Fraction:
    """Direct exact value of R(s,offset), without symbolic expansion."""

    def coefficient(x: Fraction, p: int) -> Fraction:
        return Fraction(p + 1) * x ** (p * (p + 2))

    def window(x: Fraction, k: int) -> Fraction:
        return sum(
            (coefficient(x, p) * coefficient(x, s + k - p) for p in range(s + 1)),
            Fraction(0),
        )

    def edge(x: Fraction, k: int) -> Fraction:
        return coefficient(x, s + 1) * coefficient(x, k)

    def a_components(x: Fraction) -> List[Fraction]:
        return [
            window(x, offset + 1) * window(x, offset + 3),
            window(x, offset + 1) * edge(x, offset + 2),
            edge(x, offset) * window(x, offset + 3),
            edge(x, offset) * edge(x, offset + 2),
        ]

    def m_components(x: Fraction) -> List[Fraction]:
        return [
            window(x, offset + 2) ** 2,
            2 * window(x, offset + 2) * edge(x, offset + 1),
            edge(x, offset + 1) ** 2,
        ]

    aw, ah = a_components(width), a_components(height)
    mw, mh = m_components(width), m_components(height)
    return sum(
        (aw[i] * mh[j] - mw[j] * ah[i] for i in range(4) for j in range(3) if (i, j) != (0, 0)),
        Fraction(0),
    )


def prefix_sign_sweep(s: int, threshold: int) -> bool:
    widths = [Fraction(1, 4), Fraction(1, 5), Fraction(1, 8)]
    height_ratios = [Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(15, 16), Fraction(1)]
    tested = negatives = 0
    for offset in range(threshold):
        for width in widths:
            for ratio in height_ratios:
                value = residual_value(s, offset, width, width * ratio)
                tested += 1
                negatives += value < 0
    print(f"      exact finite-region falsification sweep: {tested} points, negatives={negatives}")
    return negatives == 0


def finite_prefix_report(s: int, families: List[Family], threshold: int) -> bool:
    all_paid = True
    if threshold == 0:
        print("  (f) finite prefix: empty")
        return True
    print(f"  (f) finite prefix r=0..{threshold - 1}:")
    for value in range(threshold):
        content, quotient = specialized_quotient(families, value)
        data = quotient.as_dict()
        reserve = int(data.get((0, 0), 0))
        adverse = [
            (monomial, -int(coefficient))
            for monomial, coefficient in data.items()
            if coefficient < 0
        ]
        adverse_mass = sum(coefficient for _, coefficient in adverse)
        if adverse:
            min_w = min(monomial[0] for monomial, _ in adverse)
            min_h = min(monomial[1] for monomial, _ in adverse)
            min_total = min(sum(monomial) for monomial, _ in adverse)
            discounted = sum(
                Fraction(coefficient, 4 ** sum(monomial)) for monomial, coefficient in adverse
            )
            symmetric_depth = None
            for depth in range(0, min(min_w, min_h) + 1):
                if Fraction(adverse_mass, 4 ** (2 * depth)) <= reserve:
                    symmetric_depth = depth
                    break
        else:
            min_w = min_h = min_total = 0
            discounted = Fraction(0)
            symmetric_depth = 0
        # This tests only the simplest tactic: discard every positive
        # nonconstant monomial and pay all adverse terms from the constant
        # reserve.  Failure is a tactic obstruction, not a sign refutation.
        paid = reserve >= 0 and discounted <= reserve
        all_paid &= paid
        depth_text = "none" if symmetric_depth is None else f"(wh)^{symmetric_depth}"
        print(
            f"      r={value}: content=(wh)^{content}, quotient_terms={len(data)}, "
            f"negative={len(adverse)}, reserve={reserve}, adverse_mass={adverse_mass}, "
            f"min_exp=({min_w},{min_h}), min_total={min_total}, "
            f"uniform_payment={depth_text}, "
            f"constant_reserve_discount={'PASS' if paid else 'NEEDS_GROUPING'}"
        )
        if not paid:
            tested, negatives = simplex_sweep(quotient)
            print(
                f"          exact simplex sweep: {tested} points, negatives={negatives} "
                "(falsification only)"
            )
    return all_paid


def scout_row(
    s: int, max_r: int, show_groups: bool, skip_prefix: bool, sweep_prefix: bool
) -> Tuple[bool, bool]:
    print(f"\n== Core-B all-row scout: s={s} ==")
    families, a_lengths, m_lengths = families_for(s)
    expected = sum(
        a_lengths[i] * m_lengths[j] for i in range(4) for j in range(3) if (i, j) != (0, 0)
    )
    expected_a_lengths = [((s + 2) * (s + 3)) // 2 - 2, s + 1, s + 1, 1]
    expected_m_lengths = [((s + 1) * (s + 2)) // 2, s + 1, 1]
    expected_family_count = ((s + 1) * (s + 2) * (3 * s + 11)) // 2
    print(
        f"  (a) collected terms A={a_lengths}, M={m_lengths}; "
        f"families={len(families)} (index (i,j,a_term,m_term), expected={expected})"
    )
    family_count_ok = (
        len(families) == expected == expected_family_count
        and a_lengths == expected_a_lengths
        and m_lengths == expected_m_lengths
    )
    print(
        "      all-s count formulas: "
        f"A0=(s+2)(s+3)/2-2, M0=(s+1)(s+2)/2, "
        f"F=(s+1)(s+2)(3s+11)/2 ({'PASS' if family_count_ok else 'FAIL'})"
    )

    parity_bad = []
    for family in families:
        coefficients = sp.Poly(family.delta, r).all_coeffs()
        if any(int(coefficient) % 2 for coefficient in coefficients):
            parity_bad.append(family)
    parity_ok = not parity_bad
    print(
        f"  (b) even exponent delta for every elementary family: {'PASS' if parity_ok else 'FAIL'}"
    )

    signed = [(family, *eventual_sign_and_threshold(family.delta)) for family in families]
    threshold = max(start for _, _, start in signed)
    expected_threshold = ((s + 2) ** 2) // 2
    counts = {
        sign: sum(1 for _, family_sign, _ in signed if family_sign == sign) for sign in (1, -1, 0)
    }
    sign_ok = threshold == expected_threshold and all(
        eventual_sign_and_threshold(family.delta)[0] == sign
        and (sign == 0 or int(family.delta.subs(r, threshold)) * sign > 0)
        for family, sign, _ in signed
    )
    print(
        f"  (c) eventual signs stabilize at r0={threshold}: "
        f"favorable={counts[1]}, adverse={counts[-1]}, zero={counts[0]} "
        f"(formula floor((s+2)^2/2) {'PASS' if sign_ok else 'FAIL'})"
    )

    anchor_candidates = [family for family in families if family.i == 3 and family.j == 2]
    if len(anchor_candidates) != 1:
        raise AssertionError(f"expected one pure-boundary anchor, got {len(anchor_candidates)}")
    anchor = anchor_candidates[0]
    anchor_delta = sp.expand(anchor.delta)
    if anchor_delta != 2:
        raise AssertionError(f"pure-boundary delta is not 2: {anchor_delta}")
    anchor_m = sp.expand(anchor.m_exponent)
    anchor_total = sp.expand(2 * anchor_m)
    anchor_c = sp.factor(anchor.coefficient)
    expected_anchor_c = sp.expand((s + 2) ** 4 * (r + 1) * (r + 2) ** 2 * (r + 3))
    expected_anchor_m = sp.expand(2 * r**2 + 8 * r + 2 * s**2 + 8 * s + 12)
    anchor_formula_ok = (
        sp.expand(anchor_c - expected_anchor_c) == 0
        and sp.expand(anchor_m - expected_anchor_m) == 0
    )
    adverse = [family for family, sign, _ in signed if sign < 0]
    domination_bad = []
    gap_groups: Dict[sp.Expr, sp.Expr] = defaultdict(lambda: sp.Integer(0))
    gap_counts: Dict[sp.Expr, int] = defaultdict(int)
    for family in adverse:
        low_margin = sp.expand(family.a_exponent - anchor_m)
        quotient_total = sp.expand(family.a_exponent + family.m_exponent - 2)
        gap = sp.expand(quotient_total - anchor_total)
        if not nonnegative_from(low_margin, threshold) or not nonnegative_from(gap, threshold):
            domination_bad.append((family, low_margin, gap))
        chain_length = sp.expand(-family.delta / 2)
        gap_groups[gap] += sp.expand(family.coefficient * chain_length)
        gap_counts[gap] += 1

    exact_ok = True
    crude_ok = True
    ratios = []
    minimum_gap_keys: set[sp.Expr] = set()
    for value in range(threshold, max_r + 1):
        lhs = discounted_sum(adverse, anchor_m, anchor_total, value)
        rhs = Fraction(integer_at(anchor_c, value))
        exact_ok &= lhs <= rhs
        gaps_at_value = [(integer_at(gap, value), gap) for gap in gap_groups]
        min_gap_value = min(gap for gap, _ in gaps_at_value) if gaps_at_value else 0
        minimum_gap_keys.update(key for gap, key in gaps_at_value if gap == min_gap_value)
        total_mass = sum(
            integer_at(family.coefficient, value) * (-integer_at(family.delta, value) // 2)
            for family in adverse
        )
        crude_ok &= Fraction(total_mass, 4**min_gap_value) <= rhs
        if value < threshold + 6:
            ratios.append(float(lhs / rhs) if rhs else float("inf"))

    domination_ok = not domination_bad
    expected_min_gap = sp.expand(2 * r - 2 * (s - 1))
    min_gap_formula_ok = expected_min_gap in gap_groups and all(
        nonnegative_from(sp.expand(gap - expected_min_gap), threshold) for gap in gap_groups
    )
    anchor_ok = domination_ok and exact_ok and anchor_formula_ok and min_gap_formula_ok
    print(
        f"  (d) anchor C_f={anchor_c}, m_f={anchor_m}, T_f={anchor_total}; "
        f"all-s formulas={'PASS' if anchor_formula_ok else 'FAIL'}; "
        f"coordinate domination={'PASS' if domination_ok else 'FAIL'}"
    )
    print(
        f"      exact discounted adverse payment r={threshold}..{max_r}: "
        f"{'PASS' if exact_ok else 'FAIL'}; "
        f"minimum-gap crude payment: {'PASS' if crude_ok else 'FAIL'}"
    )
    print(f"      exact payment/anchor ratios: {[f'{ratio:.3e}' for ratio in ratios]}")
    if show_groups:
        print("      discount groups (gap -> family count, exact coefficient mass):")
        for gap in sorted(gap_groups, key=sp.default_sort_key):
            print(f"        {gap} -> {gap_counts[gap]}, {sp.factor(gap_groups[gap])}")
    else:
        print(
            f"      discount groups: {len(gap_groups)} distinct "
            "(pass --show-groups for exact coefficient masses)"
        )
    print(
        "      minimum gap on checked tail: "
        + ", ".join(str(gap) for gap in sorted(minimum_gap_keys, key=sp.default_sort_key))
    )
    print(
        f"      symbolic minimum-gap formula 2r-2(s-1)={expected_min_gap}: "
        f"{'PASS' if min_gap_formula_ok else 'FAIL'}"
    )
    if domination_bad:
        for family, margin, gap in domination_bad[:8]:
            print(
                f"      DOMINATION FAIL family {(family.i, family.j, family.a_index, family.m_index)}: "
                f"low_margin={margin}, total_gap={gap}"
            )

    print(
        "  (e) cumulative identity: C(s,r,2) = R(s,r+1) + R(s+1,r) (PASS by the defining recursion)"
    )
    if skip_prefix:
        finite_ok = True
        print("  (f) finite prefix: skipped")
    else:
        finite_ok = finite_prefix_report(s, families, threshold)
    if sweep_prefix:
        prefix_sign_sweep(s, threshold)
    structural_ok = family_count_ok and parity_ok and sign_ok and anchor_ok
    print(f"  STRUCTURAL TAIL s={s}: {'PASS' if structural_ok else 'REFUTED'}")
    if not skip_prefix:
        print(f"  SIMPLE FINITE-PREFIX TACTIC s={s}: {'PASS' if finite_ok else 'NEEDS REFINEMENT'}")
    return structural_ok, finite_ok


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, nargs="+", default=[1, 2, 3])
    parser.add_argument("--max-r", type=int, default=120)
    parser.add_argument("--show-groups", action="store_true")
    parser.add_argument("--skip-prefix", action="store_true")
    parser.add_argument("--sweep-prefix", action="store_true")
    args = parser.parse_args()
    outcomes = [
        scout_row(s, args.max_r, args.show_groups, args.skip_prefix, args.sweep_prefix)
        for s in args.rows
    ]
    print("\n== decision ==")
    if all(structural for structural, _ in outcomes):
        print("STRUCTURAL SCOUT SURVIVES: pursue one Lean tail module symbolic in both s and r.")
        if not all(finite for _, finite in outcomes):
            print(
                "FINITE PREFIX NEEDS GROUPING: at least one cell requires positive "
                "nonconstant reserves; this does not refute the tail scheme."
            )
    else:
        print("STRUCTURAL SCOUT REFUTED: bank the failing invariant and redesign the tail proof.")


if __name__ == "__main__":
    main()
