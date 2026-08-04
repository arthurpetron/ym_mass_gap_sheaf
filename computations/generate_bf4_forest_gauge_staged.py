#!/usr/bin/env python3
"""Generate a staged Lean certificate for the BF4 0x6f6d9e contraction.

The generator mirrors the list-level definitions used by
``compactBivalentFactorizedHaarContract``.  Its output is not trusted:
every generated checkpoint is re-evaluated and proved by Lean's kernel.
Splitting the seventeen head integrations into separate theorems prevents
one enormous reduction from exhausting memory or a monolithic heartbeat
budget.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, TypeAlias


@dataclass(frozen=True)
class QRaw:
    """Lean ``Q'`` exactly, including its deliberately unreduced denominator."""

    num: int
    den_pred: int = 0

    @property
    def den(self) -> int:
        return self.den_pred + 1

    def __neg__(self) -> "QRaw":
        return QRaw(-self.num, self.den_pred)

    def __add__(self, other: "QRaw") -> "QRaw":
        denominator = self.den * other.den
        return QRaw(
            self.num * other.den + other.num * self.den,
            denominator - 1,
        )

    def __mul__(self, other: "QRaw") -> "QRaw":
        denominator = self.den * other.den
        return QRaw(self.num * other.num, denominator - 1)


Q_ZERO = QRaw(0)
Q_ONE = QRaw(1)
Q_TWO = QRaw(2)

Mono: TypeAlias = tuple[int, ...]
Term: TypeAlias = tuple[Mono, QRaw]
Poly: TypeAlias = list[Term]
Factors: TypeAlias = list[Poly]
Quaternion: TypeAlias = tuple[Poly, Poly, Poly, Poly]
Word: TypeAlias = list[tuple[int, bool]]


def var_mono(index: int) -> Mono:
    return (0,) * index + (1,)


def mono_mul(left: Mono, right: Mono) -> Mono:
    if not left:
        return right
    if not right:
        return left
    width = max(len(left), len(right))
    return tuple(
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(width)
    )


def poly_var(index: int) -> Poly:
    return [(var_mono(index), Q_ONE)]


def poly_add(left: Poly, right: Poly) -> Poly:
    return left + right


def poly_neg(poly: Poly) -> Poly:
    return [(monomial, -coefficient) for monomial, coefficient in poly]


def poly_smul(coefficient: QRaw, poly: Poly) -> Poly:
    return [
        (monomial, coefficient * old_coefficient)
        for monomial, old_coefficient in poly
    ]


def poly_mul(left: Poly, right: Poly) -> Poly:
    return [
        (mono_mul(source_monomial, target_monomial), source_coefficient * target_coefficient)
        for source_monomial, source_coefficient in left
        for target_monomial, target_coefficient in right
    ]


P_ZERO: Poly = []
P_ONE: Poly = [((), Q_ONE)]
Q_ID: Quaternion = (P_ONE, P_ZERO, P_ZERO, P_ZERO)


def coordinate_quaternion(block: int) -> Quaternion:
    return tuple(poly_var(4 * block + component) for component in range(4))  # type: ignore[return-value]


def quaternion_conj(quaternion: Quaternion) -> Quaternion:
    scalar, i_part, j_part, k_part = quaternion
    return scalar, poly_neg(i_part), poly_neg(j_part), poly_neg(k_part)


def quaternion_mul(left: Quaternion, right: Quaternion) -> Quaternion:
    a, b, c, d = left
    e, f, g, h = right
    scalar = poly_add(
        poly_mul(a, e),
        poly_neg(
            poly_add(
                poly_mul(b, f),
                poly_add(poly_mul(c, g), poly_mul(d, h)),
            )
        ),
    )
    i_part = poly_add(
        poly_mul(a, f),
        poly_add(
            poly_mul(b, e),
            poly_add(poly_mul(c, h), poly_neg(poly_mul(d, g))),
        ),
    )
    j_part = poly_add(
        poly_mul(a, g),
        poly_add(
            poly_mul(c, e),
            poly_add(poly_mul(d, f), poly_neg(poly_mul(b, h))),
        ),
    )
    k_part = poly_add(
        poly_mul(a, h),
        poly_add(
            poly_mul(d, e),
            poly_add(poly_mul(b, g), poly_neg(poly_mul(c, f))),
        ),
    )
    return scalar, i_part, j_part, k_part


def fundamental_word_factor(word: Word) -> Poly:
    total = Q_ID
    for block, reverse in word:
        quaternion = coordinate_quaternion(block)
        total = quaternion_mul(total, quaternion_conj(quaternion) if reverse else quaternion)
    return poly_smul(Q_TWO, total[0])


def odd_double_factorial(index: int) -> int:
    value = 1
    for step in range(index):
        value *= 2 * step + 1
    return value


def sphere_four_denominator(index: int) -> int:
    value = 1
    for step in range(index):
        value *= 4 + 2 * step
    return value


def head_quaternion_moment(monomial: Mono) -> QRaw:
    exponents = tuple(monomial[index] if index < len(monomial) else 0 for index in range(4))
    if any(exponent % 2 for exponent in exponents):
        return Q_ZERO
    half = tuple(exponent // 2 for exponent in exponents)
    numerator = 1
    for exponent in half:
        numerator *= odd_double_factorial(exponent)
    denominator = sphere_four_denominator(sum(half))
    return QRaw(numerator, denominator - 1)


def insert_rat_term(monomial: Mono, coefficient: QRaw, polynomial: Poly) -> Poly:
    if not polynomial:
        return [] if coefficient.num == 0 else [(monomial, coefficient)]
    other_monomial, other_coefficient = polynomial[0]
    rest = polynomial[1:]
    if coefficient.num == 0:
        return polynomial
    if monomial < other_monomial:
        return [(monomial, coefficient)] + polynomial
    if monomial == other_monomial:
        combined = coefficient + other_coefficient
        return rest if combined.num == 0 else [(monomial, combined)] + rest
    return [(other_monomial, other_coefficient)] + insert_rat_term(
        monomial, coefficient, rest
    )


def canon_rat(polynomial: Poly) -> Poly:
    accumulated: Poly = []
    for monomial, coefficient in reversed(polynomial):
        accumulated = insert_rat_term(monomial, coefficient, accumulated)
    return accumulated


def head_independent(polynomial: Poly) -> bool:
    return all(sum(monomial[:4]) == 0 for monomial, _coefficient in polynomial)


def drop_head(polynomial: Poly) -> Poly:
    return [(monomial[4:], coefficient) for monomial, coefficient in polynomial]


def direct_partial_haar_product(left: Poly, right: Poly) -> Poly:
    output: Poly = []
    for source_monomial, source_coefficient in left:
        for target_monomial, target_coefficient in right:
            product_monomial = mono_mul(source_monomial, target_monomial)
            coefficient = (
                (source_coefficient * target_coefficient)
                * head_quaternion_moment(product_monomial)
            )
            if coefficient.num != 0:
                output.append(
                    (
                        mono_mul(source_monomial[4:], target_monomial[4:]),
                        coefficient,
                    )
                )
    return output


def factor_product(factors: Factors) -> Poly:
    product = P_ONE
    for factor in reversed(factors):
        product = poly_mul(factor, product)
    return product


def partial_haar_head(polynomial: Poly) -> Poly:
    return [
        (monomial[4:], coefficient * head_quaternion_moment(monomial))
        for monomial, coefficient in polynomial
    ]


def compact_bivalent_head_step(factors: Factors) -> Factors:
    incident = [factor for factor in factors if not head_independent(factor)]
    independent = [factor for factor in factors if head_independent(factor)]
    if len(incident) == 2:
        left, right = incident
        integrated = canon_rat(direct_partial_haar_product(left, poly_mul(right, P_ONE)))
    else:
        integrated = canon_rat(partial_haar_head(factor_product(incident)))
    stepped = [integrated] + [drop_head(factor) for factor in independent]
    return [factor for factor in stepped if factor != P_ONE]


HYPERCUBE_FACE_WORDS: list[Word] = [
    [(0, False), (20, False), (12, True), (1, True)],
    [(0, False), (21, False), (7, True), (2, True)],
    [(0, False), (22, False), (4, True), (3, True)],
    [(1, False), (13, False), (8, True), (2, True)],
    [(1, False), (14, False), (5, True), (3, True)],
    [(2, False), (9, False), (6, True), (3, True)],
    [(4, False), (23, False), (15, True), (5, True)],
    [(4, False), (24, False), (10, True), (6, True)],
    [(5, False), (16, False), (11, True), (6, True)],
    [(7, False), (25, False), (17, True), (8, True)],
    [(7, False), (26, False), (10, True), (9, True)],
    [(8, False), (18, False), (11, True), (9, True)],
    [(10, False), (27, False), (19, True), (11, True)],
    [(12, False), (28, False), (17, True), (13, True)],
    [(12, False), (29, False), (15, True), (14, True)],
    [(13, False), (18, False), (16, True), (14, True)],
    [(15, False), (30, False), (19, True), (16, True)],
    [(17, False), (31, False), (19, True), (18, True)],
    [(20, False), (28, False), (25, True), (21, True)],
    [(20, False), (29, False), (23, True), (22, True)],
    [(21, False), (26, False), (24, True), (22, True)],
    [(23, False), (30, False), (27, True), (24, True)],
    [(25, False), (31, False), (27, True), (26, True)],
    [(28, False), (31, False), (30, True), (29, True)],
]

MASK = 0x6F6D9E
CHORD_ORDER = [13, 14, 16, 9, 18, 21, 28, 22, 29, 20, 24, 30, 23, 25, 27, 26, 31]


def forest_gauge_words() -> list[Word]:
    chord_index = {edge: index for index, edge in enumerate(CHORD_ORDER)}
    selected = [index for index in range(24) if MASK & (1 << index)]
    return [
        [
            (chord_index[edge], reverse)
            for edge, reverse in HYPERCUBE_FACE_WORDS[face]
            if edge in chord_index
        ]
        for face in selected
    ]


def stages() -> list[Factors]:
    output = [[fundamental_word_factor(word) for word in forest_gauge_words()]]
    for _block in CHORD_ORDER:
        output.append(compact_bivalent_head_step(output[-1]))
    return output


def lean_nat_list(values: Iterable[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_q(value: QRaw) -> str:
    return f"{{ num := {value.num}, denPred := {value.den_pred} }}"


def lean_poly(polynomial: Poly) -> str:
    terms = ",\n      ".join(
        f"({lean_nat_list(monomial)}, {lean_q(coefficient)})"
        for monomial, coefficient in polynomial
    )
    return "[" + terms + "]"


def lean_factors(factors: Factors) -> str:
    rendered = ",\n    ".join(lean_poly(polynomial) for polynomial in factors)
    return "[" + rendered + "]"


def emit_lean(all_stages: list[Factors]) -> str:
    lines = [
        "/- Generated proof-carrying checkpoints for BF4 mask 0x6f6d9e.",
        "   Regenerate with computations/generate_bf4_forest_gauge_staged.py. -/",
        "",
        "import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge",
        "",
        "namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit6F6D9E",
        "",
        "set_option maxRecDepth 200000",
        "set_option maxHeartbeats 12000000",
        "",
        "open YMGap.Constructive",
        "open YMGap.Continuum.BF4GeometricHaarMehlerProjection",
        "open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation",
        "open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge",
        "open YMGap.Continuum.SU2QuaternionBivalentHaarContraction",
        "open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction",
        "open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier",
        "",
        "local infix:50 \" ≈ \" => Q'.eqv",
        "",
    ]
    # Stage zero is retained as the actual geometric definition, avoiding a
    # large and unnecessary raw-factor literal.  Every later stage is literal.
    lines.extend(
        [
            "def stage0 := surfaceForestGaugeFactors 7302558",
            "",
        ]
    )
    for index, factors in enumerate(all_stages[1:], start=1):
        lines.extend(
            [
                f"def stage{index} : List RatPoly :=",
                f"  {lean_factors(factors)}",
                "",
                f"theorem stage{index}_exact :",
                f"    compactBivalentFactorizedHeadStep stage{index - 1} = stage{index} := by",
                "  decide",
                "",
            ]
        )
    lines.extend(
        [
            "theorem contraction17_exact :",
            "    compactBivalentFactorizedHaarContract 17 stage0 =",
            "      factorProduct (nonUnitFactors stage17) := by",
        ]
    )
    for index in range(1, len(all_stages)):
        remaining = len(CHORD_ORDER) - index
        lines.extend(
            [
                f"  change compactBivalentFactorizedHaarContract {remaining}",
                f"      (compactBivalentFactorizedHeadStep stage{index - 1}) = _",
                f"  rw [stage{index}_exact]",
            ]
        )
    lines.extend(
        [
            "  rfl",
            "",
            "theorem forestGaugeHaar_exact :",
            "    surfaceForestGaugeHaar 7302558 ≈",
            "      surfaceTopologicalHaarAmplitude 7302558 := by",
            "  unfold surfaceForestGaugeHaar compactBivalentFactorizedHaar",
            "  change quaternionHaar 0",
            "      (compactBivalentFactorizedHaarContract 17 stage0) ≈ _",
            "  rw [contraction17_exact]",
            "  decide",
        ]
    )
    lines.extend(
        [
            "",
            "end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit6F6D9E",
            "",
            "#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit6F6D9E.forestGaugeHaar_exact",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    all_stages = stages()
    for index, factors in enumerate(all_stages):
        term_count = sum(len(factor) for factor in factors)
        largest = max((len(factor) for factor in factors), default=0)
        coefficient_bits = max(
            (
                max(abs(coefficient.num).bit_length(), coefficient.den.bit_length())
                for factor in factors
                for _monomial, coefficient in factor
            ),
            default=0,
        )
        print(
            f"stage {index:02d}: factors={len(factors):2d} "
            f"terms={term_count:5d} largest={largest:5d} "
            f"coefficient_bits={coefficient_bits}"
        )
    if args.output is not None:
        args.output.write_text(emit_lean(all_stages), encoding="utf-8")


if __name__ == "__main__":
    main()
