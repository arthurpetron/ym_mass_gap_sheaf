#!/usr/bin/env python3
"""Generate a staged Lean certificate for one BF4 surface contraction.

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
    if coefficient.num == 0:
        return polynomial
    prefix: Poly = []
    for index, (other_monomial, other_coefficient) in enumerate(polynomial):
        if monomial < other_monomial:
            return prefix + [(monomial, coefficient)] + polynomial[index:]
        if monomial == other_monomial:
            combined = coefficient + other_coefficient
            replacement = [] if combined.num == 0 else [(monomial, combined)]
            return prefix + replacement + polynomial[index + 1:]
        prefix.append((other_monomial, other_coefficient))
    return prefix + [(monomial, coefficient)]


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
TORUS_CHORD_ORDER = [
    13, 14, 16, 9, 18, 21, 28, 22, 29, 20, 24, 30, 23, 25, 27, 26, 31,
]
EDGE_INCIDENCE_MASKS = [
    7, 25, 42, 52, 196, 336, 416, 1538, 2568, 3104, 5248, 6400,
    24577, 40968, 49168, 81984, 98560, 139776, 165888, 200704,
    786433, 1310722, 1572868, 2621504, 3145856, 4456960, 5243904,
    6295552, 8658944, 8929280, 10551296, 12713984,
]
BINARY_SURFACE_BASIS = [
    2707861, 1049766, 35128, 2167232, 4333056, 8642560, 16515072,
]
HYPERCUBE_EDGE_ENDPOINTS = [
    (0, 8), (0, 4), (0, 2), (0, 1), (1, 9), (1, 5), (1, 3),
    (2, 10), (2, 6), (2, 3), (3, 11), (3, 7), (4, 12), (4, 6),
    (4, 5), (5, 13), (5, 7), (6, 14), (6, 7), (7, 15), (8, 12),
    (8, 10), (8, 9), (9, 13), (9, 11), (10, 14), (10, 11),
    (11, 15), (12, 14), (12, 13), (13, 15), (14, 15),
]


def selected_surface_edges(mask: int) -> list[int]:
    return [
        edge
        for edge, incidence in enumerate(EDGE_INCIDENCE_MASKS)
        if (incidence & mask).bit_count() > 0
    ]


def binary_surface_masks() -> list[int]:
    output = []
    for coefficient in range(128):
        remaining = coefficient
        mask = 0
        for basis in BINARY_SURFACE_BASIS:
            if remaining % 2 == 1:
                mask ^= basis
            remaining //= 2
        output.append(mask)
    return output


def canonical_surface_chords(mask: int) -> list[int]:
    labels = list(range(16))
    forest: list[int] = []
    selected = set(selected_surface_edges(mask))
    for edge, (tail, head) in enumerate(HYPERCUBE_EDGE_ENDPOINTS):
        if edge not in selected:
            continue
        left_label = labels[tail]
        right_label = labels[head]
        if left_label == right_label:
            continue
        labels = [
            left_label if label == right_label else label for label in labels
        ]
        forest.append(edge)
    return [edge for edge in selected_surface_edges(mask) if edge not in forest]


def surface_chord_order(mask: int) -> list[int]:
    return TORUS_CHORD_ORDER if mask == MASK else canonical_surface_chords(mask)


def forest_gauge_words(mask: int, chord_order: list[int]) -> list[Word]:
    chord_index = {edge: index for index, edge in enumerate(chord_order)}
    selected = [index for index in range(24) if mask & (1 << index)]
    return [
        [
            (chord_index[edge], reverse)
            for edge, reverse in HYPERCUBE_FACE_WORDS[face]
            if edge in chord_index
        ]
        for face in selected
    ]


def stages(mask: int = MASK, chord_order: list[int] | None = None) -> list[Factors]:
    if chord_order is None:
        chord_order = surface_chord_order(mask)
    output = [[
        fundamental_word_factor(word)
        for word in forest_gauge_words(mask, chord_order)
    ]]
    for _block in chord_order:
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


def emit_lean(
    all_stages: list[Factors], mask: int = MASK,
    chord_order: list[int] | None = None,
) -> str:
    if chord_order is None:
        chord_order = surface_chord_order(mask)
    suffix = f"{mask:06X}"
    lines = [
        f"/- Generated proof-carrying checkpoints for BF4 mask 0x{mask:06x}.",
        "   Regenerate with computations/generate_bf4_forest_gauge_staged.py. -/",
        "",
        "import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge",
        "",
        f"namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask{suffix}",
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
            f"def stage0 := surfaceForestGaugeFactors {mask}",
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
            f"theorem contraction{len(chord_order)}_exact :",
            f"    compactBivalentFactorizedHaarContract {len(chord_order)} stage0 =",
            f"      factorProduct (nonUnitFactors stage{len(chord_order)}) := by",
        ]
    )
    for index in range(1, len(all_stages)):
        remaining = len(chord_order) - index
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
            f"    surfaceForestGaugeHaar {mask} ≈",
            f"      surfaceTopologicalHaarAmplitude {mask} := by",
            "  unfold surfaceForestGaugeHaar compactBivalentFactorizedHaar",
            "  change quaternionHaar 0",
            f"      (compactBivalentFactorizedHaarContract {len(chord_order)} stage0) ≈ _",
            f"  rw [contraction{len(chord_order)}_exact]",
            "  decide",
        ]
    )
    lines.extend(
        [
            "",
            f"end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask{suffix}",
            "",
            f"#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask{suffix}.forestGaugeHaar_exact",
            "",
        ]
    )
    return "\n".join(lines)


def mask_module_name(mask: int) -> str:
    return f"BF4ExactCutoffOneSurfaceForestGaugeMask{mask:06X}"


def emit_all_evaluation_umbrella(masks: list[int]) -> str:
    nonzero_masks = [mask for mask in masks if mask != 0]
    lines = [
        "/- Generated complete finite BF4 forest-gauge evaluation umbrella.",
        "   Every imported per-mask checkpoint is independently kernel-checked. -/",
        "",
    ]
    lines.extend(
        f"import YMGap.Continuum.{mask_module_name(mask)}"
        for mask in nonzero_masks
    )
    lines.extend(
        [
            "",
            "namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeAllEvaluation",
            "",
            "set_option maxRecDepth 300000",
            "set_option maxHeartbeats 12000000",
            "",
            "open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate",
            "open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge",
            "",
            "def binarySurfaceMasksLiteral : List Nat :=",
            "  [" + ", ".join(str(mask) for mask in masks) + "]",
            "",
            "theorem binarySurfaceMasks_eq_literal :",
            "    binarySurfaceMasks = binarySurfaceMasksLiteral := by",
            "  decide",
            "",
            "/-- Every concrete nonempty forest-gauge network has its exact",
            "topological Haar value, by exhaustive proof-carrying contraction. -/",
            "theorem cutoffOneSurfaceForestGaugeEvaluation :",
            "    CutoffOneSurfaceForestGaugeEvaluation := by",
            "  intro mask hmask hnonzero",
            "  have hcases :",
        ]
    )
    alternatives = [f"mask = {mask}" for mask in masks]
    for index, alternative in enumerate(alternatives):
        prefix = "      " if index == 0 else "        "
        suffix = " ∨" if index + 1 < len(alternatives) else " := by"
        lines.append(f"{prefix}{alternative}{suffix}")
    lines.extend(
        [
            "    rw [binarySurfaceMasks_eq_literal] at hmask",
            "    simpa only [binarySurfaceMasksLiteral, List.mem_cons,",
            "      List.not_mem_nil, or_false] using hmask",
        ]
    )
    for index, mask in enumerate(masks):
        if index + 1 < len(masks):
            lines.append(f"  rcases hcases with h{index} | hcases")
            lines.append(f"  · subst mask")
            indent = "    "
        else:
            lines.append(f"  have h{index} := hcases")
            lines.append("  subst mask")
            indent = "  "
        if mask == 0:
            lines.append(f"{indent}exact False.elim (hnonzero rfl)")
        else:
            namespace = (
                "YMGap.Continuum."
                f"BF4ExactCutoffOneSurfaceForestGaugeMask{mask:06X}"
            )
            lines.append(f"{indent}exact {namespace}.forestGaugeHaar_exact")
    lines.extend(
        [
            "",
            "end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeAllEvaluation",
            "",
            "#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeAllEvaluation.cutoffOneSurfaceForestGaugeEvaluation",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--mask", type=lambda value: int(value, 0), default=MASK)
    parser.add_argument("--survey-binary", action="store_true")
    parser.add_argument("--all-output-dir", type=Path)
    args = parser.parse_args()
    if args.survey_binary:
        for mask in binary_surface_masks():
            if mask == 0:
                continue
            chord_order = surface_chord_order(mask)
            all_stages = stages(mask, chord_order)
            largest = max(
                (len(factor) for factors in all_stages for factor in factors),
                default=0,
            )
            total = max(
                (sum(len(factor) for factor in factors) for factors in all_stages),
                default=0,
            )
            print(
                f"0x{mask:06x} faces={mask.bit_count():2d} "
                f"chords={len(chord_order):2d} largest={largest:6d} "
                f"stage-terms={total:6d}"
            )
        return
    if args.all_output_dir is not None:
        masks = binary_surface_masks()
        for mask in masks:
            if mask == 0:
                continue
            chord_order = surface_chord_order(mask)
            all_stages = stages(mask, chord_order)
            output = args.all_output_dir / f"{mask_module_name(mask)}.lean"
            output.write_text(
                emit_lean(all_stages, mask, chord_order), encoding="utf-8"
            )
            print(
                f"wrote {output.name}: faces={mask.bit_count()} "
                f"chords={len(chord_order)} stages={len(all_stages) - 1}"
            )
        umbrella = (
            args.all_output_dir /
            "BF4ExactCutoffOneSurfaceForestGaugeAllEvaluation.lean"
        )
        umbrella.write_text(
            emit_all_evaluation_umbrella(masks), encoding="utf-8"
        )
        print(f"wrote {umbrella.name}: masks={len(masks)}")
        return
    chord_order = surface_chord_order(args.mask)
    all_stages = stages(args.mask, chord_order)
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
        args.output.write_text(
            emit_lean(all_stages, args.mask, chord_order), encoding="utf-8"
        )


if __name__ == "__main__":
    main()
