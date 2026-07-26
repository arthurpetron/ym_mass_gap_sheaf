"""Exact open-magnetic-index SU(2) tensors for the BF4 transverse carrier.

All representation and magnetic labels are doubled integers.  The
Condon--Shortley Clebsch--Gordan coefficient is evaluated by its terminating
factorial sum and stored as a signed :class:`QuadRadical`; its square is
therefore an exact :class:`fractions.Fraction`.

Two tensor families are exposed:

* normalized three-leg invariant vectors at the five internal transverse
  links; and
* complete Clebsch--Gordan isometries at the nine protected boundary links.

An incoming oriented leg is identified with the self-dual SU(2)
representation through

    |j,m>* -> (-1)^(j-m) |j,-m>.

This is a signed permutation of the magnetic basis, so it preserves the
exact orthonormality and completeness identities checked here.

The formula is valid for arbitrary nonnegative doubled labels.  Finite
audits through a requested cutoff materialize the corresponding tensors and
verify their identities exactly.  This does not yet contract the tensors
through the whole transverse graph, evaluate global F/R transport, establish
a carrier-norm cutoff modulus, or prove CP-order domination.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial
from typing import cast

from computations.exact_haar_network import fusion_labels
from computations.transverse_all_label_recoupling import (
    BoundaryFusionChannel,
    FiniteCutoffTransverseRecouplingCarrier,
    OrientedCoreLeg,
    TrivalentInvariantChannel,
    finite_cutoff_transverse_recoupling_carrier,
)
from computations.wigner_6j import QuadRadical

MagneticTuple = tuple[int, ...]
SparseComponents = tuple[tuple[MagneticTuple, QuadRadical], ...]


def magnetic_indices(label: int) -> tuple[int, ...]:
    """Return the doubled magnetic labels ``-j, -j+1, ..., j``."""

    if label < 0:
        raise ValueError("a doubled representation label must be nonnegative")
    return tuple(range(-label, label + 1, 2))


def _magnetic_valid(label: int, magnetic: int) -> bool:
    return (
        label >= 0
        and abs(magnetic) <= label
        and (label - magnetic) % 2 == 0
    )


def _factorial_half(doubled_integer: int) -> int:
    """Return ``(doubled_integer / 2)!`` when the argument is even."""

    if doubled_integer < 0 or doubled_integer % 2:
        raise ValueError("the doubled factorial argument must be nonnegative and even")
    return factorial(doubled_integer // 2)


def _squarefree_integer_total(value: int) -> tuple[int, int]:
    """Factor ``value = square_part**2 * squarefree_part`` without a prime cap."""

    if value < 0:
        raise ValueError("squarefree extraction needs a nonnegative integer")
    if value == 0:
        return 0, 0
    square_part = 1
    squarefree_part = 1
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        exponent = 0
        while remaining % divisor == 0:
            remaining //= divisor
            exponent += 1
        square_part *= divisor ** (exponent // 2)
        if exponent % 2:
            squarefree_part *= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        squarefree_part *= remaining
    return square_part, squarefree_part


def _quad_from_coeff_radicand(
    coefficient: Fraction,
    radicand: Fraction,
) -> QuadRadical:
    """Construct a canonical radical using total finite factorization."""

    if radicand < 0:
        raise ValueError("a quadratic radicand must be nonnegative")
    if coefficient == 0 or radicand == 0:
        return QuadRadical.zero()
    numerator = radicand.numerator
    denominator = radicand.denominator
    square_part, squarefree_part = _squarefree_integer_total(
        numerator * denominator
    )
    return QuadRadical(
        coefficient * Fraction(square_part, denominator),
        squarefree_part,
    )


def _quad_from_parts(coefficient: Fraction, radicand: int) -> QuadRadical:
    return _quad_from_coeff_radicand(coefficient, Fraction(radicand))


def _quad_product(left: QuadRadical, right: QuadRadical) -> QuadRadical:
    return _quad_from_parts(
        left.coeff * right.coeff,
        left.rad * right.rad,
    )


def clebsch_gordan_doubled(
    left_label: int,
    left_magnetic: int,
    right_label: int,
    right_magnetic: int,
    output_label: int,
    output_magnetic: int,
) -> QuadRadical:
    """Return one exact Condon--Shortley Clebsch--Gordan coefficient.

    This implements the standard terminating factorial formula for

    ``<left,left_magnetic; right,right_magnetic | output,output_magnetic>``.

    Invalid fusion or magnetic selections return exact zero.  Negative
    representation labels are rejected.
    """

    if min(left_label, right_label, output_label) < 0:
        raise ValueError("doubled representation labels must be nonnegative")
    if (
        output_label not in fusion_labels(left_label, right_label)
        or not _magnetic_valid(left_label, left_magnetic)
        or not _magnetic_valid(right_label, right_magnetic)
        or not _magnetic_valid(output_label, output_magnetic)
        or left_magnetic + right_magnetic != output_magnetic
    ):
        return QuadRadical.zero()

    triangle_factor = Fraction(
        (output_label + 1)
        * _factorial_half(output_label + left_label - right_label)
        * _factorial_half(output_label - left_label + right_label)
        * _factorial_half(left_label + right_label - output_label),
        _factorial_half(left_label + right_label + output_label + 2),
    )
    magnetic_factor = (
        _factorial_half(output_label + output_magnetic)
        * _factorial_half(output_label - output_magnetic)
        * _factorial_half(left_label - left_magnetic)
        * _factorial_half(left_label + left_magnetic)
        * _factorial_half(right_label - right_magnetic)
        * _factorial_half(right_label + right_magnetic)
    )
    radicand = triangle_factor * magnetic_factor

    signed_sum = Fraction(0)
    maximum_k = (
        left_label + right_label + output_label
    ) // 2 + 1
    for k in range(maximum_k):
        doubled_arguments = (
            2 * k,
            left_label + right_label - output_label - 2 * k,
            left_label - left_magnetic - 2 * k,
            right_label + right_magnetic - 2 * k,
            output_label - right_label + left_magnetic + 2 * k,
            output_label - left_label - right_magnetic + 2 * k,
        )
        if any(argument < 0 or argument % 2 for argument in doubled_arguments):
            continue
        denominator = 1
        for argument in doubled_arguments:
            denominator *= _factorial_half(argument)
        signed_sum += Fraction((-1) ** k, denominator)
    return _quad_from_coeff_radicand(signed_sum, radicand)


def _oriented_magnetic(
    label: int,
    magnetic: int,
    orientation: int,
) -> tuple[int, int]:
    """Transport one oriented leg to the canonical outgoing basis."""

    if not _magnetic_valid(label, magnetic):
        raise ValueError("the magnetic label does not belong to the representation")
    if orientation == 1:
        return magnetic, 1
    if orientation == -1:
        return -magnetic, (-1) ** ((label - magnetic) // 2)
    raise ValueError("a leg orientation must be +1 or -1")


def oriented_clebsch_gordan_doubled(
    left_label: int,
    left_magnetic: int,
    left_orientation: int,
    right_label: int,
    right_magnetic: int,
    right_orientation: int,
    output_label: int,
    output_magnetic: int,
) -> QuadRadical:
    """Return the CG component after self-dualizing incoming face legs."""

    canonical_left, left_phase = _oriented_magnetic(
        left_label,
        left_magnetic,
        left_orientation,
    )
    canonical_right, right_phase = _oriented_magnetic(
        right_label,
        right_magnetic,
        right_orientation,
    )
    return (
        left_phase
        * right_phase
        * clebsch_gordan_doubled(
            left_label,
            canonical_left,
            right_label,
            canonical_right,
            output_label,
            output_magnetic,
        )
    )


def trivalent_invariant_component(
    labels: tuple[int, int, int],
    magnetics: tuple[int, int, int],
    orientations: tuple[int, int, int] = (1, 1, 1),
) -> QuadRadical:
    """Return one normalized oriented three-leg invariant component.

    In the all-outgoing basis this is

    ``(-1)^(j1-j2-m3) / sqrt(dim(j3))
    * C(j1,m1;j2,m2|j3,-m3)``.

    This is the ordered Wigner-three-j convention, expressed in doubled
    labels.  Its label-dependent phase must be fixed before global recoupling.
    """

    if len(labels) != 3 or len(magnetics) != 3 or len(orientations) != 3:
        raise ValueError("a trivalent invariant needs exactly three legs")
    if min(labels) < 0:
        raise ValueError("doubled representation labels must be nonnegative")
    if any(orientation not in (-1, 1) for orientation in orientations):
        raise ValueError("a leg orientation must be +1 or -1")
    if (
        labels[2] not in fusion_labels(labels[0], labels[1])
        or not all(
            _magnetic_valid(label, magnetic)
            for label, magnetic in zip(labels, magnetics, strict=True)
        )
    ):
        return QuadRadical.zero()
    canonical: list[int] = []
    phase = 1
    for label, magnetic, orientation in zip(
        labels,
        magnetics,
        orientations,
        strict=True,
    ):
        transported, leg_phase = _oriented_magnetic(
            label,
            magnetic,
            orientation,
        )
        canonical.append(transported)
        phase *= leg_phase
    three_j_exponent = (
        labels[0] - labels[1] - canonical[2]
    ) // 2
    third_phase = 1 if three_j_exponent % 2 == 0 else -1
    coefficient = clebsch_gordan_doubled(
        labels[0],
        canonical[0],
        labels[1],
        canonical[1],
        labels[2],
        -canonical[2],
    )
    return _quad_product(
        (phase * third_phase) * coefficient,
        _quad_from_coeff_radicand(
            Fraction(1),
            Fraction(1, labels[2] + 1),
        ),
    )


def _magnetic_triples(
    labels: tuple[int, int, int],
) -> tuple[tuple[int, int, int], ...]:
    return tuple(
        (first, second, third)
        for first in magnetic_indices(labels[0])
        for second in magnetic_indices(labels[1])
        for third in magnetic_indices(labels[2])
    )


@dataclass(frozen=True)
class RadicalSum:
    """Exact finite sum of squarefree quadratic radicals."""

    terms: tuple[tuple[int, Fraction], ...]

    @classmethod
    def zero(cls) -> RadicalSum:
        return cls(())

    @classmethod
    def rational(cls, value: Fraction | int) -> RadicalSum:
        coefficient = Fraction(value)
        return cls(()) if coefficient == 0 else cls(((1, coefficient),))

    @classmethod
    def from_quad(cls, value: QuadRadical) -> RadicalSum:
        return cls.zero() if value.is_zero() else cls(((value.rad, value.coeff),))

    @classmethod
    def from_terms(
        cls,
        terms: tuple[tuple[int, Fraction], ...],
    ) -> RadicalSum:
        collected: dict[int, Fraction] = {}
        for radicand, coefficient in terms:
            normalized = _quad_from_parts(coefficient, radicand)
            if normalized.is_zero():
                continue
            collected[normalized.rad] = (
                collected.get(normalized.rad, Fraction(0))
                + normalized.coeff
            )
        return cls(
            tuple(
                sorted(
                    (radicand, coefficient)
                    for radicand, coefficient in collected.items()
                    if coefficient
                )
            )
        )

    def __add__(self, other: RadicalSum) -> RadicalSum:
        return RadicalSum.from_terms(self.terms + other.terms)

    def __neg__(self) -> RadicalSum:
        return RadicalSum(
            tuple((radicand, -coefficient) for radicand, coefficient in self.terms)
        )

    def __sub__(self, other: RadicalSum) -> RadicalSum:
        return self + (-other)

    def __mul__(self, other: RadicalSum) -> RadicalSum:
        products: list[tuple[int, Fraction]] = []
        for left_rad, left_coefficient in self.terms:
            for right_rad, right_coefficient in other.terms:
                product_value = _quad_from_parts(
                    left_coefficient * right_coefficient,
                    left_rad * right_rad,
                )
                products.append((product_value.rad, product_value.coeff))
        return RadicalSum.from_terms(tuple(products))

    def is_zero(self) -> bool:
        return not self.terms


def _inner_product(
    left: tuple[QuadRadical, ...],
    right: tuple[QuadRadical, ...],
) -> RadicalSum:
    if len(left) != len(right):
        raise ValueError("inner-product vectors have different dimensions")
    total = RadicalSum.zero()
    for left_value, right_value in zip(left, right, strict=True):
        total += (
            RadicalSum.from_quad(left_value)
            * RadicalSum.from_quad(right_value)
        )
    return total


def _scaled_quad(value: QuadRadical, scale: Fraction) -> RadicalSum:
    return RadicalSum.from_quad(scale * value)


def _raising_coefficient(label: int, source_magnetic: int) -> QuadRadical:
    if (
        not _magnetic_valid(label, source_magnetic)
        or source_magnetic + 2 > label
    ):
        return QuadRadical.zero()
    return _quad_from_coeff_radicand(
        Fraction(1, 2),
        Fraction(
            (label - source_magnetic)
            * (label + source_magnetic + 2)
        ),
    )


def _lowering_coefficient(label: int, source_magnetic: int) -> QuadRadical:
    if (
        not _magnetic_valid(label, source_magnetic)
        or source_magnetic - 2 < -label
    ):
        return QuadRadical.zero()
    return _quad_from_coeff_radicand(
        Fraction(1, 2),
        Fraction(
            (label + source_magnetic)
            * (label - source_magnetic + 2)
        ),
    )


def _canonical_trivalent_generator_residuals(
    labels: tuple[int, int, int],
) -> tuple[int, int, int, int]:
    """Return checked components and nonzero ``Jz,J+,J-`` residual counts."""

    checked = 0
    nonzero_z = 0
    nonzero_raising = 0
    nonzero_lowering = 0
    for target in _magnetic_triples(labels):
        component = trivalent_invariant_component(labels, target)
        z_residual = _scaled_quad(
            component,
            Fraction(sum(target), 2),
        )
        raising_residual = RadicalSum.zero()
        lowering_residual = RadicalSum.zero()
        for leg_index, label in enumerate(labels):
            raising_source = list(target)
            raising_source[leg_index] -= 2
            if _magnetic_valid(label, raising_source[leg_index]):
                source_tuple = (
                    raising_source[0],
                    raising_source[1],
                    raising_source[2],
                )
                raising_residual += (
                    RadicalSum.from_quad(
                        _raising_coefficient(
                            label,
                            raising_source[leg_index],
                        )
                    )
                    * RadicalSum.from_quad(
                        trivalent_invariant_component(
                            labels,
                            source_tuple,
                        )
                    )
                )

            lowering_source = list(target)
            lowering_source[leg_index] += 2
            if _magnetic_valid(label, lowering_source[leg_index]):
                source_tuple = (
                    lowering_source[0],
                    lowering_source[1],
                    lowering_source[2],
                )
                lowering_residual += (
                    RadicalSum.from_quad(
                        _lowering_coefficient(
                            label,
                            lowering_source[leg_index],
                        )
                    )
                    * RadicalSum.from_quad(
                        trivalent_invariant_component(
                            labels,
                            source_tuple,
                        )
                    )
                )
        checked += 1
        nonzero_z += int(not z_residual.is_zero())
        nonzero_raising += int(not raising_residual.is_zero())
        nonzero_lowering += int(not lowering_residual.is_zero())
    return checked, nonzero_z, nonzero_raising, nonzero_lowering


@dataclass(frozen=True)
class TrivalentInvarianceAudit:
    """Exact Lie-generator annihilation of all canonical invariant tensors."""

    representation_cutoff: int
    admissible_label_triples: int
    magnetic_components_checked: int
    nonzero_jz_residuals: int
    nonzero_raising_residuals: int
    nonzero_lowering_residuals: int

    def validates(self) -> bool:
        return (
            self.representation_cutoff >= 0
            and self.admissible_label_triples > 0
            and self.magnetic_components_checked
            >= self.admissible_label_triples
            and self.nonzero_jz_residuals == 0
            and self.nonzero_raising_residuals == 0
            and self.nonzero_lowering_residuals == 0
        )


@cache
def trivalent_invariance_audit(
    representation_cutoff: int,
) -> TrivalentInvarianceAudit:
    """Check ``Jz``, ``J+`` and ``J-`` annihilation through one cutoff."""

    if representation_cutoff < 0:
        raise ValueError("the representation cutoff must be nonnegative")
    triples = tuple(
        (first, second, third)
        for first in range(representation_cutoff + 1)
        for second in range(representation_cutoff + 1)
        for third in range(representation_cutoff + 1)
        if third in fusion_labels(first, second)
    )
    checked = 0
    nonzero_z = 0
    nonzero_raising = 0
    nonzero_lowering = 0
    for labels in triples:
        (
            local_checked,
            local_z,
            local_raising,
            local_lowering,
        ) = _canonical_trivalent_generator_residuals(labels)
        checked += local_checked
        nonzero_z += local_z
        nonzero_raising += local_raising
        nonzero_lowering += local_lowering
    audit = TrivalentInvarianceAudit(
        representation_cutoff=representation_cutoff,
        admissible_label_triples=len(triples),
        magnetic_components_checked=checked,
        nonzero_jz_residuals=nonzero_z,
        nonzero_raising_residuals=nonzero_raising,
        nonzero_lowering_residuals=nonzero_lowering,
    )
    if not audit.validates():
        raise AssertionError("the trivalent Lie-generator audit failed")
    return audit


@dataclass(frozen=True)
class TrivalentMagneticTensor:
    """One normalized open magnetic tensor for an internal carrier channel."""

    link: int
    legs: tuple[OrientedCoreLeg, OrientedCoreLeg, OrientedCoreLeg]
    channel: TrivalentInvariantChannel
    components: SparseComponents

    def coefficient(self, magnetics: tuple[int, int, int]) -> QuadRadical:
        return dict(self.components).get(magnetics, QuadRadical.zero())

    def norm_squared(self) -> Fraction:
        return sum(
            (value.square for _magnetics, value in self.components),
            start=Fraction(0),
        )

    def validates(self) -> bool:
        labels = self.channel.leg_labels
        orientations = cast(
            tuple[int, int, int],
            tuple(leg.orientation for leg in self.legs),
        )
        expected = tuple(
            (magnetics, value)
            for magnetics in _magnetic_triples(labels)
            if not (
                value := trivalent_invariant_component(
                    labels,
                    magnetics,
                    orientations,
                )
            ).is_zero()
        )
        return (
            self.channel.validates()
            and all(leg.validates() for leg in self.legs)
            and self.components == expected
            and self.norm_squared() == 1
        )


@dataclass(frozen=True)
class BoundaryMagneticTensor:
    """One complete open-output CG tensor at a protected carrier link."""

    link: int
    legs: tuple[OrientedCoreLeg, OrientedCoreLeg]
    channel: BoundaryFusionChannel
    components: SparseComponents

    def coefficient(
        self,
        magnetics: tuple[int, int, int],
    ) -> QuadRadical:
        return dict(self.components).get(magnetics, QuadRadical.zero())

    def output_column(
        self,
        output_magnetic: int,
    ) -> tuple[QuadRadical, ...]:
        left, right = self.channel.leg_labels
        return tuple(
            self.coefficient((left_magnetic, right_magnetic, output_magnetic))
            for left_magnetic in magnetic_indices(left)
            for right_magnetic in magnetic_indices(right)
        )

    def validates(self) -> bool:
        left, right = self.channel.leg_labels
        output = self.channel.output_label
        orientations = tuple(leg.orientation for leg in self.legs)
        expected = tuple(
            ((left_magnetic, right_magnetic, output_magnetic), value)
            for left_magnetic in magnetic_indices(left)
            for right_magnetic in magnetic_indices(right)
            for output_magnetic in magnetic_indices(output)
            if not (
                value := oriented_clebsch_gordan_doubled(
                    left,
                    left_magnetic,
                    orientations[0],
                    right,
                    right_magnetic,
                    orientations[1],
                    output,
                    output_magnetic,
                )
            ).is_zero()
        )
        columns = tuple(
            self.output_column(output_magnetic)
            for output_magnetic in magnetic_indices(output)
        )
        return (
            self.channel.validates()
            and all(leg.validates() for leg in self.legs)
            and self.components == expected
            and all(
                _inner_product(first_column, second_column)
                == RadicalSum.rational(
                    int(first_index == second_index)
                )
                for first_index, first_column in enumerate(columns)
                for second_index, second_column in enumerate(columns)
            )
        )


def trivalent_magnetic_tensor(
    link: int,
    legs: tuple[OrientedCoreLeg, OrientedCoreLeg, OrientedCoreLeg],
    channel: TrivalentInvariantChannel,
) -> TrivalentMagneticTensor:
    """Materialize one sparse normalized internal invariant tensor."""

    labels = channel.leg_labels
    orientations = cast(
        tuple[int, int, int],
        tuple(leg.orientation for leg in legs),
    )
    components = tuple(
        (magnetics, value)
        for magnetics in _magnetic_triples(labels)
        if not (
            value := trivalent_invariant_component(
                labels,
                magnetics,
                orientations,
            )
        ).is_zero()
    )
    tensor = TrivalentMagneticTensor(link, legs, channel, components)
    if not tensor.validates():
        raise AssertionError("the trivalent magnetic tensor drifted")
    return tensor


def boundary_magnetic_tensor(
    link: int,
    legs: tuple[OrientedCoreLeg, OrientedCoreLeg],
    channel: BoundaryFusionChannel,
) -> BoundaryMagneticTensor:
    """Materialize one sparse protected-boundary CG tensor."""

    left, right = channel.leg_labels
    output = channel.output_label
    orientations = tuple(leg.orientation for leg in legs)
    components = tuple(
        ((left_magnetic, right_magnetic, output_magnetic), value)
        for left_magnetic in magnetic_indices(left)
        for right_magnetic in magnetic_indices(right)
        for output_magnetic in magnetic_indices(output)
        if not (
            value := oriented_clebsch_gordan_doubled(
                left,
                left_magnetic,
                orientations[0],
                right,
                right_magnetic,
                orientations[1],
                output,
                output_magnetic,
            )
        ).is_zero()
    )
    tensor = BoundaryMagneticTensor(link, legs, channel, components)
    if not tensor.validates():
        raise AssertionError("the boundary magnetic tensor drifted")
    return tensor


@dataclass(frozen=True)
class ClebschGordanBasisAudit:
    """Exact row-orthonormality and completeness sweep through one cutoff."""

    representation_cutoff: int
    ordered_representation_pairs: int
    coupled_basis_vectors: int
    product_basis_vectors: int
    orthonormality_entries_checked: int
    completeness_entries_checked: int
    nonzero_orthonormality_residuals: int
    nonzero_completeness_residuals: int

    def validates(self) -> bool:
        expected_vectors = sum(
            (left + 1) * (right + 1)
            for left in range(self.representation_cutoff + 1)
            for right in range(self.representation_cutoff + 1)
        )
        expected_entries = sum(
            ((left + 1) * (right + 1)) ** 2
            for left in range(self.representation_cutoff + 1)
            for right in range(self.representation_cutoff + 1)
        )
        return (
            self.representation_cutoff >= 0
            and self.ordered_representation_pairs
            == (self.representation_cutoff + 1) ** 2
            and self.coupled_basis_vectors
            == self.product_basis_vectors
            == expected_vectors
            and self.orthonormality_entries_checked
            == self.completeness_entries_checked
            == expected_entries
            and self.nonzero_orthonormality_residuals == 0
            and self.nonzero_completeness_residuals == 0
        )


@cache
def clebsch_gordan_basis_audit(
    representation_cutoff: int,
) -> ClebschGordanBasisAudit:
    """Verify the exact CG change of basis for every label pair up to cutoff."""

    if representation_cutoff < 0:
        raise ValueError("the representation cutoff must be nonnegative")
    coupled_vectors = 0
    product_vectors = 0
    orthonormality_entries = 0
    completeness_entries = 0
    nonzero_orthonormality = 0
    nonzero_completeness = 0
    for left in range(representation_cutoff + 1):
        for right in range(representation_cutoff + 1):
            product_indices = tuple(
                product(magnetic_indices(left), magnetic_indices(right))
            )
            coupled_indices = tuple(
                (output, output_magnetic)
                for output in fusion_labels(left, right)
                for output_magnetic in magnetic_indices(output)
            )
            product_vectors += len(product_indices)
            coupled_vectors += len(coupled_indices)
            rows = {
                coupled: tuple(
                    clebsch_gordan_doubled(
                        left,
                        left_magnetic,
                        right,
                        right_magnetic,
                        coupled[0],
                        coupled[1],
                    )
                    for left_magnetic, right_magnetic in product_indices
                )
                for coupled in coupled_indices
            }
            for first in coupled_indices:
                for second in coupled_indices:
                    residual = _inner_product(rows[first], rows[second]) - (
                        RadicalSum.rational(int(first == second))
                    )
                    orthonormality_entries += 1
                    nonzero_orthonormality += int(not residual.is_zero())
            columns = tuple(
                tuple(rows[coupled][index] for coupled in coupled_indices)
                for index in range(len(product_indices))
            )
            for first_index, first_column in enumerate(columns):
                for second_index, second_column in enumerate(columns):
                    residual = _inner_product(first_column, second_column) - (
                        RadicalSum.rational(int(first_index == second_index))
                    )
                    completeness_entries += 1
                    nonzero_completeness += int(not residual.is_zero())
    audit = ClebschGordanBasisAudit(
        representation_cutoff=representation_cutoff,
        ordered_representation_pairs=(representation_cutoff + 1) ** 2,
        coupled_basis_vectors=coupled_vectors,
        product_basis_vectors=product_vectors,
        orthonormality_entries_checked=orthonormality_entries,
        completeness_entries_checked=completeness_entries,
        nonzero_orthonormality_residuals=nonzero_orthonormality,
        nonzero_completeness_residuals=nonzero_completeness,
    )
    if not audit.validates():
        raise AssertionError("the exact Clebsch--Gordan basis audit failed")
    return audit


@dataclass(frozen=True)
class TransverseMagneticTensorPacket:
    """All local open-index tensors attached to one finite-cutoff carrier."""

    representation_cutoff: int
    carrier: FiniteCutoffTransverseRecouplingCarrier
    internal_tensors: tuple[TrivalentMagneticTensor, ...]
    boundary_tensors: tuple[BoundaryMagneticTensor, ...]
    nonzero_internal_components: int
    nonzero_boundary_components: int
    clebsch_gordan_basis_audit: ClebschGordanBasisAudit
    trivalent_invariance_audit: TrivalentInvarianceAudit
    arbitrary_label_factorial_formula_exposed: bool
    fixed_condon_shortley_phase: bool
    every_local_tensor_exact: bool
    global_tensor_network_contracted: bool
    global_f_r_transport_evaluated: bool
    carrier_amplitude_cutoff_modulus_proved: bool
    cp_order_domination_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        return (
            self.representation_cutoff == self.carrier.representation_cutoff
            and self.carrier.validates()
            and len(self.internal_tensors)
            == sum(len(basis.channels) for basis in self.carrier.internal_bases)
            and len(self.boundary_tensors)
            == sum(len(basis.channels) for basis in self.carrier.boundary_bases)
            and all(tensor.validates() for tensor in self.internal_tensors)
            and all(tensor.validates() for tensor in self.boundary_tensors)
            and self.nonzero_internal_components
            == sum(len(tensor.components) for tensor in self.internal_tensors)
            and self.nonzero_boundary_components
            == sum(len(tensor.components) for tensor in self.boundary_tensors)
            and self.clebsch_gordan_basis_audit.validates()
            and self.trivalent_invariance_audit.validates()
            and self.arbitrary_label_factorial_formula_exposed
            and self.fixed_condon_shortley_phase
            and self.every_local_tensor_exact
            and not self.global_tensor_network_contracted
            and not self.global_f_r_transport_evaluated
            and not self.carrier_amplitude_cutoff_modulus_proved
            and not self.cp_order_domination_proved
            and self.first_open_obligation
            == "contract-open-magnetic-tensors-through-global-f-r-transport"
        )


@cache
def transverse_magnetic_tensor_packet(
    representation_cutoff: int,
) -> TransverseMagneticTensorPacket:
    """Materialize every local magnetic tensor of the transverse carrier."""

    carrier = finite_cutoff_transverse_recoupling_carrier(
        representation_cutoff
    )
    internal_tensors = tuple(
        trivalent_magnetic_tensor(basis.link, basis.legs, channel)
        for basis in carrier.internal_bases
        for channel in basis.channels
    )
    boundary_tensors = tuple(
        boundary_magnetic_tensor(basis.link, basis.legs, channel)
        for basis in carrier.boundary_bases
        for channel in basis.channels
    )
    packet = TransverseMagneticTensorPacket(
        representation_cutoff=representation_cutoff,
        carrier=carrier,
        internal_tensors=internal_tensors,
        boundary_tensors=boundary_tensors,
        nonzero_internal_components=sum(
            len(tensor.components) for tensor in internal_tensors
        ),
        nonzero_boundary_components=sum(
            len(tensor.components) for tensor in boundary_tensors
        ),
        clebsch_gordan_basis_audit=clebsch_gordan_basis_audit(
            representation_cutoff
        ),
        trivalent_invariance_audit=trivalent_invariance_audit(
            representation_cutoff
        ),
        arbitrary_label_factorial_formula_exposed=True,
        fixed_condon_shortley_phase=True,
        every_local_tensor_exact=True,
        global_tensor_network_contracted=False,
        global_f_r_transport_evaluated=False,
        carrier_amplitude_cutoff_modulus_proved=False,
        cp_order_domination_proved=False,
        first_open_obligation=(
            "contract-open-magnetic-tensors-through-global-f-r-transport"
        ),
    )
    if not packet.validates():
        raise AssertionError("the transverse magnetic tensor packet drifted")
    return packet
