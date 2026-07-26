"""Exact finite-dimensional CP-order pilot for the BF4 transverse core.

The compact cutoff-one loop tensors are scalar functions of the nine
corridor-protected Haar variables.  They do not by themselves supply the
open magnetic/intertwiner indices of the physical corrected-slab Choi
operator.  This module extracts a rigorous finite shadow which can be
computed from those tensors without inventing the missing indices.

Let ``z = 2 s^3`` be the coefficient of the fundamental character in a
cutoff-one plaquette factor and let ``f_z`` be the transverse-core density
after the five internal Haar variables have been integrated.  Compress
multiplication by ``f_z`` to

    V = span(1, chi_1(U_1), ..., chi_1(U_9)),

where the nine ``U_i`` are the protected boundary variables.  This basis is
orthonormal for product Haar measure, so its exact moment matrix is

    G_ij(z) = integral f_z phi_i phi_j.

Associate to ``G`` the Schur multiplier ``S_G(A) = G .* A`` on ``M_10``.
The Schur-product theorem and the Choi criterion give the exact equivalence

    S_G - eta S_I is completely positive
      iff G - eta I is positive semidefinite.

This is a bounded cutoff-one pilot, not the physical BF4 map.  It is a
necessary finite Gram test for any scalar multiplication domination, and it
provides a precise screening obstruction when the cutoff-one character
truncation ceases even to define a positive multiplier.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias

from computations.exact_haar_network import (
    Poly,
    SPoly,
    chi,
    contract_pairing_aware,
    holonomy,
    scalar,
    sp_eval,
)
from computations.general_reflection_cut_carrier import exact_ldlt
from computations.transverse_cutoff_one_loop_tensor import (
    cutoff_one_core_geometry,
    fundamental_partial_loop_tensor,
)

RationalMatrix: TypeAlias = tuple[tuple[Fraction, ...], ...]
PolynomialMatrix: TypeAlias = tuple[tuple[SPoly, ...], ...]


def _add_polynomial_term(
    polynomial: SPoly,
    exponent: int,
    coefficient: Fraction,
) -> None:
    if coefficient:
        value = polynomial.get(exponent, Fraction(0)) + coefficient
        if value:
            polynomial[exponent] = value
        else:
            polynomial.pop(exponent, None)


@cache
def _core_character_factors() -> tuple[Poly, ...]:
    geometry = cutoff_one_core_geometry()
    return tuple(
        chi(1, geometry.complex.holonomy_of(path))
        for path in geometry.full_face_paths
    )


@cache
def _protected_character_factors() -> tuple[Poly, ...]:
    return tuple(
        chi(1, holonomy(((link, 1),)))
        for link in cutoff_one_core_geometry().protected_links
    )


@cache
def _admissible_masks_by_boundary_parity() -> (
    tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]
):
    """Group admissible masks by their nine protected-link parities."""

    geometry = cutoff_one_core_geometry()
    buckets: dict[tuple[int, ...], list[int]] = {}
    for face_mask in range(1 << len(geometry.face_words)):
        try:
            fundamental_partial_loop_tensor(face_mask)
        except ValueError:
            continue
        parity = tuple(
            sum(
                1
                for position, word in enumerate(geometry.face_words)
                if (face_mask >> position) & 1
                for word_link, _orientation in word
                if word_link == link
            )
            % 2
            for link in geometry.protected_links
        )
        buckets.setdefault(parity, []).append(face_mask)
    return tuple(
        (parity, tuple(masks))
        for parity, masks in sorted(buckets.items())
    )


def _masks_for_feature_pair(
    left_feature: int,
    right_feature: int,
) -> tuple[int, ...]:
    """Return masks not killed by protected-link parity.

    Feature zero is the vacuum.  Features one through nine are the
    fundamental characters of the corresponding protected Haar variable.
    """

    protected_count = len(cutoff_one_core_geometry().protected_links)
    if left_feature not in range(protected_count + 1):
        raise ValueError("left feature leaves the cutoff-one pilot basis")
    if right_feature not in range(protected_count + 1):
        raise ValueError("right feature leaves the cutoff-one pilot basis")
    parity = [0] * protected_count
    if left_feature:
        parity[left_feature - 1] ^= 1
    if right_feature:
        parity[right_feature - 1] ^= 1
    lookup = dict(_admissible_masks_by_boundary_parity())
    return lookup.get(tuple(parity), ())


@cache
def _closed_network_value(
    face_mask: int,
    left_feature: int,
    right_feature: int,
) -> Fraction:
    """Integrate one core filling against two pilot features exactly."""

    geometry = cutoff_one_core_geometry()
    tensor = fundamental_partial_loop_tensor(face_mask)
    factors = [
        factor
        for position, factor in enumerate(_core_character_factors())
        if (face_mask >> position) & 1
    ]
    if left_feature:
        factors.append(_protected_character_factors()[left_feature - 1])
    if right_feature:
        factors.append(_protected_character_factors()[right_feature - 1])
    contracted = contract_pairing_aware(
        factors,
        geometry.internal_links + geometry.protected_links,
    )
    value = scalar(contracted)
    if any(exponent != 0 for exponent in value):
        raise AssertionError("a character-only pilot acquired heat powers")
    result = Fraction(value.get(0, Fraction(0)))
    if tensor.active_face_count != face_mask.bit_count():
        raise AssertionError("the compact tensor and direct filling disagree")
    return result


@cache
def transverse_cutoff_one_moment_polynomial_matrix() -> PolynomialMatrix:
    """Return the exact ``10 x 10`` Gram matrix as polynomials in ``z``."""

    feature_count = len(cutoff_one_core_geometry().protected_links) + 1
    rows: list[tuple[SPoly, ...]] = []
    for left in range(feature_count):
        row: list[SPoly] = []
        for right in range(feature_count):
            polynomial: SPoly = {}
            for face_mask in _masks_for_feature_pair(left, right):
                _add_polynomial_term(
                    polynomial,
                    face_mask.bit_count(),
                    _closed_network_value(face_mask, left, right),
                )
            row.append(polynomial)
        rows.append(tuple(row))
    matrix = tuple(rows)
    if any(
        matrix[row][column] != matrix[column][row]
        for row in range(feature_count)
        for column in range(feature_count)
    ):
        raise AssertionError("the cutoff-one pilot Gram lost symmetry")
    return matrix


def evaluate_moment_matrix(z: Fraction) -> RationalMatrix:
    """Evaluate the transverse moment matrix at one rational activity."""

    if z < 0:
        raise ValueError("the fundamental activity must be nonnegative")
    return tuple(
        tuple(sp_eval(entry, z) for entry in row)
        for row in transverse_cutoff_one_moment_polynomial_matrix()
    )


def shifted_moment_matrix(
    z: Fraction,
    domination_mass: Fraction,
) -> RationalMatrix:
    """Return ``G(z) - domination_mass * I`` exactly."""

    matrix = evaluate_moment_matrix(z)
    return tuple(
        tuple(
            value - (domination_mass if row == column else Fraction(0))
            for column, value in enumerate(values)
        )
        for row, values in enumerate(matrix)
    )


@dataclass(frozen=True)
class CutoffOneCPOrderPilot:
    """Exact Choi/Schur certificate for one rational cutoff-one activity."""

    activity: Fraction
    domination_mass: Fraction
    feature_dimension: int
    moment_matrix: RationalMatrix
    shifted_matrix: RationalMatrix
    moment_pivots: tuple[Fraction, ...]
    shifted_pivots: tuple[Fraction, ...]
    cutoff_one_schur_map_cp: bool
    corridor_difference_cp: bool
    equivalent_by_schur_choi_criterion: bool
    physical_corrected_slab_choi_reconstructed: bool

    def validates(self) -> bool:
        moment_factor = exact_ldlt(self.moment_matrix)
        shifted_factor = exact_ldlt(self.shifted_matrix)
        return (
            self.activity >= 0
            and self.domination_mass >= 0
            and self.feature_dimension == 10
            and len(self.moment_matrix) == self.feature_dimension
            and all(
                len(row) == self.feature_dimension
                for row in self.moment_matrix
            )
            and self.shifted_matrix
            == shifted_moment_matrix(self.activity, self.domination_mass)
            and self.moment_pivots == moment_factor.diagonal
            and self.shifted_pivots == shifted_factor.diagonal
            and self.cutoff_one_schur_map_cp == moment_factor.is_psd
            and self.corridor_difference_cp == shifted_factor.is_psd
            and self.equivalent_by_schur_choi_criterion
            and not self.physical_corrected_slab_choi_reconstructed
        )


def cutoff_one_cp_order_pilot(
    activity: Fraction,
    domination_mass: Fraction,
) -> CutoffOneCPOrderPilot:
    """Construct one exact finite-dimensional CP-order pilot."""

    moment = evaluate_moment_matrix(activity)
    shifted = shifted_moment_matrix(activity, domination_mass)
    moment_factor = exact_ldlt(moment)
    shifted_factor = exact_ldlt(shifted)
    pilot = CutoffOneCPOrderPilot(
        activity=activity,
        domination_mass=domination_mass,
        feature_dimension=len(moment),
        moment_matrix=moment,
        shifted_matrix=shifted,
        moment_pivots=moment_factor.diagonal,
        shifted_pivots=shifted_factor.diagonal,
        cutoff_one_schur_map_cp=moment_factor.is_psd,
        corridor_difference_cp=shifted_factor.is_psd,
        equivalent_by_schur_choi_criterion=True,
        physical_corrected_slab_choi_reconstructed=False,
    )
    if not pilot.validates():
        raise AssertionError("the cutoff-one CP-order pilot drifted")
    return pilot


def _quadratic_form(
    matrix: RationalMatrix,
    vector: tuple[Fraction, ...],
) -> Fraction:
    if len(matrix) != len(vector):
        raise ValueError("the pilot vector has the wrong dimension")
    return sum(
        (
            vector[row] * matrix[row][column] * vector[column]
            for row in range(len(vector))
            for column in range(len(vector))
        ),
        start=Fraction(0),
    )


@dataclass(frozen=True)
class CutoffOneCPOrderAudit:
    """Pinned positive pilot and weak-coupling truncation obstruction."""

    protected_links: tuple[int, ...]
    feature_dimension: int
    nonzero_polynomial_entries: int
    distinct_polynomial_entries: int
    activity_exponents: tuple[int, ...]
    strong_activity: Fraction
    certified_strong_domination_mass: Fraction
    strong_pilot: CutoffOneCPOrderPilot
    weak_activity: Fraction
    weak_pilot: CutoffOneCPOrderPilot
    weak_obstruction_features: tuple[int, int]
    weak_obstruction_vector: tuple[Fraction, ...]
    weak_obstruction_quadratic_form: Fraction
    weak_obstruction_principal_block: RationalMatrix
    weak_obstruction_principal_determinant: Fraction
    finite_schur_cp_equivalence_proved: bool
    finite_compression_sufficient_for_physical_cp_order: bool
    all_label_completion_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        polynomial_matrix = transverse_cutoff_one_moment_polynomial_matrix()
        weak_matrix = self.weak_pilot.moment_matrix
        left, right = self.weak_obstruction_features
        principal = (
            (weak_matrix[left][left], weak_matrix[left][right]),
            (weak_matrix[right][left], weak_matrix[right][right]),
        )
        determinant = (
            principal[0][0] * principal[1][1]
            - principal[0][1] * principal[1][0]
        )
        return (
            self.protected_links
            == cutoff_one_core_geometry().protected_links
            == (7, 8, 11, 12, 19, 23, 25, 53, 54)
            and self.feature_dimension == 10
            and self.nonzero_polynomial_entries
            == sum(
                bool(entry)
                for row in polynomial_matrix
                for entry in row
            )
            == 28
            and self.distinct_polynomial_entries
            == len(
                {
                    tuple(sorted(entry.items()))
                    for row in polynomial_matrix
                    for entry in row
                }
            )
            == 7
            and self.activity_exponents
            == tuple(
                sorted(
                    {
                        exponent
                        for row in polynomial_matrix
                        for entry in row
                        for exponent in entry
                    }
                )
            )
            == (0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12)
            and self.strong_activity == Fraction(1, 2)
            and self.certified_strong_domination_mass == Fraction(1, 3)
            and self.strong_pilot
            == cutoff_one_cp_order_pilot(
                self.strong_activity,
                self.certified_strong_domination_mass,
            )
            and self.strong_pilot.cutoff_one_schur_map_cp
            and self.strong_pilot.corridor_difference_cp
            and self.weak_activity == Fraction(3, 2)
            and self.weak_pilot
            == cutoff_one_cp_order_pilot(self.weak_activity, Fraction(0))
            and not self.weak_pilot.cutoff_one_schur_map_cp
            and not self.weak_pilot.corridor_difference_cp
            and self.weak_obstruction_features == (8, 9)
            and self.weak_obstruction_vector
            == (Fraction(0),) * 8 + (Fraction(1), Fraction(-1))
            and self.weak_obstruction_quadratic_form
            == _quadratic_form(weak_matrix, self.weak_obstruction_vector)
            == Fraction(-2738971, 1048576)
            and self.weak_obstruction_principal_block
            == principal
            == (
                (
                    Fraction(10962521, 2097152),
                    Fraction(3425373, 524288),
                ),
                (
                    Fraction(3425373, 524288),
                    Fraction(10962521, 2097152),
                ),
            )
            and self.weak_obstruction_principal_determinant
            == determinant
            == Fraction(-67554016350623, 4398046511104)
            and self.finite_schur_cp_equivalence_proved
            and not self.finite_compression_sufficient_for_physical_cp_order
            and not self.all_label_completion_proved
            and self.first_open_obligation
            == "reconstruct-open-index-all-label-choi-and-prove-cp-domination"
        )


@cache
def cutoff_one_cp_order_audit() -> CutoffOneCPOrderAudit:
    """Return the exact positive pilot and exact weak-coupling obstruction."""

    polynomial_matrix = transverse_cutoff_one_moment_polynomial_matrix()
    weak = cutoff_one_cp_order_pilot(Fraction(3, 2), Fraction(0))
    weak_vector = (Fraction(0),) * 8 + (Fraction(1), Fraction(-1))
    weak_block = (
        (weak.moment_matrix[8][8], weak.moment_matrix[8][9]),
        (weak.moment_matrix[9][8], weak.moment_matrix[9][9]),
    )
    audit = CutoffOneCPOrderAudit(
        protected_links=cutoff_one_core_geometry().protected_links,
        feature_dimension=10,
        nonzero_polynomial_entries=sum(
            bool(entry)
            for row in polynomial_matrix
            for entry in row
        ),
        distinct_polynomial_entries=len(
            {
                tuple(sorted(entry.items()))
                for row in polynomial_matrix
                for entry in row
            }
        ),
        activity_exponents=tuple(
            sorted(
                {
                    exponent
                    for row in polynomial_matrix
                    for entry in row
                    for exponent in entry
                }
            )
        ),
        strong_activity=Fraction(1, 2),
        certified_strong_domination_mass=Fraction(1, 3),
        strong_pilot=cutoff_one_cp_order_pilot(
            Fraction(1, 2),
            Fraction(1, 3),
        ),
        weak_activity=Fraction(3, 2),
        weak_pilot=weak,
        weak_obstruction_features=(8, 9),
        weak_obstruction_vector=weak_vector,
        weak_obstruction_quadratic_form=_quadratic_form(
            weak.moment_matrix,
            weak_vector,
        ),
        weak_obstruction_principal_block=weak_block,
        weak_obstruction_principal_determinant=(
            weak_block[0][0] * weak_block[1][1]
            - weak_block[0][1] * weak_block[1][0]
        ),
        finite_schur_cp_equivalence_proved=True,
        finite_compression_sufficient_for_physical_cp_order=False,
        all_label_completion_proved=False,
        first_open_obligation=(
            "reconstruct-open-index-all-label-choi-and-prove-cp-domination"
        ),
    )
    if not audit.validates():
        raise AssertionError("the cutoff-one CP-order audit drifted")
    return audit
