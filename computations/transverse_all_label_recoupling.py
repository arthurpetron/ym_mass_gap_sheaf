"""Finite-cutoff all-label recoupling carrier for the BF4 transverse core.

The connected 15-face transverse residual has five unprotected trivalent
Haar links and nine corridor-protected bivalent links.  For arbitrary
doubled-spin face labels, not just labels zero and one, its complete local
SU(2) recoupling data are:

* the unique invariant basis vector at every admissible internal trivalent
  triple; and
* every Clebsch--Gordan output at every protected bivalent link.

This module records those bases with the oriented, canonically ordered face
legs attached.  It also contracts the resulting finite factor graph exactly,
without flattening it into a potentially enormous boundary-profile table.
The contraction counts both internally admissible face assignments and
complete boundary-channel paths.

The cutoff is on face labels only.  Boundary outputs are deliberately *not*
truncated: two cutoff-``N`` faces may fuse up to label ``2N``.  Carriers at
successive cutoffs therefore embed exactly by inclusion of local basis
records.

This is an abstract orthonormal fusion-basis carrier.  It does not evaluate
magnetic-index Clebsch--Gordan coefficients, global F/R transport, Haar
tensor amplitudes above cutoff one, a summable cutoff modulus, or CP-order
corridor domination.  Those analytic/operator claims remain fail-closed.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import cache
from itertools import product
from typing import cast

from computations.exact_haar_network import (
    casimir4,
    dimension,
    fusion_labels,
    invariant_multiplicity,
)
from computations.transverse_cutoff_one_loop_tensor import (
    CONNECTED_CORE_FACE_IDS,
    cutoff_one_core_geometry,
)


@dataclass(frozen=True, order=True)
class OrientedCoreLeg:
    """One oriented face incidence in the pinned core ordering."""

    face_position: int
    face_id: int
    orientation: int

    def validates(self) -> bool:
        return (
            0 <= self.face_position < len(CONNECTED_CORE_FACE_IDS)
            and self.face_id == CONNECTED_CORE_FACE_IDS[self.face_position]
            and self.orientation in (-1, 1)
        )


@dataclass(frozen=True, order=True)
class FaceRepresentation:
    """Exact representation metadata for one allowed doubled-spin label."""

    label: int
    dimension: int
    casimir4: int

    def validates(self) -> bool:
        return (
            self.label >= 0
            and self.dimension == dimension(self.label)
            and self.casimir4 == casimir4(self.label)
        )


@dataclass(frozen=True, order=True)
class TrivalentInvariantChannel:
    """The canonical basis record for one admissible invariant triple."""

    leg_labels: tuple[int, int, int]
    basis_index: int
    invariant_dimension: int
    phase_convention: str

    def validates(self) -> bool:
        return (
            all(label >= 0 for label in self.leg_labels)
            and self.basis_index == 0
            and self.invariant_dimension
            == invariant_multiplicity(self.leg_labels)
            == 1
            and self.phase_convention == "condon-shortley"
        )


@dataclass(frozen=True, order=True)
class BoundaryFusionChannel:
    """One complete bivalent Clebsch--Gordan output channel."""

    leg_labels: tuple[int, int]
    output_label: int
    basis_index: int
    multiplicity: int
    phase_convention: str

    def validates(self) -> bool:
        left, right = self.leg_labels
        return (
            left >= 0
            and right >= 0
            and self.output_label in fusion_labels(left, right)
            and self.basis_index == 0
            and self.multiplicity == 1
            and self.phase_convention == "condon-shortley"
        )


@dataclass(frozen=True)
class InternalIntertwinerBasis:
    """Complete local invariant basis at one unprotected Haar link."""

    link: int
    legs: tuple[OrientedCoreLeg, OrientedCoreLeg, OrientedCoreLeg]
    channels: tuple[TrivalentInvariantChannel, ...]

    def validates(self, cutoff: int) -> bool:
        expected = tuple(
            TrivalentInvariantChannel(
                (first, second, third),
                0,
                1,
                "condon-shortley",
            )
            for first in range(cutoff + 1)
            for second in range(cutoff + 1)
            for third in range(cutoff + 1)
            if invariant_multiplicity((first, second, third)) == 1
        )
        return (
            len(self.legs) == 3
            and all(leg.validates() for leg in self.legs)
            and tuple(sorted(self.legs)) == self.legs
            and self.channels == expected
            and all(channel.validates() for channel in self.channels)
        )


@dataclass(frozen=True)
class ProtectedBoundaryFusionBasis:
    """Complete local output basis at one corridor-protected link."""

    link: int
    legs: tuple[OrientedCoreLeg, OrientedCoreLeg]
    channels: tuple[BoundaryFusionChannel, ...]

    def validates(self, cutoff: int) -> bool:
        expected = tuple(
            BoundaryFusionChannel(
                (left, right),
                output,
                0,
                1,
                "condon-shortley",
            )
            for left in range(cutoff + 1)
            for right in range(cutoff + 1)
            for output in fusion_labels(left, right)
        )
        return (
            len(self.legs) == 2
            and all(leg.validates() for leg in self.legs)
            and tuple(sorted(self.legs)) == self.legs
            and self.channels == expected
            and all(channel.validates() for channel in self.channels)
        )


@dataclass(frozen=True)
class FiniteCutoffTransverseRecouplingCarrier:
    """Nested exact local fusion bases for one face-label cutoff."""

    representation_cutoff: int
    face_ids: tuple[int, ...]
    representations: tuple[FaceRepresentation, ...]
    internal_bases: tuple[InternalIntertwinerBasis, ...]
    boundary_bases: tuple[ProtectedBoundaryFusionBasis, ...]
    fixed_oriented_leg_order: bool
    complete_internal_invariant_bases: bool
    complete_boundary_output_bases: bool
    boundary_outputs_untruncated: bool
    magnetic_index_coefficients_evaluated: bool
    global_f_r_transport_evaluated: bool

    def validates(self) -> bool:
        geometry = cutoff_one_core_geometry()
        expected_internal_links = tuple(link for link, _ in geometry.internal_incidence)
        return (
            self.representation_cutoff >= 0
            and self.face_ids == CONNECTED_CORE_FACE_IDS
            and self.representations
            == tuple(
                FaceRepresentation(label, dimension(label), casimir4(label))
                for label in range(self.representation_cutoff + 1)
            )
            and all(item.validates() for item in self.representations)
            and tuple(basis.link for basis in self.internal_bases)
            == expected_internal_links
            and tuple(basis.link for basis in self.boundary_bases)
            == geometry.protected_links
            and all(
                basis.validates(self.representation_cutoff)
                for basis in self.internal_bases
            )
            and all(
                basis.validates(self.representation_cutoff)
                for basis in self.boundary_bases
            )
            and self.fixed_oriented_leg_order
            and self.complete_internal_invariant_bases
            and self.complete_boundary_output_bases
            and self.boundary_outputs_untruncated
            and not self.magnetic_index_coefficients_evaluated
            and not self.global_f_r_transport_evaluated
        )

    def embeds_into(
        self,
        larger: FiniteCutoffTransverseRecouplingCarrier,
    ) -> bool:
        """Check the literal local-basis inclusion into a larger cutoff."""

        if (
            not self.validates()
            or not larger.validates()
            or self.representation_cutoff > larger.representation_cutoff
            or self.face_ids != larger.face_ids
        ):
            return False
        return (
            set(self.representations) <= set(larger.representations)
            and all(
                small.link == big.link
                and small.legs == big.legs
                and set(small.channels) <= set(big.channels)
                for small, big in zip(
                    self.internal_bases,
                    larger.internal_bases,
                    strict=True,
                )
            )
            and all(
                small.link == big.link
                and small.legs == big.legs
                and set(small.channels) <= set(big.channels)
                for small, big in zip(
                    self.boundary_bases,
                    larger.boundary_bases,
                    strict=True,
                )
            )
        )


def _leg(face_position: int, orientation: int) -> OrientedCoreLeg:
    return OrientedCoreLeg(
        face_position,
        CONNECTED_CORE_FACE_IDS[face_position],
        orientation,
    )


@cache
def finite_cutoff_transverse_recoupling_carrier(
    representation_cutoff: int,
) -> FiniteCutoffTransverseRecouplingCarrier:
    """Construct the complete abstract local recoupling bases."""

    if representation_cutoff < 0:
        raise ValueError("the representation cutoff must be nonnegative")
    geometry = cutoff_one_core_geometry()
    internal_bases = tuple(
        InternalIntertwinerBasis(
            link=link,
            legs=cast(
                tuple[OrientedCoreLeg, OrientedCoreLeg, OrientedCoreLeg],
                tuple(
                    sorted(
                        _leg(position, orientation)
                        for position, orientation in incident
                    )
                ),
            ),
            channels=tuple(
                TrivalentInvariantChannel(
                    (first, second, third),
                    0,
                    1,
                    "condon-shortley",
                )
                for first in range(representation_cutoff + 1)
                for second in range(representation_cutoff + 1)
                for third in range(representation_cutoff + 1)
                if invariant_multiplicity((first, second, third)) == 1
            ),
        )
        for link, incident in geometry.internal_incidence
    )
    boundary_bases = tuple(
        ProtectedBoundaryFusionBasis(
            link=link,
            legs=cast(
                tuple[OrientedCoreLeg, OrientedCoreLeg],
                tuple(
                    sorted(
                        _leg(position, orientation)
                        for position, word in enumerate(geometry.face_words)
                        for word_link, orientation in word
                        if word_link == link
                    )
                )
            ),
            channels=tuple(
                BoundaryFusionChannel(
                    (left, right),
                    output,
                    0,
                    1,
                    "condon-shortley",
                )
                for left in range(representation_cutoff + 1)
                for right in range(representation_cutoff + 1)
                for output in fusion_labels(left, right)
            ),
        )
        for link in geometry.protected_links
    )
    carrier = FiniteCutoffTransverseRecouplingCarrier(
        representation_cutoff=representation_cutoff,
        face_ids=CONNECTED_CORE_FACE_IDS,
        representations=tuple(
            FaceRepresentation(label, dimension(label), casimir4(label))
            for label in range(representation_cutoff + 1)
        ),
        internal_bases=internal_bases,
        boundary_bases=boundary_bases,
        fixed_oriented_leg_order=True,
        complete_internal_invariant_bases=True,
        complete_boundary_output_bases=True,
        boundary_outputs_untruncated=True,
        magnetic_index_coefficients_evaluated=False,
        global_f_r_transport_evaluated=False,
    )
    if not carrier.validates():
        raise AssertionError("the transverse all-label recoupling carrier drifted")
    return carrier


@dataclass(frozen=True)
class _IntegerFactor:
    """Sparse nonnegative-integer factor used by exact variable elimination."""

    variables: tuple[int, ...]
    values: dict[tuple[int, ...], int]

    def value(self, assignment: dict[int, int]) -> int:
        return self.values.get(
            tuple(assignment[variable] for variable in self.variables),
            0,
        )


def _unary_unit_factor(variable: int, cutoff: int) -> _IntegerFactor:
    return _IntegerFactor(
        (variable,),
        {(label,): 1 for label in range(cutoff + 1)},
    )


def _internal_factor(
    positions: tuple[int, int, int],
    cutoff: int,
) -> _IntegerFactor:
    return _IntegerFactor(
        positions,
        {
            labels: invariant_multiplicity(labels)
            for labels in product(range(cutoff + 1), repeat=3)
            if invariant_multiplicity(labels)
        },
    )


def _boundary_path_factor(
    positions: tuple[int, int],
    cutoff: int,
) -> _IntegerFactor:
    return _IntegerFactor(
        positions,
        {
            labels: len(fusion_labels(*labels))
            for labels in product(range(cutoff + 1), repeat=2)
        },
    )


def _eliminate_integer_factors(
    factors: tuple[_IntegerFactor, ...],
    cutoff: int,
) -> int:
    """Contract a small exact factor graph by deterministic min-scope order."""

    remaining = set(range(len(CONNECTED_CORE_FACE_IDS)))
    active = list(factors)
    while remaining:
        choices: list[tuple[int, int, tuple[int, ...]]] = []
        for variable in remaining:
            incident = tuple(factor for factor in active if variable in factor.variables)
            union = tuple(
                sorted(
                    {
                        item
                        for factor in incident
                        for item in factor.variables
                    }
                )
            )
            choices.append((len(union), variable, union))
        _scope_size, selected, union = min(choices)
        incident = tuple(factor for factor in active if selected in factor.variables)
        active = [factor for factor in active if selected not in factor.variables]
        following_variables = tuple(variable for variable in union if variable != selected)
        following_values: dict[tuple[int, ...], int] = {}
        for labels in product(range(cutoff + 1), repeat=len(union)):
            assignment = dict(zip(union, labels, strict=True))
            value = 1
            for factor in incident:
                value *= factor.value(assignment)
                if value == 0:
                    break
            if value:
                following_key = tuple(
                    assignment[variable] for variable in following_variables
                )
                following_values[following_key] = (
                    following_values.get(following_key, 0) + value
                )
        active.append(_IntegerFactor(following_variables, following_values))
        remaining.remove(selected)
    result = 1
    for factor in active:
        if factor.variables:
            raise AssertionError("variable elimination left a non-scalar factor")
        result *= factor.values.get((), 0)
    return result


def _incidence_positions() -> tuple[
    tuple[tuple[int, int, int], ...],
    tuple[tuple[int, int], ...],
]:
    geometry = cutoff_one_core_geometry()
    internal = cast(
        tuple[tuple[int, int, int], ...],
        tuple(
            tuple(position for position, _orientation in incident)
            for _link, incident in geometry.internal_incidence
        ),
    )
    boundary = cast(
        tuple[tuple[int, int], ...],
        tuple(
            tuple(
                position
                for position, word in enumerate(geometry.face_words)
                if any(word_link == link for word_link, _orientation in word)
            )
            for link in geometry.protected_links
        ),
    )
    if any(len(positions) != 3 for positions in internal):
        raise AssertionError("the all-label internal core ceased to be trivalent")
    if any(len(positions) != 2 for positions in boundary):
        raise AssertionError("the all-label protected boundary ceased to be bivalent")
    return internal, boundary


@dataclass(frozen=True)
class TransverseRecouplingCensus:
    """Exact finite-cutoff size audit without flattening boundary profiles."""

    representation_cutoff: int
    face_count: int
    internal_link_count: int
    protected_boundary_link_count: int
    local_internal_channels_per_link: int
    local_boundary_channels_per_link: int
    maximum_boundary_output_label: int
    internally_admissible_face_assignments: int
    complete_boundary_channel_paths: int
    nested_with_previous_cutoff: bool
    compact_factor_graph_used: bool
    flat_boundary_profile_ledger_materialized: bool
    finite_cutoff_basis_inclusion_proved: bool
    carrier_amplitude_cutoff_modulus_proved: bool
    coherent_all_label_haar_amplitudes_evaluated: bool
    global_f_r_transport_evaluated: bool
    cp_order_domination_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        carrier = finite_cutoff_transverse_recoupling_carrier(
            self.representation_cutoff
        )
        assignment_count, path_count = _global_counts(
            self.representation_cutoff
        )
        prior_nested = (
            True
            if self.representation_cutoff == 0
            else finite_cutoff_transverse_recoupling_carrier(
                self.representation_cutoff - 1
            ).embeds_into(carrier)
        )
        return (
            carrier.validates()
            and self.face_count == 15
            and self.internal_link_count == len(carrier.internal_bases) == 5
            and self.protected_boundary_link_count
            == len(carrier.boundary_bases)
            == 9
            and self.local_internal_channels_per_link
            == len(carrier.internal_bases[0].channels)
            and all(
                len(basis.channels) == self.local_internal_channels_per_link
                for basis in carrier.internal_bases
            )
            and self.local_boundary_channels_per_link
            == len(carrier.boundary_bases[0].channels)
            and all(
                len(basis.channels) == self.local_boundary_channels_per_link
                for basis in carrier.boundary_bases
            )
            and self.maximum_boundary_output_label
            == 2 * self.representation_cutoff
            and self.internally_admissible_face_assignments == assignment_count
            and self.complete_boundary_channel_paths == path_count
            and self.nested_with_previous_cutoff == prior_nested
            and self.compact_factor_graph_used
            and not self.flat_boundary_profile_ledger_materialized
            and self.finite_cutoff_basis_inclusion_proved
            and not self.carrier_amplitude_cutoff_modulus_proved
            and not self.coherent_all_label_haar_amplitudes_evaluated
            and not self.global_f_r_transport_evaluated
            and not self.cp_order_domination_proved
            and self.first_open_obligation
            == "evaluate-all-label-haar-amplitudes-in-the-recoupling-basis"
        )


@cache
def _global_counts(representation_cutoff: int) -> tuple[int, int]:
    if representation_cutoff < 0:
        raise ValueError("the representation cutoff must be nonnegative")
    internal, boundary = _incidence_positions()
    unit_factors = tuple(
        _unary_unit_factor(position, representation_cutoff)
        for position in range(len(CONNECTED_CORE_FACE_IDS))
    )
    internal_factors = tuple(
        _internal_factor(positions, representation_cutoff)
        for positions in internal
    )
    assignment_count = _eliminate_integer_factors(
        unit_factors + internal_factors,
        representation_cutoff,
    )
    path_count = _eliminate_integer_factors(
        unit_factors
        + internal_factors
        + tuple(
            _boundary_path_factor(positions, representation_cutoff)
            for positions in boundary
        ),
        representation_cutoff,
    )
    return assignment_count, path_count


@cache
def transverse_recoupling_census(
    representation_cutoff: int,
) -> TransverseRecouplingCensus:
    """Build and contract the exact finite-cutoff recoupling carrier."""

    carrier = finite_cutoff_transverse_recoupling_carrier(
        representation_cutoff
    )
    assignment_count, path_count = _global_counts(representation_cutoff)
    previous_nested = (
        True
        if representation_cutoff == 0
        else finite_cutoff_transverse_recoupling_carrier(
            representation_cutoff - 1
        ).embeds_into(carrier)
    )
    census = TransverseRecouplingCensus(
        representation_cutoff=representation_cutoff,
        face_count=len(carrier.face_ids),
        internal_link_count=len(carrier.internal_bases),
        protected_boundary_link_count=len(carrier.boundary_bases),
        local_internal_channels_per_link=len(
            carrier.internal_bases[0].channels
        ),
        local_boundary_channels_per_link=len(
            carrier.boundary_bases[0].channels
        ),
        maximum_boundary_output_label=2 * representation_cutoff,
        internally_admissible_face_assignments=assignment_count,
        complete_boundary_channel_paths=path_count,
        nested_with_previous_cutoff=previous_nested,
        compact_factor_graph_used=True,
        flat_boundary_profile_ledger_materialized=False,
        finite_cutoff_basis_inclusion_proved=True,
        carrier_amplitude_cutoff_modulus_proved=False,
        coherent_all_label_haar_amplitudes_evaluated=False,
        global_f_r_transport_evaluated=False,
        cp_order_domination_proved=False,
        first_open_obligation=(
            "evaluate-all-label-haar-amplitudes-in-the-recoupling-basis"
        ),
    )
    if not census.validates():
        raise AssertionError("the transverse recoupling census drifted")
    return census
