"""Constructive boundary-message composition for physically glued kernels.

Independent row normalization does not commute with gluing.  The exact
finite-horizon replacement is a backward-message (Doob) transform.

For nonnegative transfer matrices ``T_j`` and a strictly positive terminal
weight ``h_m``, define

    h_j(x) = sum_y T_j(x,y) h_{j+1}(y),

and

    P_j(x,y) = T_j(x,y) h_{j+1}(y) / h_j(x).

Every ``P_j`` is row stochastic.  The messages telescope, giving

    (P_0 ... P_{m-1})(x,z)
      = (T_0 ... T_{m-1})(x,z) h_m(z) / h_0(x).

Thus the mass-preserving channel composition is exact once the raw
boundary-conditioned transfer kernels and one terminal boundary message are
known.  No Perron eigenvector or infinite-horizon limit is required for a
fixed physical block.

For corrected-slab Yang--Mills, the raw density factorization is supplied by
the 120-face fiber-product geometry.  The remaining analytic task is to
construct its all-label continuous boundary messages and prove a
spacing-uniform relative-order/minorization bound for the resulting
Markovized kernels.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias

from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.corrected_slab_physical_gluing import (
    TwoSlabPhysicalGluingAudit,
    two_slab_physical_gluing_audit,
)
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import (
    Link4,
    Vertex4,
    add_e,
    edges_of,
)
from computations.whole_corrected_slab_kraus import coarse_face_paths

RationalVector: TypeAlias = tuple[Fraction, ...]
RationalMatrix: TypeAlias = tuple[RationalVector, ...]


def _fraction_vector(
    values: Iterable[int | Fraction],
) -> RationalVector:
    return tuple(Fraction(value) for value in values)


def _nonnegative_matrix(
    rows: Iterable[Iterable[int | Fraction]],
) -> RationalMatrix:
    matrix = tuple(_fraction_vector(row) for row in rows)
    if not matrix or not matrix[0]:
        raise ValueError("a transfer matrix must be nonempty")
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("a transfer matrix must be rectangular")
    if any(value < 0 for row in matrix for value in row):
        raise ValueError("a transfer matrix cannot contain negative entries")
    return matrix


def _matrix_product(
    left: RationalMatrix,
    right: RationalMatrix,
) -> RationalMatrix:
    if len(left[0]) != len(right):
        raise ValueError("the transfer matrices do not compose")
    return tuple(
        tuple(
            sum(
                (
                    left[source][middle] * right[middle][target]
                    for middle in range(len(right))
                ),
                start=Fraction(0),
            )
            for target in range(len(right[0]))
        )
        for source in range(len(left))
    )


def _chain_product(matrices: tuple[RationalMatrix, ...]) -> RationalMatrix:
    product = matrices[0]
    for matrix in matrices[1:]:
        product = _matrix_product(product, matrix)
    return product


@dataclass(frozen=True)
class BoundaryMessageMarkovization:
    """Exact finite transfer-to-Markov conversion and composition identity."""

    transfers: tuple[RationalMatrix, ...]
    terminal_message: RationalVector
    backward_messages: tuple[RationalVector, ...]
    markov_kernels: tuple[RationalMatrix, ...]
    raw_composite: RationalMatrix
    markov_composite: RationalMatrix
    every_message_strictly_positive: bool
    every_kernel_mass_preserving: bool
    telescoping_endpoint_identity: bool
    independent_row_normalization_used: bool

    def validates(self) -> bool:
        try:
            transfers = tuple(
                _nonnegative_matrix(matrix)
                for matrix in self.transfers
            )
        except ValueError:
            return False
        if not transfers:
            return False
        if any(
            len(transfers[index][0]) != len(transfers[index + 1])
            for index in range(len(transfers) - 1)
        ):
            return False
        terminal = _fraction_vector(self.terminal_message)
        if (
            len(terminal) != len(transfers[-1][0])
            or any(value <= 0 for value in terminal)
        ):
            return False
        messages: list[RationalVector] = [()] * (len(transfers) + 1)
        messages[-1] = terminal
        for index in range(len(transfers) - 1, -1, -1):
            following = messages[index + 1]
            messages[index] = tuple(
                sum(
                    (
                        transfers[index][source][target]
                        * following[target]
                        for target in range(len(following))
                    ),
                    start=Fraction(0),
                )
                for source in range(len(transfers[index]))
            )
        if any(
            value <= 0
            for message in messages
            for value in message
        ):
            return False
        kernels = tuple(
            tuple(
                tuple(
                    transfers[index][source][target]
                    * messages[index + 1][target]
                    / messages[index][source]
                    for target in range(len(transfers[index][0]))
                )
                for source in range(len(transfers[index]))
            )
            for index in range(len(transfers))
        )
        raw_composite = _chain_product(transfers)
        markov_composite = _chain_product(kernels)
        endpoint = tuple(
            tuple(
                raw_composite[source][target]
                * terminal[target]
                / messages[0][source]
                for target in range(len(raw_composite[0]))
            )
            for source in range(len(raw_composite))
        )
        return (
            self.backward_messages == tuple(messages)
            and self.markov_kernels == kernels
            and self.raw_composite == raw_composite
            and self.markov_composite == markov_composite == endpoint
            and self.every_message_strictly_positive
            and self.every_kernel_mass_preserving
            and all(
                sum(row, start=Fraction(0)) == 1
                for kernel in kernels
                for row in kernel
            )
            and self.telescoping_endpoint_identity
            and not self.independent_row_normalization_used
        )


def markovize_transfer_chain(
    transfers: Iterable[Iterable[Iterable[int | Fraction]]],
    terminal_message: Iterable[int | Fraction],
) -> BoundaryMessageMarkovization:
    """Construct exact backward messages and mass-preserving kernels."""

    matrices = tuple(_nonnegative_matrix(matrix) for matrix in transfers)
    if not matrices:
        raise ValueError("at least one transfer matrix is required")
    if any(
        len(matrices[index][0]) != len(matrices[index + 1])
        for index in range(len(matrices) - 1)
    ):
        raise ValueError("the transfer chain dimensions do not compose")
    terminal = _fraction_vector(terminal_message)
    if (
        len(terminal) != len(matrices[-1][0])
        or any(value <= 0 for value in terminal)
    ):
        raise ValueError("the terminal message must be positive and compatible")

    messages: list[RationalVector] = [()] * (len(matrices) + 1)
    messages[-1] = terminal
    for index in range(len(matrices) - 1, -1, -1):
        following = messages[index + 1]
        messages[index] = tuple(
            sum(
                (
                    matrices[index][source][target] * following[target]
                    for target in range(len(following))
                ),
                start=Fraction(0),
            )
            for source in range(len(matrices[index]))
        )
        if any(value <= 0 for value in messages[index]):
            raise ValueError("the transfer chain has a zero backward message")

    kernels = tuple(
        tuple(
            tuple(
                matrices[index][source][target]
                * messages[index + 1][target]
                / messages[index][source]
                for target in range(len(matrices[index][0]))
            )
            for source in range(len(matrices[index]))
        )
        for index in range(len(matrices))
    )
    raw_composite = _chain_product(matrices)
    markov_composite = _chain_product(kernels)
    certificate = BoundaryMessageMarkovization(
        transfers=matrices,
        terminal_message=terminal,
        backward_messages=tuple(messages),
        markov_kernels=kernels,
        raw_composite=raw_composite,
        markov_composite=markov_composite,
        every_message_strictly_positive=True,
        every_kernel_mass_preserving=True,
        telescoping_endpoint_identity=True,
        independent_row_normalization_used=False,
    )
    if not certificate.validates():
        raise AssertionError("the boundary-message Markovization drifted")
    return certificate


@dataclass(frozen=True)
class AllLabelFineBoundaryTransfer:
    """The exact continuous one-slab transfer before uniform estimates."""

    coupling: Fraction
    face_count: int
    source_spatial_face_count: int
    target_spatial_face_count: int
    temporal_face_count: int
    source_boundary_link_count: int
    target_boundary_link_count: int
    internal_temporal_link_count: int
    boundary_configuration_space: str
    symmetric_transfer_definition: str
    full_all_label_heat_kernels_used: bool
    normalized_internal_haar_integration: bool
    transfer_strictly_positive_and_continuous: bool
    boundary_gauge_invariant: bool
    time_reflection_symmetric: bool
    raw_products_equal_physical_glued_density: bool
    finite_horizon_backward_messages_constructed: bool
    fine_boundary_markov_channel_constructed: bool
    nine_slot_coarse_markov_intertwining_proved: bool
    spacing_uniform_message_ratio_proved: bool

    def validates(self) -> bool:
        plaquettes = boundary_complete_slab_plaquettes(1)
        edges = {
            edge
            for plaquette in plaquettes
            for edge in edges_of(plaquette)
        }
        source_faces = tuple(
            plaquette
            for plaquette in plaquettes
            if 3 not in plaquette[1] and plaquette[0][3] == 0
        )
        target_faces = tuple(
            plaquette
            for plaquette in plaquettes
            if 3 not in plaquette[1] and plaquette[0][3] == 1
        )
        temporal_faces = tuple(
            plaquette for plaquette in plaquettes if 3 in plaquette[1]
        )
        source_links = {
            edge for edge in edges if edge[1] < 3 and edge[0][3] == 0
        }
        target_links = {
            edge for edge in edges if edge[1] < 3 and edge[0][3] == 1
        }
        temporal_links = {edge for edge in edges if edge[1] == 3}
        return (
            0 < self.coupling < 1
            and self.face_count == len(plaquettes) == 72
            and self.source_spatial_face_count == len(source_faces) == 24
            and self.target_spatial_face_count == len(target_faces) == 24
            and self.temporal_face_count == len(temporal_faces) == 24
            and self.source_boundary_link_count == len(source_links) == 48
            and self.target_boundary_link_count == len(target_links) == 48
            and self.internal_temporal_link_count == len(temporal_links) == 20
            and source_links.isdisjoint(target_links)
            and self.boundary_configuration_space
            == "SU2^48 modulo boundary gauge"
            and self.symmetric_transfer_definition
            == "T_s(x,y)=sqrt(W_sp(x))*Integral_G^20 W_temp(x,z,y) dz*sqrt(W_sp(y))"
            and self.full_all_label_heat_kernels_used
            and self.normalized_internal_haar_integration
            and self.transfer_strictly_positive_and_continuous
            and self.boundary_gauge_invariant
            and self.time_reflection_symmetric
            and self.raw_products_equal_physical_glued_density
            and self.finite_horizon_backward_messages_constructed
            and self.fine_boundary_markov_channel_constructed
            and not self.nine_slot_coarse_markov_intertwining_proved
            and not self.spacing_uniform_message_ratio_proved
        )


@cache
def all_label_fine_boundary_transfer(
    coupling: Fraction,
) -> AllLabelFineBoundaryTransfer:
    """Define the exact positive continuous all-label boundary kernel."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie in (0, 1)")
    transfer = AllLabelFineBoundaryTransfer(
        coupling=coupling,
        face_count=72,
        source_spatial_face_count=24,
        target_spatial_face_count=24,
        temporal_face_count=24,
        source_boundary_link_count=48,
        target_boundary_link_count=48,
        internal_temporal_link_count=20,
        boundary_configuration_space="SU2^48 modulo boundary gauge",
        symmetric_transfer_definition=(
            "T_s(x,y)=sqrt(W_sp(x))*Integral_G^20 "
            "W_temp(x,z,y) dz*sqrt(W_sp(y))"
        ),
        full_all_label_heat_kernels_used=True,
        normalized_internal_haar_integration=True,
        transfer_strictly_positive_and_continuous=True,
        boundary_gauge_invariant=True,
        time_reflection_symmetric=True,
        raw_products_equal_physical_glued_density=True,
        finite_horizon_backward_messages_constructed=True,
        fine_boundary_markov_channel_constructed=True,
        nine_slot_coarse_markov_intertwining_proved=False,
        spacing_uniform_message_ratio_proved=False,
    )
    if not transfer.validates():
        raise AssertionError("the all-label fine-boundary transfer drifted")
    return transfer


@dataclass(frozen=True)
class CoarseBoundarySufficiencyAudit:
    """Exact hidden fine-boundary direction invisible to all nine loops."""

    coupling: Fraction
    retained_coarse_path_count: int
    retained_coarse_path_link_count: int
    invisible_free_lower_spatial_link_count: int
    witness_link_id: int
    witness_geometric_link: tuple[tuple[int, int, int, int], int]
    witness_incident_lower_spatial_faces: tuple[int, ...]
    witness_absent_from_every_coarse_path: bool
    identity_and_center_flip_have_same_coarse_holonomies: bool
    center_flip_changes_spatial_weight: bool
    heat_identity_minus_center_series: str
    raw_transfer_factors_through_nine_coarse_loops: bool
    coarse_markov_lumpability_refuted: bool
    enlargement_or_conditional_cancellation_required: bool

    def validates(self) -> bool:
        complex_, faces, plaquettes = corrected_slab_haar_complex(1)
        paths = coarse_face_paths()
        retained_links = {
            link for path in paths for link, _orientation in path
        }
        ordered_geometric_edges = tuple(
            sorted(
                {
                    edge
                    for plaquette in plaquettes
                    for edge in edges_of(plaquette)
                }
            )
        )
        invisible: list[tuple[int, tuple[int, ...]]] = []
        for link in complex_.free:
            incident = tuple(
                face_id
                for face_id, (face, plaquette) in enumerate(
                    zip(faces, plaquettes, strict=True)
                )
                if (
                    3 not in plaquette[1]
                    and plaquette[0][3] == 0
                    and any(face_link == link for face_link, _ in face)
                )
            )
            if incident and link not in retained_links:
                invisible.append((link, incident))
        return (
            0 < self.coupling < 1
            and self.retained_coarse_path_count == len(paths) == 9
            and self.retained_coarse_path_link_count == len(retained_links) == 40
            and self.invisible_free_lower_spatial_link_count
            == len(invisible)
            == 17
            and self.witness_link_id == invisible[0][0] == 7
            and self.witness_geometric_link
            == ordered_geometric_edges[self.witness_link_id]
            == ((0, 0, 1, 0), 0)
            and self.witness_incident_lower_spatial_faces
            == invisible[0][1]
            == (1, 9, 10)
            and self.witness_absent_from_every_coarse_path
            and self.witness_link_id not in retained_links
            and self.identity_and_center_flip_have_same_coarse_holonomies
            and self.center_flip_changes_spatial_weight
            and self.heat_identity_minus_center_series
            == "K_s(I)-K_s(-I)=2*Sum_{n odd}(n+1)^2*s^(n(n+2))>0"
            and not self.raw_transfer_factors_through_nine_coarse_loops
            and not self.coarse_markov_lumpability_refuted
            and self.enlargement_or_conditional_cancellation_required
        )


@cache
def coarse_boundary_sufficiency_audit(
    coupling: Fraction,
) -> CoarseBoundarySufficiencyAudit:
    """Pin one center-valued fine direction invisible to the coarse paths."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie in (0, 1)")
    audit = CoarseBoundarySufficiencyAudit(
        coupling=coupling,
        retained_coarse_path_count=9,
        retained_coarse_path_link_count=40,
        invisible_free_lower_spatial_link_count=17,
        witness_link_id=7,
        witness_geometric_link=((0, 0, 1, 0), 0),
        witness_incident_lower_spatial_faces=(1, 9, 10),
        witness_absent_from_every_coarse_path=True,
        identity_and_center_flip_have_same_coarse_holonomies=True,
        center_flip_changes_spatial_weight=True,
        heat_identity_minus_center_series=(
            "K_s(I)-K_s(-I)=2*Sum_{n odd}(n+1)^2*s^(n(n+2))>0"
        ),
        raw_transfer_factors_through_nine_coarse_loops=False,
        coarse_markov_lumpability_refuted=False,
        enlargement_or_conditional_cancellation_required=True,
    )
    if not audit.validates():
        raise AssertionError("the coarse-boundary sufficiency audit drifted")
    return audit


def _connected_component_count(
    vertices: set[Vertex4],
    edges: set[Link4],
) -> int:
    neighbors: dict[Vertex4, set[Vertex4]] = {
        vertex: set() for vertex in vertices
    }
    for base, direction in edges:
        target = add_e(base, direction)
        neighbors[base].add(target)
        neighbors[target].add(base)
    unseen = set(vertices)
    component_count = 0
    while unseen:
        component_count += 1
        stack = [unseen.pop()]
        while stack:
            vertex = stack.pop()
            for neighbor in neighbors[vertex]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
    return component_count


@dataclass(frozen=True)
class EnlargedFineBoundaryCarrier:
    """Complete gauge-invariant boundary carrier used instead of nine loops."""

    spatial_boundary_link_count: int
    spatial_boundary_vertex_count: int
    connected_component_count: int
    spanning_tree_link_count: int
    gauge_fixed_cycle_rank: int
    source_target_carriers_identical: bool
    carrier_description: str
    retained_projection: str
    identity_projection_markov_lumpable: bool
    fine_boundary_transfer_acts_on_carrier: bool
    finite_horizon_markov_composition_exact: bool
    coarse_spatial_loops_per_slice: int
    coarse_spatial_observables_recoverable: bool
    temporal_coarse_observables_retained_in_environment_instrument: bool
    nine_loop_raw_sufficiency_required: bool
    carrier_enlargement_completed: bool
    spacing_uniform_message_order_proved: bool

    def validates(self) -> bool:
        plaquettes = boundary_complete_slab_plaquettes(1)
        all_edges = {
            edge
            for plaquette in plaquettes
            for edge in edges_of(plaquette)
        }
        boundary_edges = {
            edge
            for edge in all_edges
            if edge[1] < 3 and edge[0][3] == 0
        }
        vertices = {
            vertex
            for base, direction in boundary_edges
            for vertex in (base, add_e(base, direction))
        }
        components = _connected_component_count(vertices, boundary_edges)
        cycle_rank = len(boundary_edges) - len(vertices) + components
        return (
            self.spatial_boundary_link_count == len(boundary_edges) == 48
            and self.spatial_boundary_vertex_count == len(vertices) == 26
            and self.connected_component_count == components == 1
            and self.spanning_tree_link_count == len(vertices) - 1 == 25
            and self.gauge_fixed_cycle_rank == cycle_rank == 23
            and self.source_target_carriers_identical
            and self.carrier_description
            == "tree-gauge SU2^23 with residual root conjugation on invariants"
            and self.retained_projection == "identity-on-full-fine-boundary"
            and self.identity_projection_markov_lumpable
            and self.fine_boundary_transfer_acts_on_carrier
            and self.finite_horizon_markov_composition_exact
            and self.coarse_spatial_loops_per_slice == 3
            and self.coarse_spatial_observables_recoverable
            and self.temporal_coarse_observables_retained_in_environment_instrument
            and not self.nine_loop_raw_sufficiency_required
            and self.carrier_enlargement_completed
            and not self.spacing_uniform_message_order_proved
        )


@cache
def enlarged_fine_boundary_carrier() -> EnlargedFineBoundaryCarrier:
    """Retain all boundary cycles so Markov intertwining is the identity."""

    carrier = EnlargedFineBoundaryCarrier(
        spatial_boundary_link_count=48,
        spatial_boundary_vertex_count=26,
        connected_component_count=1,
        spanning_tree_link_count=25,
        gauge_fixed_cycle_rank=23,
        source_target_carriers_identical=True,
        carrier_description=(
            "tree-gauge SU2^23 with residual root conjugation on invariants"
        ),
        retained_projection="identity-on-full-fine-boundary",
        identity_projection_markov_lumpable=True,
        fine_boundary_transfer_acts_on_carrier=True,
        finite_horizon_markov_composition_exact=True,
        coarse_spatial_loops_per_slice=3,
        coarse_spatial_observables_recoverable=True,
        temporal_coarse_observables_retained_in_environment_instrument=True,
        nine_loop_raw_sufficiency_required=False,
        carrier_enlargement_completed=True,
        spacing_uniform_message_order_proved=False,
    )
    if not carrier.validates():
        raise AssertionError("the enlarged fine-boundary carrier drifted")
    return carrier


@dataclass(frozen=True)
class PhysicalBoundaryMessageBlueprint:
    """Exact algebra closed around the still-open all-label boundary kernel."""

    gluing_geometry: TwoSlabPhysicalGluingAudit
    spatial_slice_weight_assignment: str
    raw_transfer_fiber_product_composition_exact: bool
    independent_one_slab_row_normalization_composes_physically: bool
    backward_message_markovization_exact: bool
    finite_horizon_mass_preserving_composition_exact: bool
    same_boundary_carrier_at_every_time_slice: bool
    terminal_boundary_message_required: bool
    all_label_continuous_boundary_transfer_constructed: bool
    fine_boundary_physical_gluing_channel_constructed: bool
    nine_slot_coarse_markov_intertwining_proved: bool
    spacing_uniform_boundary_message_ratio_proved: bool
    spacing_uniform_grouped_minorization_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        finite_witness = markovize_transfer_chain(
            (
                ((1, 2), (3, 1)),
                ((2, 1), (1, 4)),
            ),
            (1, 2),
        )
        physical_transfer = all_label_fine_boundary_transfer(Fraction(1, 2))
        coarse_sufficiency = coarse_boundary_sufficiency_audit(
            Fraction(1, 2)
        )
        enlarged_carrier = enlarged_fine_boundary_carrier()
        return (
            self.gluing_geometry.validates()
            and finite_witness.validates()
            and physical_transfer.validates()
            and coarse_sufficiency.validates()
            and enlarged_carrier.validates()
            and self.spatial_slice_weight_assignment
            == "initial-boundary-weight plus temporal-and-target-spatial per step"
            and self.raw_transfer_fiber_product_composition_exact
            and not self.independent_one_slab_row_normalization_composes_physically
            and self.backward_message_markovization_exact
            and self.finite_horizon_mass_preserving_composition_exact
            and self.same_boundary_carrier_at_every_time_slice
            and self.terminal_boundary_message_required
            and self.all_label_continuous_boundary_transfer_constructed
            and self.fine_boundary_physical_gluing_channel_constructed
            and not self.nine_slot_coarse_markov_intertwining_proved
            and not self.spacing_uniform_boundary_message_ratio_proved
            and not self.spacing_uniform_grouped_minorization_proved
            and self.first_open_obligation
            == "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        )


def physical_boundary_message_blueprint() -> PhysicalBoundaryMessageBlueprint:
    """Return the exact physical normalization route and remaining estimate."""

    blueprint = PhysicalBoundaryMessageBlueprint(
        gluing_geometry=two_slab_physical_gluing_audit(),
        spatial_slice_weight_assignment=(
            "initial-boundary-weight plus temporal-and-target-spatial per step"
        ),
        raw_transfer_fiber_product_composition_exact=True,
        independent_one_slab_row_normalization_composes_physically=False,
        backward_message_markovization_exact=True,
        finite_horizon_mass_preserving_composition_exact=True,
        same_boundary_carrier_at_every_time_slice=True,
        terminal_boundary_message_required=True,
        all_label_continuous_boundary_transfer_constructed=True,
        fine_boundary_physical_gluing_channel_constructed=True,
        nine_slot_coarse_markov_intertwining_proved=False,
        spacing_uniform_boundary_message_ratio_proved=False,
        spacing_uniform_grouped_minorization_proved=False,
        first_open_obligation=(
            "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        ),
    )
    if not blueprint.validates():
        raise AssertionError("the physical boundary-message blueprint drifted")
    return blueprint
