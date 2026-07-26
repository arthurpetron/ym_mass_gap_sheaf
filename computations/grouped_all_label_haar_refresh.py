"""Exact BF4 census for a grouped all-label SU(2) heat corridor.

The first physical grouping mechanism that can possibly avoid the vanishing
microscopic Haar floor is the exact heat-kernel convolution law.  In the
repository's rational heat coordinate ``s``, the doubled-spin ``label`` mode
has multiplier

    s ** (label * (label + 2)).

After ``steps`` Haar-convolved plaquettes the multiplier is therefore the
same expression with grouped coordinate ``u = s ** steps``.  This module
certifies a useful all-label consequence without evaluating a transcendental
heat kernel:

* if ``0 < u <= 1/2``, then the full central SU(2) heat kernel is bounded
  below by the exact rational ``1055/2272`` relative to normalized Haar;
* a product of ``corridor_count`` independently refreshed coordinates has a
  common Haar packet of mass at least ``(1055/2272) ** corridor_count``;
* every Peter--Weyl mode remains present because ``u > 0``.

The lower bound uses ``|chi_n| <= n + 1`` and an exact geometric envelope
for every label ``n >= 2``.  It is an all-label certificate, not a
representation-cutoff experiment.

This does *not* assert that the interacting 72-plaquette corrected-slab map
dominates such a product corridor in completely-positive order.  The final
frontier object records that missing geometric/operator comparison and the
also-missing physical relation between lattice spacing and cumulative heat
time.  Those two fields are exactly what separates the positive corridor
result from closure of BF4.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product

from computations.all_label_whole_slab_tail import (
    heat_character_sup_term,
    single_plaquette_all_label_tail,
)
from computations.boundary_message_markovization import (
    physical_boundary_message_blueprint,
)
from computations.boundary_message_uniform_order import (
    physical_backward_message_order_frontier,
)
from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.corrected_slab_physical_gluing import (
    interface_floor_ceiling_no_go,
    two_slab_physical_gluing_audit,
)
from computations.dual_positivity_geometry_bridge import edges_of
from computations.exact_haar_network import casimir4, invariant_multiplicity
from computations.physical_all_label_channel_composition import (
    dyadic_fixed_distance_iteration_no_go,
    mass_preserving_channel_promotion,
)
from computations.physical_all_label_choi_domination import (
    physical_all_label_choi_domination,
)
from computations.su2_magnetic_intertwiners import (
    transverse_magnetic_tensor_packet,
)
from computations.transverse_all_label_recoupling import (
    finite_cutoff_transverse_recoupling_carrier,
    transverse_recoupling_census,
)
from computations.transverse_all_label_tail import (
    transverse_all_label_uniform_tail,
)
from computations.transverse_cutoff_one_cp_order import (
    cutoff_one_cp_order_audit,
)
from computations.transverse_cutoff_one_loop_tensor import (
    cutoff_one_loop_tensor_audit,
)
from computations.transverse_cutoff_one_residual_tensor import (
    cutoff_one_residual_loop_tensor_audit,
)
from computations.transverse_open_index_network import (
    cutoff_one_open_index_network,
)
from computations.transverse_residual_operator_tail import (
    transverse_residual_operator_tail,
)
from computations.transverse_weak_coupling_tail_obstruction import (
    fixed_cutoff_weak_coupling_obstruction,
)
from computations.whole_corrected_slab_kraus import coarse_face_paths

GROUPED_HEAT_CAP = Fraction(1, 2)
TAIL_START_CUTOFF = 1
ALL_LABEL_HAAR_FLOOR = Fraction(1055, 2272)
BF32_COARSE_HOLONOMY_COUNT = 9


def grouped_heat_coordinate(coupling: Fraction, steps: int) -> Fraction:
    """Return the exact heat coordinate after Haar convolution."""

    if not 0 < coupling < 1:
        raise ValueError("the microscopic heat coordinate must lie in (0, 1)")
    if steps < 1:
        raise ValueError("a grouped corridor must contain at least one step")
    return Fraction(coupling**steps)


def heat_mode_multiplier(coupling: Fraction, steps: int, label: int) -> Fraction:
    """Return one exact all-label multiplier after grouping."""

    if label < 0:
        raise ValueError("a doubled SU(2) label must be nonnegative")
    return Fraction(grouped_heat_coordinate(coupling, steps) ** casimir4(label))


def least_steps_below_cap(
    coupling: Fraction,
    cap: Fraction = GROUPED_HEAT_CAP,
) -> int:
    """Locate the least positive grouping length with ``coupling**n <= cap``."""

    if not 0 < coupling < 1:
        raise ValueError("the microscopic heat coordinate must lie in (0, 1)")
    if not 0 < cap < 1:
        raise ValueError("the grouped heat cap must lie in (0, 1)")
    steps = 1
    grouped = coupling
    while grouped > cap:
        grouped *= coupling
        steps += 1
    return steps


def ceil_fraction(value: Fraction) -> int:
    """Constructive ceiling of a nonnegative rational."""

    if value < 0:
        raise ValueError("the rational ceiling helper expects a nonnegative value")
    return (value.numerator + value.denominator - 1) // value.denominator


@dataclass(frozen=True)
class AllLabelHaarFloorCertificate:
    """Exact all-label Haar minorization for one grouped heat corridor."""

    microscopic_coupling: Fraction
    steps: int
    grouped_coupling: Fraction
    cap: Fraction
    tail_cutoff: int
    first_excited_absolute_bound: Fraction
    remaining_absolute_tail_bound: Fraction
    nonvacuum_absolute_bound: Fraction
    common_haar_floor: Fraction
    all_label: bool
    convolution_semigroup_exact: bool
    every_peter_weyl_mode_positive: bool

    def mode_multiplier(self, label: int) -> Fraction:
        """Return the grouped multiplier for any requested label."""

        return heat_mode_multiplier(
            self.microscopic_coupling,
            self.steps,
            label,
        )

    def packet_mass(self, corridor_count: int) -> Fraction:
        """Return the product-Haar common mass for a finite corridor cover."""

        if corridor_count < 1:
            raise ValueError("at least one corridor coordinate is required")
        return self.common_haar_floor**corridor_count

    def validates(self) -> bool:
        try:
            grouped = grouped_heat_coordinate(
                self.microscopic_coupling,
                self.steps,
            )
            envelope = single_plaquette_all_label_tail(
                self.cap,
                self.tail_cutoff,
            )
        except ValueError:
            return False
        first_excited = heat_character_sup_term(self.cap, 1)
        remaining_tail = envelope.tail_bound
        nonvacuum = first_excited + remaining_tail
        floor = 1 - nonvacuum
        return (
            self.grouped_coupling == grouped
            and 0 < grouped <= self.cap == GROUPED_HEAT_CAP
            and self.tail_cutoff == TAIL_START_CUTOFF
            and self.first_excited_absolute_bound == first_excited
            == Fraction(1, 2)
            and self.remaining_absolute_tail_bound == remaining_tail
            == Fraction(81, 2272)
            and self.nonvacuum_absolute_bound == nonvacuum
            == Fraction(1217, 2272)
            and self.common_haar_floor == floor == ALL_LABEL_HAAR_FLOOR
            and 0 < floor < 1
            and self.all_label
            and self.convolution_semigroup_exact
            and self.every_peter_weyl_mode_positive
            and all(self.mode_multiplier(label) > 0 for label in range(8))
        )


def all_label_haar_floor_certificate(
    coupling: Fraction,
    steps: int | None = None,
) -> AllLabelHaarFloorCertificate:
    """Construct the exact common-Haar certificate once grouping reaches 1/2."""

    selected_steps = (
        least_steps_below_cap(coupling) if steps is None else steps
    )
    grouped = grouped_heat_coordinate(coupling, selected_steps)
    if grouped > GROUPED_HEAT_CAP:
        raise ValueError("the selected grouping has not reached the certified cap")
    envelope = single_plaquette_all_label_tail(
        GROUPED_HEAT_CAP,
        TAIL_START_CUTOFF,
    )
    first_excited = heat_character_sup_term(GROUPED_HEAT_CAP, 1)
    remaining_tail = envelope.tail_bound
    nonvacuum = first_excited + remaining_tail
    certificate = AllLabelHaarFloorCertificate(
        microscopic_coupling=coupling,
        steps=selected_steps,
        grouped_coupling=grouped,
        cap=GROUPED_HEAT_CAP,
        tail_cutoff=TAIL_START_CUTOFF,
        first_excited_absolute_bound=first_excited,
        remaining_absolute_tail_bound=remaining_tail,
        nonvacuum_absolute_bound=nonvacuum,
        common_haar_floor=1 - nonvacuum,
        all_label=True,
        convolution_semigroup_exact=True,
        every_peter_weyl_mode_positive=grouped > 0,
    )
    if not certificate.validates():
        raise AssertionError("the grouped all-label Haar floor drifted")
    return certificate


@dataclass(frozen=True)
class FixedDistanceCorridorCertificate:
    """Exact cumulative-heat criterion for one rational spacing and distance."""

    spacing: Fraction
    physical_distance: Fraction
    microscopic_coupling: Fraction
    grouped_steps: int
    grouped_coupling: Fraction
    cumulative_heat_condition: bool
    common_haar_floor: Fraction | None
    nine_holonomy_packet_mass: Fraction | None

    def validates(self) -> bool:
        if (
            not self.spacing > 0
            or not self.physical_distance > 0
            or not 0 < self.microscopic_coupling < 1
        ):
            return False
        steps = ceil_fraction(self.physical_distance / self.spacing)
        grouped = self.microscopic_coupling**steps
        condition = grouped <= GROUPED_HEAT_CAP
        expected_floor = ALL_LABEL_HAAR_FLOOR if condition else None
        expected_nine = (
            ALL_LABEL_HAAR_FLOOR**BF32_COARSE_HOLONOMY_COUNT
            if condition
            else None
        )
        return (
            self.grouped_steps == steps >= 1
            and self.grouped_coupling == grouped
            and self.cumulative_heat_condition == condition
            and self.common_haar_floor == expected_floor
            and self.nine_holonomy_packet_mass == expected_nine
        )


def fixed_distance_corridor_certificate(
    spacing: Fraction,
    physical_distance: Fraction,
    microscopic_coupling: Fraction,
) -> FixedDistanceCorridorCertificate:
    """Check the exact fixed-distance cumulative-heat condition."""

    if spacing <= 0 or physical_distance <= 0:
        raise ValueError("spacing and physical distance must be positive")
    steps = ceil_fraction(physical_distance / spacing)
    grouped = grouped_heat_coordinate(microscopic_coupling, steps)
    condition = grouped <= GROUPED_HEAT_CAP
    certificate = FixedDistanceCorridorCertificate(
        spacing=spacing,
        physical_distance=physical_distance,
        microscopic_coupling=microscopic_coupling,
        grouped_steps=steps,
        grouped_coupling=grouped,
        cumulative_heat_condition=condition,
        common_haar_floor=ALL_LABEL_HAAR_FLOOR if condition else None,
        nine_holonomy_packet_mass=(
            ALL_LABEL_HAAR_FLOOR**BF32_COARSE_HOLONOMY_COUNT
            if condition
            else None
        ),
    )
    if not certificate.validates():
        raise AssertionError("the fixed-distance corridor certificate drifted")
    return certificate


@dataclass(frozen=True)
class CumulativeHeatModeWitness:
    """Rescale the bare heat-kernel mode margin implied by grouped mixing.

    The quantity ``rho = s**3`` is a Fourier multiplier of the local
    plaquette heat kernel.  It is not the separator of the interacting
    gauge-invariant transfer operator unless an additional physical
    identification theorem is supplied.
    """

    spacing: Fraction
    physical_distance: Fraction
    microscopic_coupling: Fraction
    grouped_steps: int
    fundamental_separator: Fraction
    grouped_separator: Fraction
    lattice_margin: Fraction
    lattice_margin_lower: Fraction
    rescaled_bare_margin: Fraction
    rescaled_bare_margin_lower: Fraction
    rescaled_bare_floor: Fraction | None
    physical_transfer_identification_proved: bool

    def validates(self) -> bool:
        if (
            self.spacing <= 0
            or self.physical_distance <= 0
            or not 0 < self.microscopic_coupling < 1
        ):
            return False
        steps = ceil_fraction(self.physical_distance / self.spacing)
        separator = self.microscopic_coupling**3
        grouped_separator = separator**steps
        if grouped_separator > Fraction(1, 8):
            return False
        lattice_margin = 1 - separator
        lattice_lower = Fraction(7, 8 * steps)
        rescaled_margin = lattice_margin / self.spacing
        rescaled_lower = lattice_lower / self.spacing
        fixed_floor = (
            Fraction(7, 16) / self.physical_distance
            if self.spacing <= self.physical_distance
            else None
        )
        return (
            self.grouped_steps == steps
            and self.fundamental_separator == separator
            and self.grouped_separator == grouped_separator
            and self.lattice_margin == lattice_margin >= lattice_lower
            and self.lattice_margin_lower == lattice_lower
            and self.rescaled_bare_margin == rescaled_margin >= rescaled_lower
            and self.rescaled_bare_margin_lower == rescaled_lower
            and steps * self.spacing
            <= self.physical_distance + self.spacing
            and self.rescaled_bare_floor == fixed_floor
            and (
                fixed_floor is None
                or rescaled_margin >= rescaled_lower >= fixed_floor
            )
            and not self.physical_transfer_identification_proved
        )


def cumulative_heat_mode_witness(
    certificate: FixedDistanceCorridorCertificate,
) -> CumulativeHeatModeWitness:
    """Derive a rescaled bare-mode margin from grouped heat mixing.

    If ``s**m <= 1/2``, then the fundamental bare multiplier satisfies
    ``(s**3)**m <= 1/8``.  The exact Bernoulli inequality

        1 - rho**m <= m * (1 - rho)

    therefore yields ``1 - rho >= 7/(8m)``.  With
    ``m = ceil(L/a)`` and ``a <= L``, this gives the spacing-uniform floor
    ``(1-rho)/a >= 7/(16L)``.  This is an exact statement about the bare
    heat-kernel mode.  Calling it a physical mass-gap estimate would require
    the separate, currently open identification with the interacting
    gauge-invariant transfer separator.
    """

    if not certificate.validates() or not certificate.cumulative_heat_condition:
        raise ValueError("the grouped-half cumulative heat condition is required")
    steps = certificate.grouped_steps
    separator = certificate.microscopic_coupling**3
    grouped_separator = separator**steps
    if grouped_separator > Fraction(1, 8):
        raise AssertionError("cubing the grouped-half condition drifted")
    lattice_lower = Fraction(7, 8 * steps)
    physical_lower = lattice_lower / certificate.spacing
    witness = CumulativeHeatModeWitness(
        spacing=certificate.spacing,
        physical_distance=certificate.physical_distance,
        microscopic_coupling=certificate.microscopic_coupling,
        grouped_steps=steps,
        fundamental_separator=separator,
        grouped_separator=grouped_separator,
        lattice_margin=1 - separator,
        lattice_margin_lower=lattice_lower,
        rescaled_bare_margin=(1 - separator) / certificate.spacing,
        rescaled_bare_margin_lower=physical_lower,
        rescaled_bare_floor=(
            Fraction(7, 16) / certificate.physical_distance
            if certificate.spacing <= certificate.physical_distance
            else None
        ),
        physical_transfer_identification_proved=False,
    )
    if not witness.validates():
        raise AssertionError("the cumulative-heat bare-mode witness drifted")
    return witness


@dataclass(frozen=True)
class CorrectedSlabCorridorGeometryAudit:
    """Exact geometry of the nine canonical coarse-loop filling disks."""

    corridor_count: int
    spatial_corridor_count: int
    temporal_corridor_count: int
    corridor_face_count_census: tuple[tuple[int, int], ...]
    selected_face_count: int
    selected_faces_pairwise_disjoint: bool
    internal_link_count: int
    internal_links_pairwise_disjoint: bool
    every_disk_boundary_matches_coarse_path: bool
    off_corridor_incidence_per_internal_link_census: tuple[tuple[int, int], ...]
    every_internal_link_transversely_coupled: bool
    literal_semigroup_factorization_of_full_integrand: bool

    def validates(self) -> bool:
        return (
            self.corridor_count == BF32_COARSE_HOLONOMY_COUNT
            and self.spatial_corridor_count == 6
            and self.temporal_corridor_count == 3
            and self.corridor_face_count_census == ((2, 3), (4, 6))
            and self.selected_face_count == 30
            and self.selected_faces_pairwise_disjoint
            and self.internal_link_count == 27
            and self.internal_links_pairwise_disjoint
            and self.every_disk_boundary_matches_coarse_path
            and self.off_corridor_incidence_per_internal_link_census
            == ((2, 27),)
            and self.every_internal_link_transversely_coupled
            and not self.literal_semigroup_factorization_of_full_integrand
        )


def _corridor_face_ids() -> tuple[tuple[int, ...], ...]:
    """Return the canonical fine-disk faces for the nine coarse paths."""

    _complex, _faces, plaquettes = corrected_slab_haar_complex(1)
    face_index = {
        plaquette: index for index, plaquette in enumerate(plaquettes)
    }
    corridors: list[tuple[int, ...]] = []
    for time in (0, 1):
        for first, second in ((0, 1), (0, 2), (1, 2)):
            face_ids: list[int] = []
            for first_offset in range(2):
                for second_offset in range(2):
                    point = [0, 0, 0, time]
                    point[first] += first_offset
                    point[second] += second_offset
                    vertex = (point[0], point[1], point[2], point[3])
                    face_ids.append(
                        face_index[(vertex, (first, second))]
                    )
            corridors.append(tuple(face_ids))
    for direction in range(3):
        face_ids = []
        for offset in range(2):
            point = [0, 0, 0, 0]
            point[direction] += offset
            vertex = (point[0], point[1], point[2], point[3])
            face_ids.append(
                face_index[(vertex, (direction, 3))]
            )
        corridors.append(tuple(face_ids))
    return tuple(corridors)


@cache
def corrected_slab_corridor_geometry_audit() -> (
    CorrectedSlabCorridorGeometryAudit
):
    """Pin the canonical corridors and the transverse-coupling obstruction."""

    _complex, _faces, plaquettes = corrected_slab_haar_complex(1)
    corridors = _corridor_face_ids()
    selected_faces = {
        face_id for corridor in corridors for face_id in corridor
    }
    geometric_edges = tuple(
        sorted(
            {
                edge
                for plaquette in plaquettes
                for edge in edges_of(plaquette)
            }
        )
    )
    edge_index = {
        edge: index for index, edge in enumerate(geometric_edges)
    }
    incident_faces: defaultdict[int, list[int]] = defaultdict(list)
    for face_id, plaquette in enumerate(plaquettes):
        for edge in edges_of(plaquette):
            incident_faces[edge_index[edge]].append(face_id)

    internal_sets: list[set[int]] = []
    boundary_matches: list[bool] = []
    off_corridor_counts: list[int] = []
    for corridor_index, corridor in enumerate(corridors):
        incidence = Counter(
            edge_index[edge]
            for face_id in corridor
            for edge in edges_of(plaquettes[face_id])
        )
        internal = {
            edge_id for edge_id, count in incidence.items() if count == 2
        }
        boundary = {
            edge_id for edge_id, count in incidence.items() if count == 1
        }
        coarse_boundary = {
            edge_id for edge_id, _orientation in coarse_face_paths()[corridor_index]
        }
        internal_sets.append(internal)
        boundary_matches.append(boundary == coarse_boundary)
        off_corridor_counts.extend(
            sum(face_id not in selected_faces for face_id in incident_faces[edge_id])
            for edge_id in internal
        )

    all_internal = {
        edge_id for internal in internal_sets for edge_id in internal
    }
    internal_total = sum(len(internal) for internal in internal_sets)
    certificate = CorrectedSlabCorridorGeometryAudit(
        corridor_count=len(corridors),
        spatial_corridor_count=6,
        temporal_corridor_count=3,
        corridor_face_count_census=tuple(
            sorted(Counter(map(len, corridors)).items())
        ),
        selected_face_count=len(selected_faces),
        selected_faces_pairwise_disjoint=(
            len(selected_faces) == sum(map(len, corridors))
        ),
        internal_link_count=len(all_internal),
        internal_links_pairwise_disjoint=(
            len(all_internal) == internal_total
        ),
        every_disk_boundary_matches_coarse_path=all(boundary_matches),
        off_corridor_incidence_per_internal_link_census=tuple(
            sorted(Counter(off_corridor_counts).items())
        ),
        every_internal_link_transversely_coupled=all(
            count > 0 for count in off_corridor_counts
        ),
        literal_semigroup_factorization_of_full_integrand=False,
    )
    if not certificate.validates():
        raise AssertionError("the corrected-slab corridor geometry drifted")
    return certificate


@dataclass(frozen=True)
class TransverseLeafReductionAudit:
    """Exact Haar-normalization peeling of the off-corridor factor graph."""

    initial_off_corridor_faces: int
    peeled_face_count: int
    residual_core_face_count: int
    peel_witnesses: tuple[tuple[int, int], ...]
    residual_core_faces: tuple[int, ...]
    residual_free_link_degree_census: tuple[tuple[int, int], ...]
    residual_component_face_count_census: tuple[tuple[int, int], ...]
    protected_links_in_residual_core: int
    every_residual_leaf_is_corridor_protected: bool
    heat_normalization_makes_each_peel_exact: bool
    maximal_for_unprotected_leaf_rule: bool

    def validates(self) -> bool:
        return (
            self.initial_off_corridor_faces == 42
            and self.peeled_face_count == 21
            and self.residual_core_face_count == 21
            and len(self.peel_witnesses) == self.peeled_face_count
            and self.residual_core_faces
            == (
                9,
                11,
                13,
                15,
                19,
                20,
                23,
                25,
                29,
                31,
                32,
                39,
                40,
                41,
                44,
                47,
                49,
                50,
                56,
                58,
                59,
            )
            and self.residual_free_link_degree_census
            == ((1, 9), (2, 9), (3, 5))
            and self.residual_component_face_count_census
            == ((1, 6), (15, 1))
            and self.protected_links_in_residual_core == 18
            and self.every_residual_leaf_is_corridor_protected
            and self.heat_normalization_makes_each_peel_exact
            and self.maximal_for_unprotected_leaf_rule
        )


@cache
def transverse_leaf_reduction_audit() -> TransverseLeafReductionAudit:
    """Peel every off-corridor face carrying an unprotected leaf Haar link."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    selected_faces = {
        face_id
        for corridor in _corridor_face_ids()
        for face_id in corridor
    }
    free_links = set(complex_.free)
    protected_links = {
        link
        for face_id in selected_faces
        for link, _orientation in faces[face_id]
        if link in free_links
    }
    remaining = set(range(len(faces))) - selected_faces
    peeled: list[tuple[int, int]] = []
    while True:
        link_degrees = Counter(
            link
            for face_id in remaining
            for link, _orientation in faces[face_id]
            if link in free_links
        )
        witness: tuple[int, int] | None = None
        for face_id in sorted(remaining):
            candidates = tuple(
                link
                for link, _orientation in faces[face_id]
                if (
                    link in free_links
                    and link not in protected_links
                    and link_degrees[link] == 1
                )
            )
            if candidates:
                witness = (face_id, candidates[0])
                break
        if witness is None:
            break
        remaining.remove(witness[0])
        peeled.append(witness)

    residual_degrees = Counter(
        link
        for face_id in remaining
        for link, _orientation in faces[face_id]
        if link in free_links
    )
    residual_leaf_links = {
        link for link, degree in residual_degrees.items() if degree == 1
    }
    faces_by_link: defaultdict[int, set[int]] = defaultdict(set)
    for face_id in remaining:
        for link, _orientation in faces[face_id]:
            if link in free_links:
                faces_by_link[link].add(face_id)
    face_neighbors: defaultdict[int, set[int]] = defaultdict(set)
    for incident in faces_by_link.values():
        for face_id in incident:
            face_neighbors[face_id].update(incident - {face_id})
    unseen = set(remaining)
    component_sizes: list[int] = []
    while unseen:
        root = min(unseen)
        stack = [root]
        unseen.remove(root)
        size = 0
        while stack:
            face_id = stack.pop()
            size += 1
            for neighbor in face_neighbors[face_id]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
        component_sizes.append(size)
    certificate = TransverseLeafReductionAudit(
        initial_off_corridor_faces=len(faces) - len(selected_faces),
        peeled_face_count=len(peeled),
        residual_core_face_count=len(remaining),
        peel_witnesses=tuple(peeled),
        residual_core_faces=tuple(sorted(remaining)),
        residual_free_link_degree_census=tuple(
            sorted(Counter(residual_degrees.values()).items())
        ),
        residual_component_face_count_census=tuple(
            sorted(Counter(component_sizes).items())
        ),
        protected_links_in_residual_core=sum(
            link in protected_links for link in residual_degrees
        ),
        every_residual_leaf_is_corridor_protected=(
            residual_leaf_links <= protected_links
        ),
        heat_normalization_makes_each_peel_exact=True,
        maximal_for_unprotected_leaf_rule=not any(
            degree == 1 and link not in protected_links
            for link, degree in residual_degrees.items()
        ),
    )
    if not certificate.validates():
        raise AssertionError("the transverse leaf reduction drifted")
    return certificate


@dataclass(frozen=True)
class TransverseCutoffOneFusionAudit:
    """Complete cutoff-one fusion ledger of the pinned transverse residual.

    The actual boundary outputs ``0``, ``1`` and ``2`` are retained at every
    corridor-protected link.  Thus two incident fundamental strands keep
    their distinct singlet and triplet channels instead of being collapsed
    to mod-two parity.

    The corresponding coherent partial Haar tensors are now constructed in
    the fundamental trace-word basis.  This is still not a CP-order theorem:
    their all-label lift and positive lower bound remain open.
    """

    representation_cutoff: int
    connected_core_faces: tuple[int, ...]
    decoration_faces: tuple[int, ...]
    internal_trivalent_link_count: int
    core_protected_link_count: int
    decoration_protected_link_count: int
    decoration_protected_degree_census: tuple[tuple[int, int], ...]
    protected_link_sets_pairwise_disjoint: bool
    binary_internal_admissible_assignments: int
    binary_boundary_parity_profiles: int
    binary_fillings_per_parity_profile: int
    complete_core_boundary_label_profiles: int
    complete_core_fusion_paths: int
    core_profile_multiplicity_census: tuple[tuple[int, int], ...]
    core_profile_face_count_term_census: tuple[tuple[int, int], ...]
    vacuum_profile_face_count_ledger: tuple[tuple[int, int], ...]
    decoration_boundary_label_profiles: int
    complete_residual_boundary_label_profiles: int
    complete_residual_fusion_paths: int
    residual_profile_multiplicity_census: tuple[tuple[int, int], ...]
    internal_intertwiner_multiplicity_one: bool
    singlet_triplet_boundary_channels_retained: bool
    parity_only_boundary_carrier_refuted: bool
    coherent_partial_haar_tensors_evaluated: bool
    cp_order_domination_proved: bool
    all_label_completion_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        return (
            self.representation_cutoff == 1
            and self.connected_core_faces
            == (9, 11, 13, 15, 19, 20, 23, 25, 29, 39, 40, 41, 44, 49, 59)
            and self.decoration_faces == (31, 32, 47, 50, 56, 58)
            and self.internal_trivalent_link_count == 5
            and self.core_protected_link_count == 9
            and self.decoration_protected_link_count == 9
            and self.decoration_protected_degree_census == ((1, 3), (2, 3))
            and self.protected_link_sets_pairwise_disjoint
            and self.binary_internal_admissible_assignments == 1024
            and self.binary_boundary_parity_profiles == 128
            and self.binary_fillings_per_parity_profile == 8
            and self.complete_core_boundary_label_profiles == 4761
            and self.complete_core_fusion_paths == 10673
            and self.core_profile_multiplicity_census
            == ((1, 1505), (2, 2184), (4, 944), (8, 128))
            and self.core_profile_face_count_term_census
            == ((1, 2512), (2, 1717), (3, 465), (4, 46), (5, 21))
            and self.vacuum_profile_face_count_ledger
            == ((0, 1), (6, 3), (10, 3), (12, 1))
            and self.decoration_boundary_label_profiles == 64
            and self.complete_residual_boundary_label_profiles == 304704
            and self.complete_residual_fusion_paths == 683072
            and self.residual_profile_multiplicity_census
            == ((1, 96320), (2, 139776), (4, 60416), (8, 8192))
            and self.internal_intertwiner_multiplicity_one
            and self.singlet_triplet_boundary_channels_retained
            and self.parity_only_boundary_carrier_refuted
            and self.coherent_partial_haar_tensors_evaluated
            and not self.cp_order_domination_proved
            and not self.all_label_completion_proved
            and self.first_open_obligation
            == "evaluate-open-index-all-label-haar-amplitudes"
        )


def _residual_face_components(
    residual_faces: tuple[int, ...],
) -> tuple[tuple[int, ...], ...]:
    """Return components joined through free corrected-slab Haar links."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    residual = set(residual_faces)
    faces_by_link: defaultdict[int, set[int]] = defaultdict(set)
    for face_id in residual:
        for link, _orientation in faces[face_id]:
            if link in complex_.free:
                faces_by_link[link].add(face_id)
    neighbors: defaultdict[int, set[int]] = defaultdict(set)
    for incident in faces_by_link.values():
        for face_id in incident:
            neighbors[face_id].update(incident - {face_id})

    unseen = set(residual)
    components: list[tuple[int, ...]] = []
    while unseen:
        root = min(unseen)
        stack = [root]
        unseen.remove(root)
        component: list[int] = []
        while stack:
            face_id = stack.pop()
            component.append(face_id)
            for neighbor in neighbors[face_id]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
        components.append(tuple(sorted(component)))
    return tuple(sorted(components, key=lambda component: (-len(component), component)))


@cache
def transverse_cutoff_one_fusion_audit() -> TransverseCutoffOneFusionAudit:
    """Expand all cutoff-one fusion families of the 21-face residual."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    leaf = transverse_leaf_reduction_audit()
    components = _residual_face_components(leaf.residual_core_faces)
    connected = tuple(component for component in components if len(component) > 1)
    decorations = tuple(component[0] for component in components if len(component) == 1)
    if len(connected) != 1:
        raise AssertionError("the transverse residual ceased to have one connected core")
    core = connected[0]

    selected_faces = {
        face_id
        for corridor in _corridor_face_ids()
        for face_id in corridor
    }
    free_links = set(complex_.free)
    protected_links = {
        link
        for face_id in selected_faces
        for link, _orientation in faces[face_id]
        if link in free_links
    }
    core_links = {
        link
        for face_id in core
        for link, _orientation in faces[face_id]
        if link in free_links
    }
    core_internal = tuple(sorted(core_links - protected_links))
    core_boundary = tuple(sorted(core_links & protected_links))
    internal_incidence = tuple(
        tuple(
            position
            for position, face_id in enumerate(core)
            if any(link == internal for link, _orientation in faces[face_id])
        )
        for internal in core_internal
    )
    boundary_incidence = tuple(
        tuple(
            position
            for position, face_id in enumerate(core)
            if any(link == boundary for link, _orientation in faces[face_id])
        )
        for boundary in core_boundary
    )
    if any(len(incident) != 3 for incident in internal_incidence):
        raise AssertionError("the connected transverse core lost trivalence")
    if any(len(incident) != 2 for incident in boundary_incidence):
        raise AssertionError("the connected transverse boundary lost bivalence")

    parity_profiles: Counter[tuple[int, ...]] = Counter()
    label_profiles: Counter[tuple[int, ...]] = Counter()
    profile_face_counts: defaultdict[tuple[int, ...], Counter[int]] = defaultdict(Counter)
    admissible_assignments = 0
    internal_multiplicity_one = True
    for mask in range(1 << len(core)):
        active = tuple(bool((mask >> position) & 1) for position in range(len(core)))
        internal_counts = tuple(
            sum(active[position] for position in incident)
            for incident in internal_incidence
        )
        if any(count not in (0, 2) for count in internal_counts):
            continue
        admissible_assignments += 1
        internal_multiplicity_one = (
            internal_multiplicity_one
            and all(
                invariant_multiplicity((1,) * count) == 1
                for count in internal_counts
            )
        )
        boundary_counts = tuple(
            sum(active[position] for position in incident)
            for incident in boundary_incidence
        )
        parity_profiles[tuple(count % 2 for count in boundary_counts)] += 1
        choices = tuple(
            (0,) if count == 0 else ((1,) if count == 1 else (0, 2))
            for count in boundary_counts
        )
        face_count = mask.bit_count()
        for profile in product(*choices):
            label_profiles[profile] += 1
            profile_face_counts[profile][face_count] += 1

    parity_multiplicities = set(parity_profiles.values())
    vacuum_profile = (0,) * len(core_boundary)
    decoration_link_sets = tuple(
        {
            link
            for link, _orientation in faces[face_id]
            if link in protected_links
        }
        for face_id in decorations
    )
    all_decoration_links = set().union(*decoration_link_sets)
    decoration_profiles = 1 << len(decorations)
    certificate = TransverseCutoffOneFusionAudit(
        representation_cutoff=1,
        connected_core_faces=core,
        decoration_faces=decorations,
        internal_trivalent_link_count=len(core_internal),
        core_protected_link_count=len(core_boundary),
        decoration_protected_link_count=len(all_decoration_links),
        decoration_protected_degree_census=tuple(
            sorted(Counter(map(len, decoration_link_sets)).items())
        ),
        protected_link_sets_pairwise_disjoint=(
            len(all_decoration_links) == sum(map(len, decoration_link_sets))
            and all_decoration_links.isdisjoint(core_boundary)
        ),
        binary_internal_admissible_assignments=admissible_assignments,
        binary_boundary_parity_profiles=len(parity_profiles),
        binary_fillings_per_parity_profile=(
            next(iter(parity_multiplicities))
            if len(parity_multiplicities) == 1
            else 0
        ),
        complete_core_boundary_label_profiles=len(label_profiles),
        complete_core_fusion_paths=sum(label_profiles.values()),
        core_profile_multiplicity_census=tuple(
            sorted(Counter(label_profiles.values()).items())
        ),
        core_profile_face_count_term_census=tuple(
            sorted(Counter(len(ledger) for ledger in profile_face_counts.values()).items())
        ),
        vacuum_profile_face_count_ledger=tuple(
            sorted(profile_face_counts[vacuum_profile].items())
        ),
        decoration_boundary_label_profiles=decoration_profiles,
        complete_residual_boundary_label_profiles=(
            len(label_profiles) * decoration_profiles
        ),
        complete_residual_fusion_paths=(
            sum(label_profiles.values()) * decoration_profiles
        ),
        residual_profile_multiplicity_census=tuple(
            (multiplicity, count * decoration_profiles)
            for multiplicity, count in sorted(Counter(label_profiles.values()).items())
        ),
        internal_intertwiner_multiplicity_one=internal_multiplicity_one,
        singlet_triplet_boundary_channels_retained=any(
            2 in profile for profile in label_profiles
        ),
        parity_only_boundary_carrier_refuted=(
            len(label_profiles) > len(parity_profiles)
        ),
        coherent_partial_haar_tensors_evaluated=(
            cutoff_one_loop_tensor_audit().validates()
        ),
        cp_order_domination_proved=False,
        all_label_completion_proved=False,
        first_open_obligation=(
            "evaluate-open-index-all-label-haar-amplitudes"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the cutoff-one transverse fusion ledger drifted")
    return certificate


@dataclass(frozen=True)
class GroupedPhysicalPacketFrontier:
    """Fail-closed verdict for promotion from a heat corridor to physical BF4."""

    all_label_corridor_kernel_constructed: bool
    exact_semigroup_grouping: bool
    common_haar_packet_constructed: bool
    common_packet_faithful_on_all_peter_weyl_labels: bool
    spacing_uniform_given_cumulative_heat_condition: bool
    cumulative_heat_condition_contains_rescaled_bare_mode_floor: bool
    nine_geometric_corridors_pinned: bool
    transverse_interaction_obstruction_pinned: bool
    transverse_leaf_reduction_pinned: bool
    transverse_cutoff_one_fusion_ledger_pinned: bool
    transverse_cutoff_one_coherent_loop_tensors_pinned: bool
    transverse_cutoff_one_complete_residual_tensors_pinned: bool
    transverse_arbitrary_cutoff_recoupling_carrier_pinned: bool
    transverse_arbitrary_cutoff_open_magnetic_tensors_pinned: bool
    transverse_cutoff_one_open_index_network_pinned: bool
    transverse_fixed_coupling_all_label_cauchy_modulus_pinned: bool
    transverse_fixed_coupling_operator_trace_tail_pinned: bool
    transverse_cutoff_one_weak_coupling_cp_obstruction_pinned: bool
    transverse_fixed_cutoff_weak_coupling_tail_obstruction_pinned: bool
    transverse_open_index_all_label_choi_reconstructed: bool
    basis_free_physical_all_label_source_target_choi_defined: bool
    direct_all_label_measure_regrouping_used: bool
    spacing_dependent_cutoff_schedule_pinned: bool
    fixed_coupling_physical_corridor_cp_domination_proved: bool
    spacing_uniform_physical_corridor_cp_domination_proved: bool
    finite_cutoff_choi_deweighting_pinned: bool
    normalized_random_unitary_residual_cptp_proved: bool
    projective_all_label_normal_channel_defined: bool
    abstract_same_carrier_convolution_composition_proved: bool
    microscopic_corridor_tag_fixed_distance_route_refuted: bool
    two_slab_fixed_spatial_fiber_product_geometry_pinned: bool
    independent_convolution_physical_gluing_refuted: bool
    interface_floor_ceiling_uniform_route_refuted: bool
    raw_fiber_product_transfer_composition_exact: bool
    boundary_message_markovization_algebra_proved: bool
    finite_horizon_mass_preserving_composition_algebra_proved: bool
    all_label_continuous_boundary_transfer_constructed: bool
    spacing_uniform_boundary_message_ratio_proved: bool
    fine_boundary_conditioned_gluing_channel_constructed: bool
    nine_slot_coarse_markov_intertwining_proved: bool
    nine_coarse_loop_raw_transfer_sufficiency_refuted: bool
    coarse_markov_lumpability_refuted: bool
    carrier_enlargement_or_conditional_cancellation_required: bool
    enlarged_fine_boundary_carrier_constructed: bool
    enlarged_boundary_gauge_fixed_cycle_rank: int
    enlarged_carrier_identity_markov_intertwining_proved: bool
    grouped_row_harnack_message_order_reduction_proved: bool
    endpoint_spatial_weight_cancellation_proved: bool
    kinetic_23_cycle_spacing_uniform_message_order_proved: bool
    kinetic_markov_common_mass: Fraction
    interior_spatial_feynman_kac_harnack_proved: bool
    uniform_positive_kernel_limit_message_order_criterion_proved: bool
    physical_grouped_feynman_kac_uniform_limit_proved: bool
    physical_limit_kernel_strictly_positive_proved: bool
    direct_integrated_glued_block_comparison_refuted: bool
    physical_consecutive_slab_rg_identification_proved: bool
    consecutive_scale_channel_composition_proved: bool
    corrected_slab_corridor_cover_pinned: bool
    interacting_map_cp_dominates_corridor: bool
    physical_coupling_spacing_condition_proved: bool
    actual_grouped_all_label_packet_proved: bool
    spacing_uniform_refresh_mass_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        witness = all_label_haar_floor_certificate(Fraction(9, 10))
        geometry = corrected_slab_corridor_geometry_audit()
        leaf_reduction = transverse_leaf_reduction_audit()
        fusion = transverse_cutoff_one_fusion_audit()
        loop_tensors = cutoff_one_loop_tensor_audit()
        residual_tensors = cutoff_one_residual_loop_tensor_audit()
        recoupling = transverse_recoupling_census(2)
        smaller_carrier = finite_cutoff_transverse_recoupling_carrier(1)
        larger_carrier = finite_cutoff_transverse_recoupling_carrier(2)
        magnetic_packet = transverse_magnetic_tensor_packet(1)
        open_index_network = cutoff_one_open_index_network()
        all_label_tail = transverse_all_label_uniform_tail(
            Fraction(1, 2),
            1,
        )
        operator_tail = transverse_residual_operator_tail(
            Fraction(1, 2),
            8,
            Fraction(1, 2),
            8,
        )
        cp_obstruction = cutoff_one_cp_order_audit()
        weak_coupling_tail_obstruction = (
            fixed_cutoff_weak_coupling_obstruction(2)
        )
        physical_choi = physical_all_label_choi_domination(
            Fraction(1, 2),
            Fraction(1, 2),
        )
        channel_promotion = mass_preserving_channel_promotion(
            Fraction(1, 2),
            Fraction(1, 2),
        )
        fixed_distance_no_go = dyadic_fixed_distance_iteration_no_go(2)
        gluing = two_slab_physical_gluing_audit()
        interface_no_go = interface_floor_ceiling_no_go(
            Fraction(3, 4),
            dyadic_spacing=True,
        )
        boundary_messages = physical_boundary_message_blueprint()
        message_order = physical_backward_message_order_frontier()
        return (
            witness.validates()
            and geometry.validates()
            and leaf_reduction.validates()
            and fusion.validates()
            and loop_tensors.validates()
            and residual_tensors.validates()
            and recoupling.validates()
            and smaller_carrier.embeds_into(larger_carrier)
            and magnetic_packet.validates()
            and open_index_network.validates()
            and all_label_tail.validates()
            and operator_tail.validates()
            and cp_obstruction.validates()
            and weak_coupling_tail_obstruction.validates()
            and physical_choi.validates()
            and channel_promotion.validates()
            and fixed_distance_no_go.validates()
            and gluing.validates()
            and interface_no_go.validates()
            and boundary_messages.validates()
            and message_order.validates()
            and self.all_label_corridor_kernel_constructed
            and self.exact_semigroup_grouping
            and self.common_haar_packet_constructed
            and self.common_packet_faithful_on_all_peter_weyl_labels
            and self.spacing_uniform_given_cumulative_heat_condition
            and self.cumulative_heat_condition_contains_rescaled_bare_mode_floor
            and self.nine_geometric_corridors_pinned
            and self.transverse_interaction_obstruction_pinned
            and self.transverse_leaf_reduction_pinned
            and self.transverse_cutoff_one_fusion_ledger_pinned
            and self.transverse_cutoff_one_coherent_loop_tensors_pinned
            and self.transverse_cutoff_one_complete_residual_tensors_pinned
            and self.transverse_arbitrary_cutoff_recoupling_carrier_pinned
            and self.transverse_arbitrary_cutoff_open_magnetic_tensors_pinned
            and self.transverse_cutoff_one_open_index_network_pinned
            and self.transverse_fixed_coupling_all_label_cauchy_modulus_pinned
            and self.transverse_fixed_coupling_operator_trace_tail_pinned
            and self.transverse_cutoff_one_weak_coupling_cp_obstruction_pinned
            and (
                self.transverse_fixed_cutoff_weak_coupling_tail_obstruction_pinned
            )
            and not self.transverse_open_index_all_label_choi_reconstructed
            and self.basis_free_physical_all_label_source_target_choi_defined
            and self.direct_all_label_measure_regrouping_used
            and self.spacing_dependent_cutoff_schedule_pinned
            and self.fixed_coupling_physical_corridor_cp_domination_proved
            and not self.spacing_uniform_physical_corridor_cp_domination_proved
            and self.finite_cutoff_choi_deweighting_pinned
            and self.normalized_random_unitary_residual_cptp_proved
            and self.projective_all_label_normal_channel_defined
            and self.abstract_same_carrier_convolution_composition_proved
            and self.microscopic_corridor_tag_fixed_distance_route_refuted
            and self.two_slab_fixed_spatial_fiber_product_geometry_pinned
            and self.independent_convolution_physical_gluing_refuted
            and self.interface_floor_ceiling_uniform_route_refuted
            and self.raw_fiber_product_transfer_composition_exact
            and self.boundary_message_markovization_algebra_proved
            and self.finite_horizon_mass_preserving_composition_algebra_proved
            and self.all_label_continuous_boundary_transfer_constructed
            and not self.spacing_uniform_boundary_message_ratio_proved
            and self.fine_boundary_conditioned_gluing_channel_constructed
            and not self.nine_slot_coarse_markov_intertwining_proved
            and self.nine_coarse_loop_raw_transfer_sufficiency_refuted
            and not self.coarse_markov_lumpability_refuted
            and self.carrier_enlargement_or_conditional_cancellation_required
            and self.enlarged_fine_boundary_carrier_constructed
            and self.enlarged_boundary_gauge_fixed_cycle_rank == 23
            and self.enlarged_carrier_identity_markov_intertwining_proved
            and self.grouped_row_harnack_message_order_reduction_proved
            and self.endpoint_spatial_weight_cancellation_proved
            and self.kinetic_23_cycle_spacing_uniform_message_order_proved
            and self.kinetic_markov_common_mass
            == Fraction(1055, 3489) ** 46
            and not self.interior_spatial_feynman_kac_harnack_proved
            and self.uniform_positive_kernel_limit_message_order_criterion_proved
            and not self.physical_grouped_feynman_kac_uniform_limit_proved
            and not self.physical_limit_kernel_strictly_positive_proved
            and not self.direct_integrated_glued_block_comparison_refuted
            and not self.physical_consecutive_slab_rg_identification_proved
            and not self.consecutive_scale_channel_composition_proved
            and geometry.every_internal_link_transversely_coupled
            and not geometry.literal_semigroup_factorization_of_full_integrand
            and not self.corrected_slab_corridor_cover_pinned
            and not self.interacting_map_cp_dominates_corridor
            and not self.physical_coupling_spacing_condition_proved
            and not self.actual_grouped_all_label_packet_proved
            and not self.spacing_uniform_refresh_mass_proved
            and self.first_open_obligation
            == "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        )


def grouped_physical_packet_frontier() -> GroupedPhysicalPacketFrontier:
    """Return the exact positive result and the remaining physical obstruction."""

    frontier = GroupedPhysicalPacketFrontier(
        all_label_corridor_kernel_constructed=True,
        exact_semigroup_grouping=True,
        common_haar_packet_constructed=True,
        common_packet_faithful_on_all_peter_weyl_labels=True,
        spacing_uniform_given_cumulative_heat_condition=True,
        cumulative_heat_condition_contains_rescaled_bare_mode_floor=True,
        nine_geometric_corridors_pinned=True,
        transverse_interaction_obstruction_pinned=True,
        transverse_leaf_reduction_pinned=True,
        transverse_cutoff_one_fusion_ledger_pinned=True,
        transverse_cutoff_one_coherent_loop_tensors_pinned=True,
        transverse_cutoff_one_complete_residual_tensors_pinned=True,
        transverse_arbitrary_cutoff_recoupling_carrier_pinned=True,
        transverse_arbitrary_cutoff_open_magnetic_tensors_pinned=True,
        transverse_cutoff_one_open_index_network_pinned=True,
        transverse_fixed_coupling_all_label_cauchy_modulus_pinned=True,
        transverse_fixed_coupling_operator_trace_tail_pinned=True,
        transverse_cutoff_one_weak_coupling_cp_obstruction_pinned=True,
        transverse_fixed_cutoff_weak_coupling_tail_obstruction_pinned=True,
        transverse_open_index_all_label_choi_reconstructed=False,
        basis_free_physical_all_label_source_target_choi_defined=True,
        direct_all_label_measure_regrouping_used=True,
        spacing_dependent_cutoff_schedule_pinned=True,
        fixed_coupling_physical_corridor_cp_domination_proved=True,
        spacing_uniform_physical_corridor_cp_domination_proved=False,
        finite_cutoff_choi_deweighting_pinned=True,
        normalized_random_unitary_residual_cptp_proved=True,
        projective_all_label_normal_channel_defined=True,
        abstract_same_carrier_convolution_composition_proved=True,
        microscopic_corridor_tag_fixed_distance_route_refuted=True,
        two_slab_fixed_spatial_fiber_product_geometry_pinned=True,
        independent_convolution_physical_gluing_refuted=True,
        interface_floor_ceiling_uniform_route_refuted=True,
        raw_fiber_product_transfer_composition_exact=True,
        boundary_message_markovization_algebra_proved=True,
        finite_horizon_mass_preserving_composition_algebra_proved=True,
        all_label_continuous_boundary_transfer_constructed=True,
        spacing_uniform_boundary_message_ratio_proved=False,
        fine_boundary_conditioned_gluing_channel_constructed=True,
        nine_slot_coarse_markov_intertwining_proved=False,
        nine_coarse_loop_raw_transfer_sufficiency_refuted=True,
        coarse_markov_lumpability_refuted=False,
        carrier_enlargement_or_conditional_cancellation_required=True,
        enlarged_fine_boundary_carrier_constructed=True,
        enlarged_boundary_gauge_fixed_cycle_rank=23,
        enlarged_carrier_identity_markov_intertwining_proved=True,
        grouped_row_harnack_message_order_reduction_proved=True,
        endpoint_spatial_weight_cancellation_proved=True,
        kinetic_23_cycle_spacing_uniform_message_order_proved=True,
        kinetic_markov_common_mass=Fraction(1055, 3489) ** 46,
        interior_spatial_feynman_kac_harnack_proved=False,
        uniform_positive_kernel_limit_message_order_criterion_proved=True,
        physical_grouped_feynman_kac_uniform_limit_proved=False,
        physical_limit_kernel_strictly_positive_proved=False,
        direct_integrated_glued_block_comparison_refuted=False,
        physical_consecutive_slab_rg_identification_proved=False,
        consecutive_scale_channel_composition_proved=False,
        corrected_slab_corridor_cover_pinned=False,
        interacting_map_cp_dominates_corridor=False,
        physical_coupling_spacing_condition_proved=False,
        actual_grouped_all_label_packet_proved=False,
        spacing_uniform_refresh_mass_proved=False,
        first_open_obligation=(
            "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        ),
    )
    if not frontier.validates():
        raise AssertionError("the grouped physical packet frontier drifted")
    return frontier
