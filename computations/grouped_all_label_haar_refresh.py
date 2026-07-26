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

from computations.all_label_whole_slab_tail import (
    heat_character_sup_term,
    single_plaquette_all_label_tail,
)
from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.dual_positivity_geometry_bridge import edges_of
from computations.exact_haar_network import casimir4
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
    return coupling**steps


def heat_mode_multiplier(coupling: Fraction, steps: int, label: int) -> Fraction:
    """Return one exact all-label multiplier after grouping."""

    if label < 0:
        raise ValueError("a doubled SU(2) label must be nonnegative")
    return grouped_heat_coordinate(coupling, steps) ** casimir4(label)


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
class CumulativeHeatGapWitness:
    """Show that the grouped-half condition already contains a gap-scale floor."""

    spacing: Fraction
    physical_distance: Fraction
    microscopic_coupling: Fraction
    grouped_steps: int
    fundamental_separator: Fraction
    grouped_separator: Fraction
    lattice_margin: Fraction
    lattice_margin_lower: Fraction
    physical_margin: Fraction
    physical_margin_lower: Fraction
    fixed_distance_floor: Fraction | None

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
        physical_margin = lattice_margin / self.spacing
        physical_lower = lattice_lower / self.spacing
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
            and self.physical_margin == physical_margin >= physical_lower
            and self.physical_margin_lower == physical_lower
            and steps * self.spacing
            <= self.physical_distance + self.spacing
            and self.fixed_distance_floor == fixed_floor
            and (
                fixed_floor is None
                or physical_margin >= physical_lower >= fixed_floor
            )
        )


def cumulative_heat_gap_witness(
    certificate: FixedDistanceCorridorCertificate,
) -> CumulativeHeatGapWitness:
    """Derive a physical fundamental-mode margin from grouped heat mixing.

    If ``s**m <= 1/2``, then the fundamental separator satisfies
    ``(s**3)**m <= 1/8``.  The exact Bernoulli inequality

        1 - rho**m <= m * (1 - rho)

    therefore yields ``1 - rho >= 7/(8m)``.  With
    ``m = ceil(L/a)`` and ``a <= L``, this gives the spacing-uniform floor
    ``(1-rho)/a >= 7/(16L)``.  Thus the cumulative-heat premise is already a
    quantitative version of the physical gap-scale input; it is not a free
    consequence of grouping.
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
    witness = CumulativeHeatGapWitness(
        spacing=certificate.spacing,
        physical_distance=certificate.physical_distance,
        microscopic_coupling=certificate.microscopic_coupling,
        grouped_steps=steps,
        fundamental_separator=separator,
        grouped_separator=grouped_separator,
        lattice_margin=1 - separator,
        lattice_margin_lower=lattice_lower,
        physical_margin=(1 - separator) / certificate.spacing,
        physical_margin_lower=physical_lower,
        fixed_distance_floor=(
            Fraction(7, 16) / certificate.physical_distance
            if certificate.spacing <= certificate.physical_distance
            else None
        ),
    )
    if not witness.validates():
        raise AssertionError("the cumulative-heat gap witness drifted")
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
                    face_ids.append(
                        face_index[(tuple(point), (first, second))]
                    )
            corridors.append(tuple(face_ids))
    for direction in range(3):
        face_ids = []
        for offset in range(2):
            point = [0, 0, 0, 0]
            point[direction] += offset
            face_ids.append(
                face_index[(tuple(point), (direction, 3))]
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
class GroupedPhysicalPacketFrontier:
    """Fail-closed verdict for promotion from a heat corridor to physical BF4."""

    all_label_corridor_kernel_constructed: bool
    exact_semigroup_grouping: bool
    common_haar_packet_constructed: bool
    common_packet_faithful_on_all_peter_weyl_labels: bool
    spacing_uniform_given_cumulative_heat_condition: bool
    cumulative_heat_condition_contains_gap_scale_floor: bool
    nine_geometric_corridors_pinned: bool
    transverse_interaction_obstruction_pinned: bool
    transverse_leaf_reduction_pinned: bool
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
        return (
            witness.validates()
            and geometry.validates()
            and leaf_reduction.validates()
            and self.all_label_corridor_kernel_constructed
            and self.exact_semigroup_grouping
            and self.common_haar_packet_constructed
            and self.common_packet_faithful_on_all_peter_weyl_labels
            and self.spacing_uniform_given_cumulative_heat_condition
            and self.cumulative_heat_condition_contains_gap_scale_floor
            and self.nine_geometric_corridors_pinned
            and self.transverse_interaction_obstruction_pinned
            and self.transverse_leaf_reduction_pinned
            and geometry.every_internal_link_transversely_coupled
            and not geometry.literal_semigroup_factorization_of_full_integrand
            and not self.corrected_slab_corridor_cover_pinned
            and not self.interacting_map_cp_dominates_corridor
            and not self.physical_coupling_spacing_condition_proved
            and not self.actual_grouped_all_label_packet_proved
            and not self.spacing_uniform_refresh_mass_proved
            and self.first_open_obligation
            == "expand-21-face-transverse-core-and-prove-cp-order-domination"
        )


def grouped_physical_packet_frontier() -> GroupedPhysicalPacketFrontier:
    """Return the exact positive result and the remaining physical obstruction."""

    frontier = GroupedPhysicalPacketFrontier(
        all_label_corridor_kernel_constructed=True,
        exact_semigroup_grouping=True,
        common_haar_packet_constructed=True,
        common_packet_faithful_on_all_peter_weyl_labels=True,
        spacing_uniform_given_cumulative_heat_condition=True,
        cumulative_heat_condition_contains_gap_scale_floor=True,
        nine_geometric_corridors_pinned=True,
        transverse_interaction_obstruction_pinned=True,
        transverse_leaf_reduction_pinned=True,
        corrected_slab_corridor_cover_pinned=False,
        interacting_map_cp_dominates_corridor=False,
        physical_coupling_spacing_condition_proved=False,
        actual_grouped_all_label_packet_proved=False,
        spacing_uniform_refresh_mass_proved=False,
        first_open_obligation=(
            "expand-21-face-transverse-core-and-prove-cp-order-domination"
        ),
    )
    if not frontier.validates():
        raise AssertionError("the grouped physical packet frontier drifted")
    return frontier
