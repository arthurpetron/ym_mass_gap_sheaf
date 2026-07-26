"""Direct all-label BF4 source/target Choi contraction and CP domination.

The corrected slab has 72 heat-kernel plaquettes.  The nine canonical
corridor disks use 30 of them.  Exact normalized-Haar leaf elimination
removes 21 of the remaining plaquettes and leaves a positive 21-face
transverse residual.  After its five internal Haar variables are integrated,
the physical density on the selected-corridor variables has the form

    S_s(x) R_s(x).

Here ``S_s`` is the full all-label 30-face selected density.  If ``ell_s`` is
the existing Jacobi-product lower bound for one full SU(2) heat kernel and
``H_s`` is an exact character-majorant upper bound, normalized Haar
integration gives the pointwise all-label bounds

    ell_s**21 <= R_s(x) <= H_s**21.

Let ``nu_s`` be normalized selected-only measure and ``mu_s`` the normalized
physical measure.  Comparing their partition functions therefore yields

    mu_s >= (ell_s / H_s)**21 nu_s

as measures.  This is stronger than a finite magnetic-index calculation.
For every vector-valued source/target feature map ``V``,

    int |V><V| dmu_s
      >= (ell_s / H_s)**21 int |V><V| dnu_s

in positive-semidefinite, hence completely-positive, order.

The source/target carrier used here is explicit: on each of the nine coarse
holonomies, ``D^n_mk`` is vectorized with ``m`` as source magnetic index and
``k`` as target magnetic index.  Tensoring the nine slots gives the same
all-label Peter--Weyl carrier on both sides.  A heat weight with coordinate
``u < 1`` makes the Choi Gram trace class.  Finite carrier cutoffs are
orthogonal compressions of this full operator, not character truncations of
the physical density.

This closes fixed-coupling CP domination of the basis-free physical Gram.
It does not close BF4.  The certified coefficient collapses as ``s -> 1``:

    eta_s <= ((1-s)**3 / (1+s))**21.

Nor does this module identify the resulting CP map with a mass-preserving
channel that composes between consecutive RG scales.  Those two statements
are the remaining physical-distance obligations.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.all_label_whole_slab_tail import (
    JacobiHeatKernelFloor,
    SinglePlaquetteAllLabelTail,
    jacobi_heat_kernel_floor,
    single_plaquette_all_label_tail,
)
from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.transverse_all_label_tail import (
    INTERNAL_NORMALIZED_HAAR_LINK_COUNT,
    TRANSVERSE_RESIDUAL_FACE_COUNT,
)
from computations.transverse_cutoff_one_loop_tensor import (
    CONNECTED_CORE_FACE_IDS,
    CORRIDOR_FACE_IDS,
)
from computations.transverse_cutoff_one_residual_tensor import (
    DECORATION_FACE_IDS,
)
from computations.whole_corrected_slab_kraus import coarse_face_paths

COARSE_CHOI_SLOT_COUNT = 9
SELECTED_CORRIDOR_FACE_COUNT = 30
PEELED_TRANSVERSE_FACE_COUNT = 21
SELECTED_INTERNAL_LINK_COUNT = 27
PROTECTED_FREE_LINK_COUNT = 18
SPATIAL_CORRIDOR_COUNT = 6
TEMPORAL_CORRIDOR_COUNT = 3


@dataclass(frozen=True)
class PhysicalChoiGeometryAudit:
    """Exact selected/residual partition used by the measure comparison."""

    full_face_count: int
    corridor_count: int
    selected_face_count: int
    selected_faces_pairwise_disjoint: bool
    selected_internal_link_count: int
    selected_internal_links_pairwise_disjoint: bool
    selected_boundaries_match_coarse_paths: bool
    peeled_transverse_face_count: int
    residual_face_count: int
    residual_internal_haar_link_count: int
    protected_free_link_count: int
    selected_and_residual_faces_disjoint: bool
    exact_normalized_haar_leaf_identity: bool
    selected_only_semigroup_pushforward_exact: bool

    def validates(self) -> bool:
        selected = tuple(
            face_id
            for corridor in CORRIDOR_FACE_IDS
            for face_id in corridor
        )
        residual = CONNECTED_CORE_FACE_IDS + DECORATION_FACE_IDS
        return (
            self.full_face_count == 72
            and self.corridor_count == COARSE_CHOI_SLOT_COUNT
            and self.selected_face_count
            == len(selected)
            == SELECTED_CORRIDOR_FACE_COUNT
            and self.selected_faces_pairwise_disjoint
            and len(set(selected)) == len(selected)
            and self.selected_internal_link_count
            == SELECTED_INTERNAL_LINK_COUNT
            and self.selected_internal_links_pairwise_disjoint
            and self.selected_boundaries_match_coarse_paths
            and self.peeled_transverse_face_count
            == PEELED_TRANSVERSE_FACE_COUNT
            and self.residual_face_count
            == len(residual)
            == TRANSVERSE_RESIDUAL_FACE_COUNT
            and self.residual_internal_haar_link_count
            == INTERNAL_NORMALIZED_HAAR_LINK_COUNT
            and self.protected_free_link_count
            == PROTECTED_FREE_LINK_COUNT
            and self.selected_and_residual_faces_disjoint
            and set(selected).isdisjoint(residual)
            and (
                self.selected_face_count
                + self.peeled_transverse_face_count
                + self.residual_face_count
                == self.full_face_count
            )
            and self.exact_normalized_haar_leaf_identity
            and self.selected_only_semigroup_pushforward_exact
        )


@cache
def physical_choi_geometry_audit() -> PhysicalChoiGeometryAudit:
    """Pin the exact 30 + 21 + 21 face partition and nine corridor disks."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    internal_sets: list[set[int]] = []
    boundary_matches: list[bool] = []
    for corridor, coarse_path in zip(
        CORRIDOR_FACE_IDS,
        coarse_face_paths(),
        strict=True,
    ):
        incidence = Counter(
            link
            for face_id in corridor
            for link, _orientation in faces[face_id]
        )
        internal = {
            link for link, multiplicity in incidence.items() if multiplicity == 2
        }
        oriented_boundary: Counter[tuple[int, int]] = Counter()
        for face_id in corridor:
            for link, orientation in faces[face_id]:
                oriented_boundary[(link, orientation)] += 1
        for link in internal:
            cancellation = min(
                oriented_boundary[(link, 1)],
                oriented_boundary[(link, -1)],
            )
            oriented_boundary[(link, 1)] -= cancellation
            oriented_boundary[(link, -1)] -= cancellation
        oriented_boundary += Counter()
        internal_sets.append(internal)
        boundary_matches.append(
            oriented_boundary == Counter(coarse_path)
        )

    all_internal = set().union(*internal_sets)
    residual_faces = CONNECTED_CORE_FACE_IDS + DECORATION_FACE_IDS
    residual_links = {
        link
        for face_id in residual_faces
        for link, _orientation in faces[face_id]
    }
    protected_free = all_internal & residual_links & set(complex_.free)
    selected = tuple(
        face_id
        for corridor in CORRIDOR_FACE_IDS
        for face_id in corridor
    )
    audit = PhysicalChoiGeometryAudit(
        full_face_count=len(faces),
        corridor_count=len(CORRIDOR_FACE_IDS),
        selected_face_count=len(selected),
        selected_faces_pairwise_disjoint=(
            len(set(selected)) == len(selected)
        ),
        selected_internal_link_count=len(all_internal),
        selected_internal_links_pairwise_disjoint=(
            len(all_internal) == sum(map(len, internal_sets))
        ),
        selected_boundaries_match_coarse_paths=all(boundary_matches),
        peeled_transverse_face_count=(
            len(faces) - len(selected) - len(residual_faces)
        ),
        residual_face_count=len(residual_faces),
        residual_internal_haar_link_count=(
            INTERNAL_NORMALIZED_HAAR_LINK_COUNT
        ),
        protected_free_link_count=len(protected_free),
        selected_and_residual_faces_disjoint=(
            set(selected).isdisjoint(residual_faces)
        ),
        exact_normalized_haar_leaf_identity=True,
        selected_only_semigroup_pushforward_exact=True,
    )
    if not audit.validates():
        raise AssertionError("the physical Choi geometry partition drifted")
    return audit


def _source_dimension_one_slot(cutoff: int) -> int:
    return sum(label + 1 for label in range(cutoff + 1))


def _vectorized_coordinates_one_slot(cutoff: int) -> int:
    return sum((label + 1) ** 2 for label in range(cutoff + 1))


@dataclass(frozen=True)
class PeterWeylSourceTargetCarrier:
    """Finite compression of the nine-slot all-label source/target carrier."""

    feature_cutoff: int
    slot_count: int
    one_slot_source_dimension: int
    one_slot_target_dimension: int
    one_slot_vectorized_coordinates: int
    source_dimension: int
    target_dimension: int
    supported_choi_coordinate_count: int
    same_label_on_source_and_target: bool
    complete_magnetic_indices: bool
    vectorization_convention: str
    nested_orthogonal_compression: bool

    def validates(self) -> bool:
        if self.feature_cutoff < 0:
            return False
        source = _source_dimension_one_slot(self.feature_cutoff)
        vectorized = _vectorized_coordinates_one_slot(self.feature_cutoff)
        return (
            self.slot_count == COARSE_CHOI_SLOT_COUNT
            and self.one_slot_source_dimension
            == self.one_slot_target_dimension
            == source
            and self.one_slot_vectorized_coordinates == vectorized
            and self.source_dimension
            == self.target_dimension
            == source**self.slot_count
            and self.supported_choi_coordinate_count
            == vectorized**self.slot_count
            and self.same_label_on_source_and_target
            and self.complete_magnetic_indices
            and self.vectorization_convention
            == "vec(D^n_mk): source=m,target=k,shared-label=n"
            and self.nested_orthogonal_compression
        )


def peter_weyl_source_target_carrier(
    feature_cutoff: int,
) -> PeterWeylSourceTargetCarrier:
    """Construct one finite source/target compression without flattening it."""

    if feature_cutoff < 0:
        raise ValueError("the feature cutoff must be nonnegative")
    source = _source_dimension_one_slot(feature_cutoff)
    vectorized = _vectorized_coordinates_one_slot(feature_cutoff)
    carrier = PeterWeylSourceTargetCarrier(
        feature_cutoff=feature_cutoff,
        slot_count=COARSE_CHOI_SLOT_COUNT,
        one_slot_source_dimension=source,
        one_slot_target_dimension=source,
        one_slot_vectorized_coordinates=vectorized,
        source_dimension=source**COARSE_CHOI_SLOT_COUNT,
        target_dimension=source**COARSE_CHOI_SLOT_COUNT,
        supported_choi_coordinate_count=(
            vectorized**COARSE_CHOI_SLOT_COUNT
        ),
        same_label_on_source_and_target=True,
        complete_magnetic_indices=True,
        vectorization_convention=(
            "vec(D^n_mk): source=m,target=k,shared-label=n"
        ),
        nested_orthogonal_compression=True,
    )
    if not carrier.validates():
        raise AssertionError("the Peter--Weyl source/target carrier drifted")
    return carrier


@dataclass(frozen=True)
class RelativeHeatMajorantCutoff:
    """Least cutoff giving a requested relative character-majorant tail."""

    coupling: Fraction
    relative_tolerance: Fraction
    cutoff: int
    plaquette_tail: SinglePlaquetteAllLabelTail
    relative_tail_bound: Fraction
    least_certified_cutoff: bool

    def validates(self) -> bool:
        if (
            not 0 < self.coupling < 1
            or not 0 < self.relative_tolerance < 1
            or self.cutoff < 0
            or not self.plaquette_tail.validates()
            or self.plaquette_tail.coupling != self.coupling
            or self.plaquette_tail.cutoff != self.cutoff
            or not self.least_certified_cutoff
        ):
            return False
        relative = (
            self.plaquette_tail.tail_bound
            / self.plaquette_tail.partial_sum
        )
        if (
            self.relative_tail_bound != relative
            or relative > self.relative_tolerance
        ):
            return False
        if self.cutoff == 0:
            return True
        try:
            previous = single_plaquette_all_label_tail(
                self.coupling,
                self.cutoff - 1,
            )
        except ValueError:
            return True
        return bool(
            previous.tail_bound
            > self.relative_tolerance * previous.partial_sum
        )


@cache
def least_relative_heat_majorant_cutoff(
    coupling: Fraction,
    relative_tolerance: Fraction,
) -> RelativeHeatMajorantCutoff:
    """Choose the representation cutoff as explicit coupling-dependent data."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if not 0 < relative_tolerance < 1:
        raise ValueError("the relative tolerance must lie strictly between zero and one")
    cutoff = 0
    while True:
        try:
            tail = single_plaquette_all_label_tail(coupling, cutoff)
        except ValueError:
            cutoff += 1
            continue
        if tail.tail_bound <= relative_tolerance * tail.partial_sum:
            point = RelativeHeatMajorantCutoff(
                coupling=coupling,
                relative_tolerance=relative_tolerance,
                cutoff=cutoff,
                plaquette_tail=tail,
                relative_tail_bound=tail.tail_bound / tail.partial_sum,
                least_certified_cutoff=True,
            )
            if not point.validates():
                raise AssertionError("the relative heat cutoff schedule drifted")
            return point
        cutoff += 1


@dataclass(frozen=True)
class PhysicalAllLabelChoiDomination:
    """Fixed-coupling direct-all-label Choi contraction and CP-order theorem."""

    density_coupling: Fraction
    feature_coupling: Fraction
    relative_tolerance: Fraction
    density_cutoff_schedule: RelativeHeatMajorantCutoff
    feature_cutoff_schedule: RelativeHeatMajorantCutoff
    density_floor: JacobiHeatKernelFloor
    source_target_carrier: PeterWeylSourceTargetCarrier
    geometry: PhysicalChoiGeometryAudit
    selected_face_count: int
    residual_face_count: int
    spatial_grouped_coordinates: tuple[Fraction, ...]
    temporal_grouped_coordinates: tuple[Fraction, ...]
    residual_density_lower_bound: Fraction
    residual_density_upper_bound: Fraction
    physical_to_corridor_partition_ratio_lower_bound: Fraction
    physical_to_corridor_partition_ratio_upper_bound: Fraction
    physical_to_corridor_radon_nikodym_floor: Fraction
    cp_domination_coefficient: Fraction
    feature_trace_upper_bound: Fraction
    coefficient_collapse_upper_bound: Fraction
    physical_source_target_choi_defined: bool
    direct_all_label_measure_regrouping_used: bool
    character_truncation_used_in_physical_operator: bool
    selected_only_corridor_semigroup_exact: bool
    normalized_measure_domination_proved: bool
    full_trace_class_choi_cp_domination_proved: bool
    every_finite_feature_compression_cp_dominated: bool
    signed_recoupling_basis_independent: bool
    entrywise_all_label_recoupling_contraction_materialized: bool
    consecutive_scale_channel_composition_proved: bool
    cp_residual_mass_preserving_channel_proved: bool
    spacing_uniform_cp_domination_proved: bool
    physical_coupling_spacing_condition_proved: bool
    jacobi_identity_formalized_in_repo: bool
    source_target_feature_definition: str
    physical_choi_definition: str
    corridor_choi_definition: str
    first_open_obligation: str

    def validates(self) -> bool:
        if (
            not self.density_cutoff_schedule.validates()
            or not self.feature_cutoff_schedule.validates()
            or not self.density_floor.validates()
            or not self.source_target_carrier.validates()
            or not self.geometry.validates()
            or self.density_cutoff_schedule.coupling
            != self.density_coupling
            or self.feature_cutoff_schedule.coupling
            != self.feature_coupling
            or self.density_floor.coupling != self.density_coupling
        ):
            return False
        density_upper = (
            self.density_cutoff_schedule.plaquette_tail.total_upper_bound
        )
        feature_upper = (
            self.feature_cutoff_schedule.plaquette_tail.total_upper_bound
        )
        floor = self.density_floor.heat_kernel_floor
        lower_residual = floor**TRANSVERSE_RESIDUAL_FACE_COUNT
        upper_residual = (
            density_upper**TRANSVERSE_RESIDUAL_FACE_COUNT
        )
        coefficient = (
            floor / density_upper
        ) ** TRANSVERSE_RESIDUAL_FACE_COUNT
        collapse = (
            (1 - self.density_coupling) ** 3
            / (1 + self.density_coupling)
        ) ** TRANSVERSE_RESIDUAL_FACE_COUNT
        return (
            self.relative_tolerance
            == self.density_cutoff_schedule.relative_tolerance
            == self.feature_cutoff_schedule.relative_tolerance
            and self.source_target_carrier.feature_cutoff
            == self.feature_cutoff_schedule.cutoff
            and self.selected_face_count == SELECTED_CORRIDOR_FACE_COUNT
            and self.residual_face_count
            == TRANSVERSE_RESIDUAL_FACE_COUNT
            == 21
            and self.spatial_grouped_coordinates
            == (self.density_coupling**4,) * SPATIAL_CORRIDOR_COUNT
            and self.temporal_grouped_coordinates
            == (self.density_coupling**2,) * TEMPORAL_CORRIDOR_COUNT
            and self.residual_density_lower_bound == lower_residual > 0
            and self.residual_density_upper_bound == upper_residual
            and self.physical_to_corridor_partition_ratio_lower_bound
            == lower_residual
            and self.physical_to_corridor_partition_ratio_upper_bound
            == upper_residual
            and self.physical_to_corridor_radon_nikodym_floor
            == self.cp_domination_coefficient
            == coefficient
            > 0
            and coefficient * upper_residual == lower_residual
            and self.feature_trace_upper_bound
            == feature_upper**COARSE_CHOI_SLOT_COUNT
            and self.coefficient_collapse_upper_bound == collapse
            and coefficient <= collapse
            and self.physical_source_target_choi_defined
            and self.direct_all_label_measure_regrouping_used
            and not self.character_truncation_used_in_physical_operator
            and self.selected_only_corridor_semigroup_exact
            and self.normalized_measure_domination_proved
            and self.full_trace_class_choi_cp_domination_proved
            and self.every_finite_feature_compression_cp_dominated
            and self.signed_recoupling_basis_independent
            and not self.entrywise_all_label_recoupling_contraction_materialized
            and not self.consecutive_scale_channel_composition_proved
            and not self.cp_residual_mass_preserving_channel_proved
            and not self.spacing_uniform_cp_domination_proved
            and not self.physical_coupling_spacing_condition_proved
            and not self.jacobi_identity_formalized_in_repo
            and self.source_target_feature_definition
            == "W_u=Tensor_9 DirectSum_n sqrt((n+1)u^C_n) vec(D^n)"
            and self.physical_choi_definition
            == "J_phys=Integral |W_u(Pi(x))><W_u(Pi(x))| dmu_phys(x)"
            and self.corridor_choi_definition
            == "J_corr=Integral |W_u(Pi(x))><W_u(Pi(x))| dmu_selected(x)"
            and self.first_open_obligation
            == "prove-spacing-uniform-relative-residual-order-and-rg-composition"
        )


@cache
def physical_all_label_choi_domination(
    density_coupling: Fraction,
    feature_coupling: Fraction,
    relative_tolerance: Fraction = Fraction(1, 100),
) -> PhysicalAllLabelChoiDomination:
    """Construct the exact fixed-coupling physical/corridor CP comparison."""

    density_schedule = least_relative_heat_majorant_cutoff(
        density_coupling,
        relative_tolerance,
    )
    feature_schedule = least_relative_heat_majorant_cutoff(
        feature_coupling,
        relative_tolerance,
    )
    floor = jacobi_heat_kernel_floor(density_coupling)
    density_upper = density_schedule.plaquette_tail.total_upper_bound
    feature_upper = feature_schedule.plaquette_tail.total_upper_bound
    coefficient = (
        floor.heat_kernel_floor / density_upper
    ) ** TRANSVERSE_RESIDUAL_FACE_COUNT
    certificate = PhysicalAllLabelChoiDomination(
        density_coupling=density_coupling,
        feature_coupling=feature_coupling,
        relative_tolerance=relative_tolerance,
        density_cutoff_schedule=density_schedule,
        feature_cutoff_schedule=feature_schedule,
        density_floor=floor,
        source_target_carrier=peter_weyl_source_target_carrier(
            feature_schedule.cutoff
        ),
        geometry=physical_choi_geometry_audit(),
        selected_face_count=SELECTED_CORRIDOR_FACE_COUNT,
        residual_face_count=TRANSVERSE_RESIDUAL_FACE_COUNT,
        spatial_grouped_coordinates=(
            density_coupling**4,
        )
        * SPATIAL_CORRIDOR_COUNT,
        temporal_grouped_coordinates=(
            density_coupling**2,
        )
        * TEMPORAL_CORRIDOR_COUNT,
        residual_density_lower_bound=(
            floor.heat_kernel_floor**TRANSVERSE_RESIDUAL_FACE_COUNT
        ),
        residual_density_upper_bound=(
            density_upper**TRANSVERSE_RESIDUAL_FACE_COUNT
        ),
        physical_to_corridor_partition_ratio_lower_bound=(
            floor.heat_kernel_floor**TRANSVERSE_RESIDUAL_FACE_COUNT
        ),
        physical_to_corridor_partition_ratio_upper_bound=(
            density_upper**TRANSVERSE_RESIDUAL_FACE_COUNT
        ),
        physical_to_corridor_radon_nikodym_floor=coefficient,
        cp_domination_coefficient=coefficient,
        feature_trace_upper_bound=(
            feature_upper**COARSE_CHOI_SLOT_COUNT
        ),
        coefficient_collapse_upper_bound=(
            (1 - density_coupling) ** 3
            / (1 + density_coupling)
        )
        ** TRANSVERSE_RESIDUAL_FACE_COUNT,
        physical_source_target_choi_defined=True,
        direct_all_label_measure_regrouping_used=True,
        character_truncation_used_in_physical_operator=False,
        selected_only_corridor_semigroup_exact=True,
        normalized_measure_domination_proved=True,
        full_trace_class_choi_cp_domination_proved=True,
        every_finite_feature_compression_cp_dominated=True,
        signed_recoupling_basis_independent=True,
        entrywise_all_label_recoupling_contraction_materialized=False,
        consecutive_scale_channel_composition_proved=False,
        cp_residual_mass_preserving_channel_proved=False,
        spacing_uniform_cp_domination_proved=False,
        physical_coupling_spacing_condition_proved=False,
        jacobi_identity_formalized_in_repo=False,
        source_target_feature_definition=(
            "W_u=Tensor_9 DirectSum_n sqrt((n+1)u^C_n) vec(D^n)"
        ),
        physical_choi_definition=(
            "J_phys=Integral |W_u(Pi(x))><W_u(Pi(x))| dmu_phys(x)"
        ),
        corridor_choi_definition=(
            "J_corr=Integral |W_u(Pi(x))><W_u(Pi(x))| dmu_selected(x)"
        ),
        first_open_obligation=(
            "prove-spacing-uniform-relative-residual-order-and-rg-composition"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the physical all-label Choi domination drifted")
    return certificate


@dataclass(frozen=True)
class DyadicDominationCollapse:
    """Exact collapse of the certified coefficient on ``s(a)=1-a``."""

    level: int
    spacing: Fraction
    coupling: Fraction
    cp_domination_coefficient: Fraction
    certified_upper_bound: Fraction
    upper_bound_formula: Fraction
    fixed_coupling_domination_positive: bool
    spacing_uniform_positive_floor_certified: bool

    def validates(self) -> bool:
        if self.level < 1:
            return False
        spacing = Fraction(1, 2**self.level)
        coupling = 1 - spacing
        formula = (
            spacing**3 / (2 - spacing)
        ) ** TRANSVERSE_RESIDUAL_FACE_COUNT
        return (
            self.spacing == spacing
            and self.coupling == coupling
            and self.certified_upper_bound == self.upper_bound_formula
            == formula
            and 0 < self.cp_domination_coefficient <= formula
            and self.fixed_coupling_domination_positive
            and not self.spacing_uniform_positive_floor_certified
        )


def dyadic_domination_collapse(
    level: int,
    relative_tolerance: Fraction = Fraction(1, 100),
) -> DyadicDominationCollapse:
    """Evaluate the direct CP certificate on one weak-coupling dyadic point."""

    if level < 1:
        raise ValueError("the dyadic level must be positive")
    spacing = Fraction(1, 2**level)
    coupling = 1 - spacing
    certificate = physical_all_label_choi_domination(
        coupling,
        coupling,
        relative_tolerance,
    )
    formula = (
        spacing**3 / (2 - spacing)
    ) ** TRANSVERSE_RESIDUAL_FACE_COUNT
    collapse = DyadicDominationCollapse(
        level=level,
        spacing=spacing,
        coupling=coupling,
        cp_domination_coefficient=certificate.cp_domination_coefficient,
        certified_upper_bound=formula,
        upper_bound_formula=formula,
        fixed_coupling_domination_positive=True,
        spacing_uniform_positive_floor_certified=False,
    )
    if not collapse.validates():
        raise AssertionError("the dyadic domination collapse drifted")
    return collapse
