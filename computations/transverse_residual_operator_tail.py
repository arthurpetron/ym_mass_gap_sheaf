"""Trace-class lift of the BF4 transverse residual cutoff modulus.

This module keeps two cutoffs separate.

``density_cutoff`` truncates the 21 heat-kernel factors used to approximate
the scalar transverse residual function.  That character truncation need
not be positive.

``feature_cutoff`` projects the *full positive residual measure* onto a
finite heat-weighted Peter--Weyl open-index carrier.  Compression of the
full positive Gram/Choi operator is positive semidefinite and therefore
remains completely positive whenever the physical source/target Choi
indexing has been supplied.

At fixed couplings, the scalar uniform residual modulus lifts to trace norm.
The finite feature compression also has an explicit trace-class tail,
including both coherent cross corners.  No bound here is uniform as either
heat coordinate tends to one, and the physical corrected-slab source/target
Choi operator is not reconstructed by this scalar-to-Gram lift.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.all_label_whole_slab_tail import (
    SinglePlaquetteAllLabelTail,
    rational_sqrt_upper,
    single_plaquette_all_label_tail,
)
from computations.transverse_all_label_tail import (
    PROTECTED_BOUNDARY_LINK_COUNT,
    TRANSVERSE_RESIDUAL_FACE_COUNT,
    TransverseAllLabelUniformTail,
    transverse_all_label_uniform_tail,
)


@dataclass(frozen=True)
class TransverseResidualOperatorTail:
    """Exact fixed-coupling Gram/Choi compression and cutoff-tail bounds."""

    density_coupling: Fraction
    density_cutoff: int
    feature_coupling: Fraction
    feature_cutoff: int
    density_tail: TransverseAllLabelUniformTail
    feature_tail: SinglePlaquetteAllLabelTail
    residual_face_count: int
    open_index_feature_slots: int
    full_residual_density_sup_upper: Fraction
    retained_one_slot_feature_norm_squared: Fraction
    full_one_slot_feature_norm_squared_upper: Fraction
    retained_feature_norm_squared: Fraction
    full_feature_norm_squared_upper: Fraction
    outside_feature_norm_squared_bound: Fraction
    density_tail_full_feature_trace_norm_bound: Fraction
    density_tail_compressed_trace_norm_bound: Fraction
    outside_diagonal_trace_norm_bound: Fraction
    cross_squared_bound: Fraction
    cross_trace_norm_bound: Fraction
    feature_compression_trace_norm_tail_bound: Fraction
    combined_finite_approximation_trace_norm_bound: Fraction
    combined_finite_approximation_operator_norm_bound: Fraction
    full_measure_gram_positive: bool
    finite_full_measure_compression_positive: bool
    finite_full_measure_choi_compression_cp: bool
    character_truncated_density_positivity_proved_by_tail: bool
    character_truncation_cp_inferred: bool
    fixed_coupling_trace_class_cauchy_name: bool
    orthogonal_intertwiner_projection_nonexpansive: bool
    unitary_recoupling_invariant: bool
    ambient_volume_independent: bool
    spacing_uniform_in_weak_coupling_limit: bool
    physical_source_target_choi_reconstructed: bool
    first_open_obligation: str

    def validates(self) -> bool:
        if (
            not self.density_tail.validates()
            or not self.feature_tail.validates()
            or self.density_coupling != self.density_tail.coupling
            or self.density_cutoff != self.density_tail.cutoff
            or self.feature_coupling != self.feature_tail.coupling
            or self.feature_cutoff != self.feature_tail.cutoff
        ):
            return False
        density_upper = (
            self.density_tail.one_face_sup_upper
            ** TRANSVERSE_RESIDUAL_FACE_COUNT
        )
        retained_one = self.feature_tail.partial_sum
        full_one = self.feature_tail.total_upper_bound
        retained = retained_one**PROTECTED_BOUNDARY_LINK_COUNT
        full = full_one**PROTECTED_BOUNDARY_LINK_COUNT
        outside = (
            PROTECTED_BOUNDARY_LINK_COUNT
            * full_one ** (PROTECTED_BOUNDARY_LINK_COUNT - 1)
            * self.feature_tail.tail_bound
        )
        density_full = (
            self.density_tail.residual_uniform_tail_bound * full
        )
        density_compressed = (
            self.density_tail.residual_uniform_tail_bound * retained
        )
        outside_diagonal = density_upper * outside
        cross_squared = (
            density_upper * density_upper * full * outside
        )
        cross = rational_sqrt_upper(cross_squared)
        feature_total = 2 * cross + outside_diagonal
        combined = density_compressed + feature_total
        return (
            self.residual_face_count == TRANSVERSE_RESIDUAL_FACE_COUNT == 21
            and self.open_index_feature_slots
            == PROTECTED_BOUNDARY_LINK_COUNT
            == 18
            and self.full_residual_density_sup_upper == density_upper
            and self.retained_one_slot_feature_norm_squared == retained_one
            and self.full_one_slot_feature_norm_squared_upper == full_one
            and self.retained_feature_norm_squared == retained
            and self.full_feature_norm_squared_upper == full
            and self.outside_feature_norm_squared_bound == outside
            and self.density_tail_full_feature_trace_norm_bound
            == density_full
            and self.density_tail_compressed_trace_norm_bound
            == density_compressed
            and self.outside_diagonal_trace_norm_bound == outside_diagonal
            and self.cross_squared_bound == cross_squared
            and self.cross_trace_norm_bound == cross
            and cross * cross >= cross_squared
            and self.feature_compression_trace_norm_tail_bound
            == feature_total
            and self.combined_finite_approximation_trace_norm_bound
            == combined
            and self.combined_finite_approximation_operator_norm_bound
            == combined
            and self.full_measure_gram_positive
            and self.finite_full_measure_compression_positive
            and self.finite_full_measure_choi_compression_cp
            and not self.character_truncated_density_positivity_proved_by_tail
            and not self.character_truncation_cp_inferred
            and self.fixed_coupling_trace_class_cauchy_name
            and self.orthogonal_intertwiner_projection_nonexpansive
            and self.unitary_recoupling_invariant
            and self.ambient_volume_independent
            and not self.spacing_uniform_in_weak_coupling_limit
            and not self.physical_source_target_choi_reconstructed
            and self.first_open_obligation
            == "assemble-all-label-source-target-choi-and-prove-cp-order"
        )


@cache
def transverse_residual_operator_tail(
    density_coupling: Fraction,
    density_cutoff: int,
    feature_coupling: Fraction,
    feature_cutoff: int,
) -> TransverseResidualOperatorTail:
    """Lift the scalar residual modulus to a finite open-index compression."""

    density = transverse_all_label_uniform_tail(
        density_coupling,
        density_cutoff,
    )
    feature = single_plaquette_all_label_tail(
        feature_coupling,
        feature_cutoff,
    )
    density_upper = (
        density.one_face_sup_upper**TRANSVERSE_RESIDUAL_FACE_COUNT
    )
    retained_one = feature.partial_sum
    full_one = feature.total_upper_bound
    retained = retained_one**PROTECTED_BOUNDARY_LINK_COUNT
    full = full_one**PROTECTED_BOUNDARY_LINK_COUNT
    outside = (
        PROTECTED_BOUNDARY_LINK_COUNT
        * full_one ** (PROTECTED_BOUNDARY_LINK_COUNT - 1)
        * feature.tail_bound
    )
    density_full = density.residual_uniform_tail_bound * full
    density_compressed = density.residual_uniform_tail_bound * retained
    outside_diagonal = density_upper * outside
    cross_squared = density_upper * density_upper * full * outside
    cross = rational_sqrt_upper(cross_squared)
    feature_total = 2 * cross + outside_diagonal
    combined = density_compressed + feature_total
    certificate = TransverseResidualOperatorTail(
        density_coupling=density_coupling,
        density_cutoff=density_cutoff,
        feature_coupling=feature_coupling,
        feature_cutoff=feature_cutoff,
        density_tail=density,
        feature_tail=feature,
        residual_face_count=TRANSVERSE_RESIDUAL_FACE_COUNT,
        open_index_feature_slots=PROTECTED_BOUNDARY_LINK_COUNT,
        full_residual_density_sup_upper=density_upper,
        retained_one_slot_feature_norm_squared=retained_one,
        full_one_slot_feature_norm_squared_upper=full_one,
        retained_feature_norm_squared=retained,
        full_feature_norm_squared_upper=full,
        outside_feature_norm_squared_bound=outside,
        density_tail_full_feature_trace_norm_bound=density_full,
        density_tail_compressed_trace_norm_bound=density_compressed,
        outside_diagonal_trace_norm_bound=outside_diagonal,
        cross_squared_bound=cross_squared,
        cross_trace_norm_bound=cross,
        feature_compression_trace_norm_tail_bound=feature_total,
        combined_finite_approximation_trace_norm_bound=combined,
        combined_finite_approximation_operator_norm_bound=combined,
        full_measure_gram_positive=True,
        finite_full_measure_compression_positive=True,
        finite_full_measure_choi_compression_cp=True,
        character_truncated_density_positivity_proved_by_tail=False,
        character_truncation_cp_inferred=False,
        fixed_coupling_trace_class_cauchy_name=True,
        orthogonal_intertwiner_projection_nonexpansive=True,
        unitary_recoupling_invariant=True,
        ambient_volume_independent=True,
        spacing_uniform_in_weak_coupling_limit=False,
        physical_source_target_choi_reconstructed=False,
        first_open_obligation=(
            "assemble-all-label-source-target-choi-and-prove-cp-order"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the transverse residual operator tail drifted")
    return certificate


@dataclass(frozen=True)
class OperatorTailCauchyStep:
    """A checked fixed-coupling cutoff pair below one rational tolerance."""

    density_coupling: Fraction
    feature_coupling: Fraction
    tolerance: Fraction
    density_cutoff: int
    feature_cutoff: int
    combined_trace_norm_bound: Fraction
    meets_tolerance: bool

    def validates(self) -> bool:
        if (
            not 0 < self.density_coupling < 1
            or not 0 < self.feature_coupling < 1
            or self.tolerance <= 0
            or self.density_cutoff < 0
            or self.feature_cutoff < 0
        ):
            return False
        certificate = transverse_residual_operator_tail(
            self.density_coupling,
            self.density_cutoff,
            self.feature_coupling,
            self.feature_cutoff,
        )
        return (
            self.combined_trace_norm_bound
            == certificate.combined_finite_approximation_trace_norm_bound
            and self.meets_tolerance
            == (self.combined_trace_norm_bound <= self.tolerance)
        )


def operator_tail_cauchy_step(
    density_coupling: Fraction,
    feature_coupling: Fraction,
    tolerance: Fraction,
    density_cutoff: int,
    feature_cutoff: int,
) -> OperatorTailCauchyStep:
    """Check one proposed pair of density and feature cutoffs."""

    if tolerance <= 0:
        raise ValueError("the operator-tail tolerance must be positive")
    certificate = transverse_residual_operator_tail(
        density_coupling,
        density_cutoff,
        feature_coupling,
        feature_cutoff,
    )
    step = OperatorTailCauchyStep(
        density_coupling=density_coupling,
        feature_coupling=feature_coupling,
        tolerance=tolerance,
        density_cutoff=density_cutoff,
        feature_cutoff=feature_cutoff,
        combined_trace_norm_bound=(
            certificate.combined_finite_approximation_trace_norm_bound
        ),
        meets_tolerance=(
            certificate.combined_finite_approximation_trace_norm_bound
            <= tolerance
        ),
    )
    if not step.validates():
        raise AssertionError("the operator-tail Cauchy step drifted")
    return step
