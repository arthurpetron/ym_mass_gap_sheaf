"""Regression tests for the corrected-slab CD-2 subgate ledger."""

from fractions import Fraction

from computations.compact_dual_cd2_frontier import (
    CD2_LEAN_THEOREMS,
    CD2Subgate,
    current_cd2_frontier,
)


def test_finite_remainder_algebra_is_closed() -> None:
    frontier = current_cd2_frontier()
    assert frontier.normalized_slab_laws
    assert frontier.zero_mass_remainder_derived
    assert frontier.universal_l1_cap == Fraction(2)
    assert frontier.finite_remainder_algebra_closed()


def test_first_open_subgate_is_coarse_recoupling_coherence() -> None:
    frontier = current_cd2_frontier()
    assert frontier.local_fusion_kernel
    assert frontier.closed_component
    assert frontier.separated_composition
    assert frontier.overlapping_carrier_correction
    assert frontier.cutoff_one_overlap_kernel
    assert frontier.all_cutoff_shared_face_recoupling
    assert frontier.overlapping_link_assembly
    assert frontier.overlap_reflection_intertwining
    assert frontier.restricted_source_coverage_refuted
    assert frontier.general_source_kernel
    assert frontier.fine_intertwiner_witness
    assert frontier.whole_slab_raw_carrier
    assert frontier.cutoff_one_coarse_face_door
    assert frontier.cutoff_one_coarse_link_door
    assert frontier.cutoff_one_global_coherent_target
    assert not frontier.coarse_recoupling_coherence
    assert (
        frontier.first_open_subgate()
        is CD2Subgate.COARSE_RECOUPLING_COHERENCE
    )
    assert not frontier.physical_cd2_closed()
    assert not frontier.cd3_smallness_closed()


def test_theorem_surface_pins_normalization_and_uniform_fence() -> None:
    assert (
        "Z4AdjacentCubeCancellationActivity."
        "zeroXAxisCancelledRoot_canonicalSurfaceActivity_eqv_pow_ten"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeCancellationActivity."
        "independent_cube_power_eqv_shared_face_square_mul_cancelled"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeCancellationConditionalKernel."
        "adjacentCubeConditionalKernel_row_normalized"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeCancellationConditionalKernel."
        "adjacentCubeConditionalKernel_detailed_balance"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeCancellationConditionalKernel."
        "adjacentCubeConditionalKernel_anchor_source_dependent"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeSharedFaceRecouplingKernel."
        "adjacentCubeSharedFaceConditionalKernel_row_normalized"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeSharedFaceRecouplingKernel."
        "adjacentCubeSharedFaceConditionalKernel_reflection"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeSharedFaceRecouplingKernel."
        "adjacentCubeSharedFaceConditionalKernel_source_dependent"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeJointConditionalKernel."
        "adjacentCubeJointConditionalKernel_row_normalized"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeJointConditionalKernel."
        "adjacentCubeJointConditionalKernel_reflection"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeGeneralSourceConditionalKernel."
        "generalAdjacentCubeConditionalKernel_row_normalized"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeGeneralSourceConditionalKernel."
        "generalAdjacentCubeConditionalKernel_reflection"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4AdjacentCubeGeneralSourceConditionalKernel."
        "generalKernel_of_stretched"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "Z4CubeStretchedSourceCoverageFence."
        "originUnitCube_not_covered_by_stretched_source"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualSlabFineIntertwinerWitness."
        "positivePhysicalTerm_has_fineFusionWitness"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualWholeSlabRecouplingRawKernel."
        "wholeSlabRecouplingRawWeight_nonnegative"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualWholeSlabRecouplingRawKernel."
        "wholeSlabRecouplingConditionalKernel_row_normalized"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualCutoffOneCoarseFaceDoor."
        "fixedFinalFaceRawWeight_parity_pos"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualCutoffOneCoarseLinkDoor."
        "binaryEvenExplicitValenceMultiplicity_pos_of_cutoff"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualCutoffOneParitySlabTarget."
        "CutoffOneEvenSlabSource.toCoherentSlabRecouplingSource"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualCutoffOneParitySlabTarget."
        "cutoffOneWholeSlabConditionalKernel_row_normalized"
        in CD2_LEAN_THEOREMS
    )
    assert (
        "CompactDualPhysicalRemainderLocality.PhysicalKernel."
        "fineCoarseCylinderDefect_abs_le_remainderL1"
        in CD2_LEAN_THEOREMS
    )
    assert CD2_LEAN_THEOREMS[-2:] == (
        "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
        "remainder_total_eqv_zero",
        "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
        "remainderL1_le_two",
    )
