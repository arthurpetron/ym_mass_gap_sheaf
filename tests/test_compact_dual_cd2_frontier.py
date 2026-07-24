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


def test_first_open_subgate_is_overlapping_link_assembly() -> None:
    frontier = current_cd2_frontier()
    assert frontier.local_fusion_kernel
    assert frontier.closed_component
    assert frontier.separated_composition
    assert frontier.overlapping_carrier_correction
    assert (
        frontier.first_open_subgate()
        is CD2Subgate.OVERLAPPING_LINK_ASSEMBLY
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
    assert CD2_LEAN_THEOREMS[-2:] == (
        "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
        "remainder_total_eqv_zero",
        "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
        "remainderL1_le_two",
    )
