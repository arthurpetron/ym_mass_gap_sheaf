"""Regression tests for the fail-closed compact-dual continuum route."""

from fractions import Fraction

import pytest

from computations.compact_dual_continuum_route import (
    ClosureGate,
    CompactDualContinuumRoute,
    ConstructiveLandingCertificate,
    ContinuumGapSurvivalCertificate,
    CumulativeContractionEnvelope,
    GeometricTailEnvelope,
    LanfordEnclosureCertificate,
    PhysicalBlockRemainderCertificate,
    SummableDistortionCertificate,
    UniformRemainderNormCertificate,
    current_dual_route,
    current_finite_dual_evidence,
)


def _exact_block(*, complete_channels: bool = True) -> PhysicalBlockRemainderCertificate:
    """A tiny algebraic fixture used only to test certificate composition."""

    return PhysicalBlockRemainderCertificate(
        physical_data_id="synthetic-composition-fixture",
        fine_state_ids=("fine:0", "fine:1"),
        coarse_state_ids=("coarse:0", "coarse:1"),
        fine_weights=(Fraction(1, 2), Fraction(1, 2)),
        coarse_weights=(Fraction(1, 4), Fraction(3, 4)),
        kernel=(
            (Fraction(1, 2), Fraction(1, 2)),
            (Fraction(0), Fraction(1)),
        ),
        geometry_pinned=True,
        integrator_semantics_proved=True,
        coupling_coordinate_pinned=True,
        complete_boundary_channels=complete_channels,
        physical_kernel_identified=True,
        target_support_proved=True,
        reflection_intertwines=True,
    )


def _synthetic_closed_route() -> CompactDualContinuumRoute:
    """Exercise the full dependency algebra; this is not a YM certificate."""

    block = _exact_block()
    enclosure = LanfordEnclosureCertificate(
        domain_id="synthetic-ball",
        self_mapping=True,
        reflection_cone_preserved=True,
        physical_norm_pinned=True,
        uniform_ratio=Fraction(3, 4),
    )
    return CompactDualContinuumRoute(
        evidence=current_finite_dual_evidence(),
        block=block,
        remainder_norm=UniformRemainderNormCertificate(
            observed_norm=Fraction(0),
            defect_coordinate=Fraction(1, 2),
            quadratic_constant=Fraction(1),
            cutoff_tail=GeometricTailEnvelope(Fraction(1, 100), Fraction(1, 2)),
            weighted_norm_matches_block=True,
            constant_is_cutoff_independent=True,
            volume_uniform=True,
        ),
        enclosure=enclosure,
        landing=ConstructiveLandingCertificate(
            scale=2,
            state_id="synthetic-state-at-2",
            physical_trajectory_pinned=True,
            state_computed=True,
            state_in_enclosure=True,
        ),
        distortion=SummableDistortionCertificate(
            block_remainder=GeometricTailEnvelope(
                Fraction(1, 100), Fraction(1, 2)
            ),
            dynamic=GeometricTailEnvelope(Fraction(1, 100), Fraction(1, 2)),
            interface=GeometricTailEnvelope(Fraction(1, 100), Fraction(1, 2)),
            physical_comparison_pinned=True,
            scale_uniform=True,
            computable_modulus=True,
        ),
        continuum=ContinuumGapSurvivalCertificate(
            fixed_spacing_gap=Fraction(1, 4),
            continuum_start=2,
            volume_error=GeometricTailEnvelope(Fraction(1, 100), Fraction(1, 2)),
            spacing_error=GeometricTailEnvelope(Fraction(1, 100), Fraction(1, 2)),
            wilson_readout_pinned=True,
            volume_modulus_uniform=True,
            spacing_conversion_proved=True,
            os_reconstruction_bound=True,
        ),
    )


def test_current_route_stops_honestly_at_physical_cd2() -> None:
    route = current_dual_route()
    assert route.evidence.four_cube_pair_orbits == 100
    assert route.evidence.six_valent_pair_orbits == 65
    assert route.evidence.first_branching_defect_orbits == 14
    assert route.evidence.analytic_gates_discharged == 0
    assert route.first_open_gate() is ClosureGate.CD2_PHYSICAL_BLOCK
    assert not route.is_continuum_closed()
    assert route.certified_gap_floor() is None


def test_cd2_pushforward_and_zero_mass_remainder_are_computed() -> None:
    block = _exact_block()
    assert block.pushforward() == (Fraction(1, 4), Fraction(3, 4))
    assert block.remainder() == (Fraction(0), Fraction(0))
    assert block.remainder_l1_norm() == 0
    assert block.kernel_is_stochastic()
    assert block.remainder_has_zero_mass()
    assert block.is_closed()


def test_cd2_retains_a_signed_overlap_remainder() -> None:
    block = PhysicalBlockRemainderCertificate(
        physical_data_id="synthetic-signed-remainder-fixture",
        fine_state_ids=("fine:0", "fine:1"),
        coarse_state_ids=("coarse:0", "coarse:1"),
        fine_weights=(Fraction(1, 2), Fraction(1, 2)),
        coarse_weights=(Fraction(1, 2), Fraction(1, 2)),
        kernel=(
            (Fraction(1, 2), Fraction(1, 2)),
            (Fraction(0), Fraction(1)),
        ),
        geometry_pinned=True,
        integrator_semantics_proved=True,
        coupling_coordinate_pinned=True,
        complete_boundary_channels=True,
        physical_kernel_identified=True,
        target_support_proved=True,
        reflection_intertwines=True,
    )
    assert block.remainder() == (Fraction(-1, 4), Fraction(1, 4))
    assert block.remainder_l1_norm() == Fraction(1, 2)
    assert block.remainder_has_zero_mass()
    assert block.is_closed()


def test_cd2_fails_closed_if_channel_completeness_is_missing() -> None:
    block = _exact_block(complete_channels=False)
    assert block.kernel_is_stochastic()
    assert block.remainder_has_zero_mass()
    assert not block.is_closed()


def test_invalid_stochastic_kernel_is_rejected_by_gate() -> None:
    block = PhysicalBlockRemainderCertificate(
        physical_data_id="synthetic-bad-kernel-fixture",
        fine_state_ids=("fine:0",),
        coarse_state_ids=("coarse:0", "coarse:1"),
        fine_weights=(Fraction(1),),
        coarse_weights=(Fraction(1), Fraction(0)),
        kernel=((Fraction(2), Fraction(-1)),),
        geometry_pinned=True,
        integrator_semantics_proved=True,
        coupling_coordinate_pinned=True,
        complete_boundary_channels=True,
        physical_kernel_identified=True,
        target_support_proved=True,
        reflection_intertwines=True,
    )
    assert not block.kernel_is_stochastic()
    assert not block.is_closed()


def test_geometric_moduli_are_exact_and_constructive() -> None:
    envelope = GeometricTailEnvelope(Fraction(3, 10), Fraction(1, 2))
    contraction = CumulativeContractionEnvelope(Fraction(2), Fraction(1, 4))
    assert envelope.term_bound(3) == Fraction(3, 80)
    assert envelope.tail_bound(3) == Fraction(3, 40)
    assert contraction.product_bound(3) == Fraction(1, 32)


def test_full_composition_returns_only_a_strict_positive_floor() -> None:
    route = _synthetic_closed_route()
    assert all(result.closed for result in route.gate_report())
    assert route.first_open_gate() is None
    assert route.is_continuum_closed()
    assert route.certified_gap_floor() == Fraction(9, 40)


def test_continuum_gate_rejects_loss_equal_to_gap() -> None:
    route = _synthetic_closed_route()
    assert route.continuum is not None
    continuum = ContinuumGapSurvivalCertificate(
        fixed_spacing_gap=Fraction(1, 40),
        continuum_start=route.continuum.continuum_start,
        volume_error=route.continuum.volume_error,
        spacing_error=route.continuum.spacing_error,
        wilson_readout_pinned=True,
        volume_modulus_uniform=True,
        spacing_conversion_proved=True,
        os_reconstruction_bound=True,
    )
    zero_floor_route = CompactDualContinuumRoute(
        evidence=route.evidence,
        block=route.block,
        remainder_norm=route.remainder_norm,
        enclosure=route.enclosure,
        landing=route.landing,
        distortion=route.distortion,
        continuum=continuum,
    )
    assert zero_floor_route.candidate_gap_floor() == 0
    assert zero_floor_route.first_open_gate() is ClosureGate.SPACING_UNIFORM_GAP
    assert zero_floor_route.certified_gap_floor() is None


@pytest.mark.parametrize(
    ("amplitude", "ratio"),
    [
        (Fraction(-1), Fraction(1, 2)),
        (Fraction(1), Fraction(-1, 2)),
        (Fraction(1), Fraction(1)),
    ],
)
def test_invalid_geometric_modulus_is_rejected(
    amplitude: Fraction, ratio: Fraction
) -> None:
    with pytest.raises(ValueError):
        GeometricTailEnvelope(amplitude, ratio)
