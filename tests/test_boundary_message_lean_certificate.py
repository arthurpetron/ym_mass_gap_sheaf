"""Tests for the exact computation-to-Lean certificate emitter."""

from fractions import Fraction

import pytest

from computations.boundary_message_lean_certificate import (
    COMPUTED_FLOOR_PREFIX_DEMO_PAYLOAD,
    DEMO_PAYLOAD,
    PREFIX_DEMO_PAYLOAD,
    REGULARIZED_RANK_ONE_PREFIX_DEMO_PAYLOAD,
    ComputedFloorPrefixLeanCertificate,
    QuarterErrorPrefixLeanCertificate,
    RegularizedRankOneMatrixPrefixLeanCertificate,
    RegularizedRankOneScaleCertificate,
    RelativeRankOneLeanCertificate,
    emit_lean,
    emit_computed_floor_prefix_lean,
    emit_prefix_tail_lean,
    emit_regularized_rank_one_prefix_lean,
    validate_regularized_shards_parallel,
)


def test_demo_certificate_has_exact_one_twentieth_error() -> None:
    certificate = RelativeRankOneLeanCertificate.from_json(DEMO_PAYLOAD)

    assert certificate.maximum_relative_error == Fraction(1, 20)
    assert all(
        error == Fraction(1, 20)
        for row in certificate.relative_errors
        for error in row
    )


def test_emitter_contains_literal_data_and_lean_checker() -> None:
    certificate = RelativeRankOneLeanCertificate.from_json(DEMO_PAYLOAD)
    source = emit_lean(certificate, name="exactPilot")

    assert "def exactPilotKernel" in source
    assert "Q'.mkPos 21 2 (by decide)" in source
    assert "FiniteRelativeRankOneQuarterWitness" in source
    assert "terminalProjectiveRefresh_rate_le_quarter" in source
    assert "relativeRankOneSpread_square_le_fourThirds" in source
    assert "native_decide" not in source
    assert "sorry" not in source


def test_emitter_rejects_relative_error_above_one_sixteenth() -> None:
    payload = dict(DEMO_PAYLOAD)
    payload["kernel"] = [["11", "19/10"], ["57/4", "63/20"]]

    with pytest.raises(ValueError, match="exceeds 1/16"):
        RelativeRankOneLeanCertificate.from_json(payload)


def test_emitter_rejects_dimension_mismatch() -> None:
    payload = dict(DEMO_PAYLOAD)
    payload["terminal"] = ["7"]

    with pytest.raises(ValueError, match="terminal length"):
        RelativeRankOneLeanCertificate.from_json(payload)


def test_emitter_rejects_unsafe_lean_identifier() -> None:
    certificate = RelativeRankOneLeanCertificate.from_json(DEMO_PAYLOAD)

    with pytest.raises(ValueError, match="safe Lean identifier"):
        emit_lean(certificate, name="bad-name")


def test_prefix_demo_has_exact_threshold_and_maximum() -> None:
    certificate = QuarterErrorPrefixLeanCertificate.from_json(PREFIX_DEMO_PAYLOAD)

    assert certificate.threshold == 2
    assert certificate.maximum_error == Fraction(1, 16)


def test_prefix_emitter_checks_finite_values_and_requires_tail_theorem() -> None:
    certificate = QuarterErrorPrefixLeanCertificate.from_json(PREFIX_DEMO_PAYLOAD)
    source = emit_prefix_tail_lean(certificate, name="exactPrefix")

    assert "def exactPrefixBudget" in source
    assert "exactPrefixStage0_exact" in source
    assert "exactPrefixStage2_exact" in source
    assert "tail_step : forall stage : Nat" in source
    assert "QuarterErrorPrefixTail error" in source
    assert "exactPrefixAllStages_le" in source
    assert "native_decide" not in source
    assert "sorry" not in source


def test_prefix_certificate_accepts_zero_error() -> None:
    certificate = QuarterErrorPrefixLeanCertificate.from_json(
        {"prefix_errors": ["0", "1/32"]}
    )

    assert certificate.errors[0] == 0
    assert "(0 : Q')" in emit_prefix_tail_lean(certificate)


def test_prefix_certificate_rejects_invalid_values() -> None:
    with pytest.raises(ValueError, match="nonnegative"):
        QuarterErrorPrefixLeanCertificate.from_json({"prefix_errors": ["-1/32"]})
    with pytest.raises(ValueError, match="exceeds 1/16"):
        QuarterErrorPrefixLeanCertificate.from_json({"prefix_errors": ["1/15"]})


def test_computed_floor_prefix_demo_reaches_exact_tolerance() -> None:
    certificate = ComputedFloorPrefixLeanCertificate.from_json(
        COMPUTED_FLOOR_PREFIX_DEMO_PAYLOAD
    )

    assert certificate.threshold == 2
    assert certificate.maximum_relative_error == Fraction(1, 2048)


def test_computed_floor_prefix_emitter_rechecks_values_and_requires_cross_tail() -> None:
    certificate = ComputedFloorPrefixLeanCertificate.from_json(
        COMPUTED_FLOOR_PREFIX_DEMO_PAYLOAD
    )
    source = emit_computed_floor_prefix_lean(certificate, name="exactFloorPrefix")

    assert "def exactFloorPrefixBudget" in source
    assert "exactFloorPrefixErrorStage0_exact" in source
    assert "exactFloorPrefixFloorStage2_exact" in source
    assert "PositiveFloorErrorCrossTail" in source
    assert "tail_cross : forall stage : Nat" in source
    assert "physicalRelativeErrorTolerance" in source
    assert "exactFloorPrefixAllStages_le" in source
    assert "native_decide" not in source
    assert "sorry" not in source


def test_computed_floor_prefix_rejects_bad_floor_data() -> None:
    with pytest.raises(ValueError, match="equal length"):
        ComputedFloorPrefixLeanCertificate.from_json(
            {"prefix_error_majorants": ["0"], "prefix_floors": ["1", "2"]}
        )
    with pytest.raises(ValueError, match="strictly positive"):
        ComputedFloorPrefixLeanCertificate.from_json(
            {"prefix_error_majorants": ["0"], "prefix_floors": ["0"]}
        )
    with pytest.raises(ValueError, match="exceeds 1/2048"):
        ComputedFloorPrefixLeanCertificate.from_json(
            {"prefix_error_majorants": ["1/1024"], "prefix_floors": ["1"]}
        )


def test_regularized_rank_one_demo_is_computed_exactly() -> None:
    certificate = RegularizedRankOneMatrixPrefixLeanCertificate.from_json(
        REGULARIZED_RANK_ONE_PREFIX_DEMO_PAYLOAD
    )

    first, second, third = certificate.scales
    assert first.profile == (Fraction(1, 2), Fraction(1, 2))
    assert first.maximum_defect == 0
    assert first.projected_floor == 4096
    assert first.maximum_pairwise_cross_residual == 0
    assert first.maximum_exact_statistical_budget == 0
    assert first.source_shards == ((0,), (1,))
    assert first.source_shard_residual_majorants == (0, 0)
    assert first.maximum_chunked_statistical_budget == 0
    assert first.maximum_hybrid_statistical_budget == 0
    assert first.maximum_statistical_budget == Fraction(16384, 12289)
    assert second.profile == (Fraction(4098, 8195), Fraction(4097, 8195))
    assert second.maximum_defect == Fraction(1, 8195)
    assert second.projected_floor == Fraction(33566721, 8195)
    assert second.maximum_pairwise_cross_residual == 0
    assert second.maximum_exact_statistical_budget == Fraction(1, 8195)
    assert second.source_shards == ((0,),)
    assert second.maximum_chunked_statistical_budget == Fraction(1, 8195)
    assert second.maximum_hybrid_statistical_budget == Fraction(1, 8195)
    assert second.maximum_statistical_budget == Fraction(16387, 8195)
    assert third.maximum_defect == Fraction(4097, 24576)
    assert third.maximum_pairwise_cross_residual == 4096
    assert third.maximum_exact_statistical_budget == Fraction(4097, 24576)
    assert third.source_shard_residual_majorants == (4096, 4096)
    assert third.maximum_chunked_statistical_budget == Fraction(2731, 8192)
    assert third.maximum_hybrid_statistical_budget == Fraction(2731, 8192)
    assert third.maximum_statistical_budget == Fraction(13653, 8192)
    assert certificate.maximum_relative_defect == Fraction(4097, 100642817)
    assert (
        certificate.to_statistical_computed_floor_prefix().maximum_relative_error
        == Fraction(16387, 33566721)
    )
    assert (
        certificate.to_exact_statistical_computed_floor_prefix().maximum_relative_error
        == Fraction(4097, 100642817)
    )
    assert validate_regularized_shards_parallel(certificate, jobs=2) == (
        (Fraction(0), Fraction(0)),
        (Fraction(0),),
        (Fraction(4096), Fraction(4096)),
    )


def test_regularized_rank_one_emitter_rechecks_matrix_defect_and_floor() -> None:
    certificate = RegularizedRankOneMatrixPrefixLeanCertificate.from_json(
        REGULARIZED_RANK_ONE_PREFIX_DEMO_PAYLOAD
    )
    source = emit_regularized_rank_one_prefix_lean(
        certificate, name="exactRegularizedPrefix"
    )

    assert "def exactRegularizedPrefixScale1Amplitude" in source
    assert "def exactRegularizedPrefixScale1Profile" in source
    assert "theorem exactRegularizedPrefixScale1Pairwise_le" in source
    assert "def exactRegularizedPrefixScale1ExactStatisticalBudget" in source
    assert "theorem exactRegularizedPrefixScale1ExactStatisticalBudget_le" in source
    assert (
        "theorem exactRegularizedPrefixScale1GenericDefect_le_exactStatisticalError"
        in source
    )
    assert "def exactRegularizedPrefixScale1SourceChunks" in source
    assert "theorem exactRegularizedPrefixScale1SourceChunks_flatten" in source
    assert "theorem exactRegularizedPrefixScale1ChunkBound" in source
    assert (
        "theorem exactRegularizedPrefixScale1GenericDefect_le_chunkedStatisticalError"
        in source
    )
    assert "def exactRegularizedPrefixScale1HybridStatisticalBudget" in source
    assert "theorem exactRegularizedPrefixScale1HybridStatisticalBudget_le" in source
    assert (
        "theorem exactRegularizedPrefixScale1GenericDefect_le_hybridStatisticalError"
        in source
    )
    assert "def exactRegularizedPrefixScale1StatisticalBudget" in source
    assert "theorem exactRegularizedPrefixScale1StatisticalBudget_le" in source
    assert "theorem exactRegularizedPrefixScale1GenericDefect_le_statisticalError" in source
    assert "theorem exactRegularizedPrefixScale1Defect_le" in source
    assert "theorem exactRegularizedPrefixScale1Floor_le" in source
    assert "Q'.mkPos 1 8195 (by decide)" in source
    assert "PositiveFloorErrorCrossTail" in source
    assert "tail_cross : forall stage : Nat" in source
    assert "native_decide" not in source
    assert "sorry" not in source


def test_regularized_rank_one_parser_rejects_bad_matrices() -> None:
    with pytest.raises(ValueError, match="rectangular"):
        RegularizedRankOneScaleCertificate.from_json(
            {"amplitude": [["1", "1"], ["1"]], "pseudocount": "1"},
            scale=0,
        )
    with pytest.raises(ValueError, match="nonnegative"):
        RegularizedRankOneScaleCertificate.from_json(
            {"amplitude": [["1", "-1"]], "pseudocount": "1"},
            scale=0,
        )
    with pytest.raises(ValueError, match="positive mass"):
        RegularizedRankOneScaleCertificate.from_json(
            {"amplitude": [["0", "0"]], "pseudocount": "1"},
            scale=0,
        )
    with pytest.raises(ValueError, match="strictly positive"):
        RegularizedRankOneScaleCertificate.from_json(
            {"amplitude": [["1", "1"]], "pseudocount": "0"},
            scale=0,
        )
    with pytest.raises(ValueError, match="source_shard_size must be positive"):
        RegularizedRankOneScaleCertificate.from_json(
            {
                "amplitude": [["1", "1"]],
                "pseudocount": "1",
                "source_shard_size": 0,
            },
            scale=0,
        )


def test_regularized_rank_one_prefix_rejects_large_relative_defect() -> None:
    with pytest.raises(ValueError, match="exceeds 1/2048"):
        RegularizedRankOneMatrixPrefixLeanCertificate.from_json(
            {
                "scales": [
                    {"amplitude": [["2", "1"]], "pseudocount": "1"}
                ]
            }
        )
