"""Tests for the untrusted exact variable-elimination trace emitter."""

from fractions import Fraction

import pytest

from computations.finite_elimination_lean_certificate import (
    DEMO_PAYLOAD,
    ProductEliminationInput,
    compute_trace,
    emit_lean,
)


def test_demo_trace_has_expected_exact_sum() -> None:
    source = ProductEliminationInput.from_json(DEMO_PAYLOAD)
    trace = compute_trace(source)

    assert trace.validates()
    assert trace.exact_sum == Fraction(126000)


def test_emitter_contains_replay_contract_and_no_banned_shortcuts() -> None:
    trace = compute_trace(ProductEliminationInput.from_json(DEMO_PAYLOAD))
    lean = emit_lean(trace, name="exactProductEight")

    assert "ExactVariableEliminationCertificate 2 8" in lean
    assert "exactProductEightCertificate.assignmentSum_eqv_bottom" in lean
    assert "finiteAssignmentSum 2 8" in lean
    assert "Q'.ofNat 126000" in lean
    assert "native_decide" not in lean
    assert "sorry" not in lean


def test_parser_rejects_ragged_or_negative_weights() -> None:
    with pytest.raises(ValueError, match="equal length"):
        ProductEliminationInput.from_json(
            {"coordinate_weights": [["1", "2"], ["3"]]}
        )
    with pytest.raises(ValueError, match="nonnegative"):
        ProductEliminationInput.from_json(
            {"coordinate_weights": [["1", "-1"]]}
        )


def test_emitter_rejects_unsafe_identifier() -> None:
    trace = compute_trace(ProductEliminationInput.from_json(DEMO_PAYLOAD))

    with pytest.raises(ValueError, match="safe Lean identifier"):
        emit_lean(trace, name="bad-name")
