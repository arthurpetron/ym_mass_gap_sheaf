"""Tests for `computations.pilot_su2` (Milestone 3.5)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.pilot_su2 import (
    PILOT_THRESHOLD_K,
    PILOT_THRESHOLD_SIGMA_RATIO,
    PilotResult,
    plot_inductive_closure,
    run_pilot,
)

CANONICAL = HeatKernelConvention.CANONICAL


def test_pilot_default_K_is_three() -> None:
    """work_plan 3.5 requires K ≥ 3."""
    assert PILOT_THRESHOLD_K == 3


def test_pilot_threshold_is_half() -> None:
    """Recommended threshold: σ̂_K ≥ 0.5 σ̂_0."""
    assert PILOT_THRESHOLD_SIGMA_RATIO == 0.5


def test_run_pilot_result_shape() -> None:
    result = run_pilot()
    assert isinstance(result, PilotResult)
    assert result.K == 3
    assert isinstance(result.crit_1_small_field_KP, bool)
    assert isinstance(result.crit_2_large_field_KP, bool)
    assert isinstance(result.crit_3_overlap_KP, bool)
    assert isinstance(result.crit_4_delta_cap_summable, bool)
    assert isinstance(result.crit_5_sigma_hat_positive_and_budget, bool)
    assert isinstance(result.threshold_success, bool)


def test_pilot_all_five_pass_with_placeholders() -> None:
    """In the placeholder regime, all five criteria trivially pass."""
    result = run_pilot()
    assert result.all_five_pass is True


def test_pilot_succeeds_with_placeholders() -> None:
    """Five criteria + threshold all pass in placeholder regime."""
    result = run_pilot()
    assert result.pilot_succeeds is True


def test_pilot_sigma_hat_retained_in_placeholder() -> None:
    """σ̂_K = σ̂_0 with placeholder (Σ η = 0)."""
    result = run_pilot(sigma_hat_initial=2.5)
    assert result.sigma_hat_final == pytest.approx(2.5)


def test_pilot_rejects_too_small_K() -> None:
    """K must be ≥ 3 per work_plan 3.5."""
    with pytest.raises(ValueError, match="K must be ≥ 3"):
        run_pilot(K=2)


def test_pilot_larger_K() -> None:
    """Pilot can run for K > 3."""
    result = run_pilot(K=5)
    assert result.K == 5
    assert len(result.__class__.__annotations__) > 0  # smoke


def test_plot_writes_svg(tmp_path: Path) -> None:
    out = tmp_path / "test.svg"
    result = plot_inductive_closure(output_path=str(out))
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0


def test_pilot_provides_supporting_data() -> None:
    result = run_pilot()
    assert result.sigma_hat_initial > 0
    assert result.sigma_hat_final > 0
    assert result.total_delta_cap >= 0
    assert result.total_eta >= 0
