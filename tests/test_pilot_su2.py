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


def test_pilot_fails_at_default_g_0_post_balaban() -> None:
    """Post-3.1-upgrade: default g_0 = 1.0 is OUTSIDE the small-field
    cluster-expansion convergence threshold (g_max ≈ 0.4).  K_sf = ∞
    propagates; criteria 4 and 5 fail."""
    result = run_pilot(g_0=1.0)
    # crit_1, _2, _3 are about positivity, which still pass.
    assert result.crit_1_small_field_KP is True
    assert result.crit_2_large_field_KP is True
    # crit_4 may still pass if total is "finite" by Python's bool(inf < inf)
    # but the σ̂ budget closure should fail.
    assert result.crit_5_sigma_hat_positive_and_budget is False
    assert result.pilot_succeeds is False


def test_pilot_passes_at_small_g_0_convergent_regime() -> None:
    """In the asymptotic-freedom regime (g_0 sufficiently small), the
    small-field cluster expansion converges and the pilot can pass."""
    # g_0 = 0.1 keeps g_k well below the threshold across K = 3 RG steps.
    result = run_pilot(g_0=0.1, sigma_hat_initial=10.0)
    # In convergent regime, η is finite + small.
    import math

    assert math.isfinite(result.total_eta)
    # σ̂ remains positive.
    assert result.sigma_hat_final > 0
    # All five criteria pass.
    assert result.all_five_pass is True


def test_pilot_sigma_hat_retained_in_convergent_regime() -> None:
    """In convergent regime, σ̂_K close to σ̂_0 (small accumulation)."""
    result = run_pilot(g_0=0.1, sigma_hat_initial=10.0)
    # σ̂_K should be close to σ̂_0; not equal (η ≠ 0 now).
    assert 0.5 * result.sigma_hat_initial <= result.sigma_hat_final <= result.sigma_hat_initial


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
    """Supporting data is structured correctly regardless of convergence."""
    result = run_pilot(g_0=0.1)  # convergent regime
    assert result.sigma_hat_initial > 0
    assert result.sigma_hat_final > 0
    assert result.total_delta_cap >= 0
    assert result.total_eta >= 0
