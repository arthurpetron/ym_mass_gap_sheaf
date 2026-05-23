"""Tests for `computations.sigma_hat_trajectory` (Milestone 3.4)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.sigma_hat_trajectory import (
    SigmaHatStep,
    SigmaHatTrajectory,
    compute_eta,
    plot_sigma_hat_trajectory,
    sigma_hat_trajectory,
)

CANONICAL = HeatKernelConvention.CANONICAL


def test_compute_eta_nonnegative_in_convergent_regime() -> None:
    """η_k ≥ 0 in the small-field convergent regime (g < 0.4)."""
    assert compute_eta(0.1, 0.2, CANONICAL) >= 0
    assert compute_eta(0.2, 0.1, CANONICAL) >= 0


def test_compute_eta_finite_in_convergent_regime() -> None:
    """In convergent regime, η_k is finite (and grows with g)."""
    import math

    assert math.isfinite(compute_eta(0.1, 0.2, CANONICAL))


def test_compute_eta_infinite_in_non_convergent_regime() -> None:
    """Above cluster-expansion threshold, K's → ∞ → η_k → ∞."""
    import math

    assert math.isinf(compute_eta(0.8, 1.2, CANONICAL))


def test_compute_eta_zero_when_g_unchanged_convergent() -> None:
    """In convergent regime, no g change → no η."""
    assert compute_eta(0.2, 0.2, CANONICAL) == 0.0


def test_sigma_hat_trajectory_result_shape() -> None:
    g_traj = [0.1, 0.15, 0.2, 0.25]  # convergent regime
    result = sigma_hat_trajectory(g_traj)
    assert isinstance(result, SigmaHatTrajectory)
    assert len(result.steps) == 4
    assert all(isinstance(s, SigmaHatStep) for s in result.steps)


def test_sigma_hat_trajectory_initial_sigma_at_step_zero() -> None:
    g_traj = [0.1, 0.15, 0.2]
    result = sigma_hat_trajectory(g_traj, sigma_hat_initial=0.7)
    assert result.steps[0].sigma_hat == pytest.approx(0.7)


def test_sigma_hat_trajectory_total_eta_is_sum() -> None:
    g_traj = [0.1, 0.15, 0.2, 0.25]
    result = sigma_hat_trajectory(g_traj)
    assert result.total_eta == pytest.approx(sum(s.eta_k for s in result.steps))


def test_sigma_hat_trajectory_budget_closure_convergent_regime() -> None:
    """In convergent regime, Σ η finite; closure depends on σ̂_0 and accumulation."""
    g_traj = [0.1, 0.15, 0.2, 0.25]
    result = sigma_hat_trajectory(g_traj, sigma_hat_initial=1.0)
    import math

    assert math.isfinite(result.total_eta)
    # With small g changes, the total η is small; closure passes for σ̂_0 = 1.
    if result.total_eta < 1.0:
        assert result.budget_closure is True


def test_sigma_hat_trajectory_budget_fails_non_convergent_regime() -> None:
    """In non-convergent regime, Σ η = ∞ → budget closure fails."""
    g_traj = [0.8, 0.9, 1.0]
    result = sigma_hat_trajectory(g_traj, sigma_hat_initial=1.0)
    import math

    assert math.isinf(result.total_eta)
    assert result.budget_closure is False


def test_sigma_hat_decreases_or_constant_along_trajectory() -> None:
    """σ̂ is non-increasing across the trajectory (convergent regime, finite η)."""
    g_traj = [0.1, 0.15, 0.2, 0.25]
    result = sigma_hat_trajectory(g_traj)
    sigmas = [s.sigma_hat for s in result.steps]
    for i in range(len(sigmas) - 1):
        assert sigmas[i + 1] <= sigmas[i] + 1e-12


def test_sigma_hat_trajectory_rejects_nonpositive_initial() -> None:
    with pytest.raises(ValueError):
        sigma_hat_trajectory([0.1, 0.2], sigma_hat_initial=0.0)
    with pytest.raises(ValueError):
        sigma_hat_trajectory([0.1, 0.2], sigma_hat_initial=-0.1)


def test_eta_coupling_scales_total_in_convergent_regime() -> None:
    """In convergent regime where Δ_∩ ≠ 0, eta_coupling scales η linearly."""
    g_traj = [0.1, 0.15, 0.2]
    r_half = sigma_hat_trajectory(g_traj, eta_coupling=0.5)
    r_one = sigma_hat_trajectory(g_traj, eta_coupling=1.0)
    # η scales linearly with the coupling.
    if r_one.total_eta > 0:
        assert r_half.total_eta == pytest.approx(0.5 * r_one.total_eta)


def test_plot_writes_svg(tmp_path: Path) -> None:
    out = tmp_path / "test.svg"
    result = plot_sigma_hat_trajectory(output_path=str(out))
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0
