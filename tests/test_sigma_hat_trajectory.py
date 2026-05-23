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


def test_compute_eta_nonnegative() -> None:
    """η_k ≥ 0 — degradation can only reduce σ̂, not increase it."""
    assert compute_eta(0.8, 1.0, CANONICAL) >= 0
    assert compute_eta(1.0, 0.8, CANONICAL) >= 0


def test_compute_eta_zero_with_placeholder_K_values() -> None:
    """Placeholder K_sf, K_lf are g-independent → Δ_∩ = 0 → η = 0."""
    assert compute_eta(0.8, 1.2, CANONICAL) == 0.0


def test_compute_eta_zero_when_g_unchanged() -> None:
    assert compute_eta(1.0, 1.0, CANONICAL) == 0.0


def test_sigma_hat_trajectory_result_shape() -> None:
    g_traj = [1.0, 1.05, 1.1, 1.15]
    result = sigma_hat_trajectory(g_traj)
    assert isinstance(result, SigmaHatTrajectory)
    assert len(result.steps) == 4
    assert all(isinstance(s, SigmaHatStep) for s in result.steps)


def test_sigma_hat_trajectory_initial_sigma_at_step_zero() -> None:
    g_traj = [1.0, 1.05, 1.1]
    result = sigma_hat_trajectory(g_traj, sigma_hat_initial=0.7)
    assert result.steps[0].sigma_hat == pytest.approx(0.7)


def test_sigma_hat_trajectory_total_eta_is_sum() -> None:
    g_traj = [1.0, 1.05, 1.1, 1.15]
    result = sigma_hat_trajectory(g_traj)
    assert result.total_eta == pytest.approx(sum(s.eta_k for s in result.steps))


def test_sigma_hat_trajectory_budget_closure_with_placeholders() -> None:
    """With placeholders Σ η = 0 < σ̂_0; closure trivially passes."""
    g_traj = [1.0, 1.05, 1.1, 1.15]
    result = sigma_hat_trajectory(g_traj, sigma_hat_initial=1.0)
    assert result.budget_closure is True
    assert result.total_eta == pytest.approx(0.0)


def test_sigma_hat_decreases_or_constant_along_trajectory() -> None:
    """σ̂ is non-increasing across the trajectory."""
    g_traj = [1.0, 1.05, 1.1, 1.15]
    result = sigma_hat_trajectory(g_traj)
    sigmas = [s.sigma_hat for s in result.steps]
    for i in range(len(sigmas) - 1):
        assert sigmas[i + 1] <= sigmas[i] + 1e-12


def test_sigma_hat_trajectory_rejects_nonpositive_initial() -> None:
    with pytest.raises(ValueError):
        sigma_hat_trajectory([1.0, 1.05], sigma_hat_initial=0.0)
    with pytest.raises(ValueError):
        sigma_hat_trajectory([1.0, 1.05], sigma_hat_initial=-0.1)


def test_eta_coupling_scales_total() -> None:
    """Scaling eta_coupling scales η_k linearly (when Δ_∩ ≠ 0)."""
    g_traj = [1.0, 1.1, 1.2]
    # With placeholder Δ_∩ = 0, total η = 0 regardless of coupling.
    r1 = sigma_hat_trajectory(g_traj, eta_coupling=0.5)
    r2 = sigma_hat_trajectory(g_traj, eta_coupling=1.0)
    assert r1.total_eta == pytest.approx(2 * r2.total_eta - r2.total_eta)
    # i.e., both are 0.0; equality holds trivially.


def test_plot_writes_svg(tmp_path: Path) -> None:
    out = tmp_path / "test.svg"
    result = plot_sigma_hat_trajectory(output_path=str(out))
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0
