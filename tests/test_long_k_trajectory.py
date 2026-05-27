"""Tests for `computations.long_k_trajectory` (Ch. 10–12 empirical decay)."""

from __future__ import annotations

import math
from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.long_k_trajectory import (
    ONE_LOOP_SU2_BETA_COEFF,
    LongKTrajectory,
    analytical_decay_rate,
    long_k_trajectory,
    plot_long_k_trajectories,
    uv_g_sequence,
)


# --------------------------------------------------------------------------
# β-function coefficient + analytical decay rate
# --------------------------------------------------------------------------


def test_one_loop_beta_coeff_su2() -> None:
    """b_0 = 11/3 · C_2(adj) = 11/3 · 2 = 22/3 for SU(2)."""
    assert ONE_LOOP_SU2_BETA_COEFF == pytest.approx(22.0 / 3.0)


def test_analytical_decay_rate_b2() -> None:
    """For block scale b = 2, the analytical decay rate r ≈ 0.976."""
    r = analytical_decay_rate(b=2.0)
    assert 0.97 < r < 0.98
    assert r == pytest.approx(0.97615, abs=1e-4)


def test_analytical_decay_rate_b1_is_one() -> None:
    """For b = 1 (no RG step), the decay rate is exp(0) = 1."""
    r = analytical_decay_rate(b=1.0)
    assert r == pytest.approx(1.0)


def test_analytical_decay_rate_b_large() -> None:
    """For very large b, the decay rate becomes very small."""
    r = analytical_decay_rate(b=10.0)
    assert 0.0 < r < 1.0
    # Larger b → faster decay (smaller r).
    assert r < analytical_decay_rate(b=2.0)


# --------------------------------------------------------------------------
# uv_g_sequence
# --------------------------------------------------------------------------


def test_uv_g_sequence_monotone_decreasing() -> None:
    """UV trajectory: g_k decreases monotonically."""
    g_seq = uv_g_sequence(g_0=0.40, K=10, b=2.0)
    assert len(g_seq) == 11
    for i in range(len(g_seq) - 1):
        assert g_seq[i + 1] < g_seq[i], f"g_{i+1} = {g_seq[i+1]} ≥ g_{i} = {g_seq[i]}"


def test_uv_g_sequence_starts_at_g_0() -> None:
    g_seq = uv_g_sequence(g_0=0.40, K=5, b=2.0)
    assert g_seq[0] == 0.40


def test_uv_g_sequence_rejects_invalid() -> None:
    with pytest.raises(ValueError, match="g_0"):
        uv_g_sequence(g_0=0.0, K=5, b=2.0)
    with pytest.raises(ValueError, match="block factor"):
        uv_g_sequence(g_0=0.40, K=5, b=1.0)
    with pytest.raises(ValueError, match="K"):
        uv_g_sequence(g_0=0.40, K=-1, b=2.0)


def test_uv_g_sequence_k_zero() -> None:
    """K=0 returns just the initial coupling."""
    g_seq = uv_g_sequence(g_0=0.40, K=0, b=2.0)
    assert g_seq == [0.40]


# --------------------------------------------------------------------------
# long_k_trajectory
# --------------------------------------------------------------------------


def test_long_k_trajectory_basic() -> None:
    traj = long_k_trajectory(K=10, g_0=0.40)
    assert isinstance(traj, LongKTrajectory)
    assert traj.K == 10
    assert len(traj.steps) == 11
    assert traj.g_0 == 0.40
    assert traj.convention is HeatKernelConvention.CANONICAL


def test_long_k_trajectory_g_decreases() -> None:
    """Sanity-check: g_k decreases (UV direction)."""
    traj = long_k_trajectory(K=20, g_0=0.40)
    for i in range(len(traj.steps) - 1):
        assert traj.steps[i + 1].g_k < traj.steps[i].g_k


def test_long_k_trajectory_K_lf_decreases() -> None:
    """K_lf decreases as g decreases (UV direction)."""
    traj = long_k_trajectory(K=20, g_0=0.40)
    for i in range(len(traj.steps) - 1):
        assert traj.steps[i + 1].K_lf <= traj.steps[i].K_lf + 1e-15


def test_long_k_trajectory_K_lf_positive() -> None:
    traj = long_k_trajectory(K=10, g_0=0.40)
    for s in traj.steps:
        assert s.K_lf > 0
        assert math.isfinite(s.K_lf)


def test_long_k_trajectory_K_sf_finite() -> None:
    traj = long_k_trajectory(K=10, g_0=0.40)
    for s in traj.steps:
        assert math.isfinite(s.K_sf)
        assert s.K_sf > 0


def test_long_k_trajectory_K_cap_is_sum() -> None:
    """K_cap_approx = K_sf + K_lf (the union-bound upper bound)."""
    traj = long_k_trajectory(K=5, g_0=0.40)
    for s in traj.steps:
        assert s.K_cap_approx == pytest.approx(s.K_sf + s.K_lf)


def test_long_k_trajectory_decay_ratio_near_analytical() -> None:
    """Empirical median r should be close to the analytical 0.976 (b=2)
    when the trajectory is long enough to reach the asymptotic regime."""
    traj = long_k_trajectory(K=50, g_0=0.40)
    assert traj.K_lf_ratio_median is not None
    r_an = analytical_decay_rate(b=2.0)
    # At K=50 with g_0 = 0.40, empirical r ≈ 0.965 (analytical 0.976).
    # The leading-asymptotic prediction is exact in the deep g → 0 limit;
    # at finite g we expect a small downward correction from higher-order
    # character-sum terms.  Tolerance: 5%.
    assert abs(traj.K_lf_ratio_median - r_an) < 0.05


def test_long_k_trajectory_sigma_hat_positive_K_50() -> None:
    """σ̂_K stays POSITIVE at K=50 (the σ̂-budget closure):
    σ̂_K ≥ 1 - 0.5 · K_lf(0) = 1 - 0.72 = 0.28 at g_0 = 0.40."""
    traj = long_k_trajectory(K=50, g_0=0.40)
    assert traj.sigma_hat_final > 0
    # Asymptotic bound: 1 - 0.5 · K_lf(0).
    K_lf_0 = traj.steps[0].K_lf
    asymptotic_bound = 1.0 - 0.5 * K_lf_0
    # At K=50, σ̂_K should be approaching the asymptotic bound from above.
    assert traj.sigma_hat_final >= asymptotic_bound - 1e-9


def test_long_k_trajectory_sigma_hat_monotone_decreasing_in_K() -> None:
    """σ̂_K decreases as K increases (more steps = more budget consumed),
    but stays bounded above the asymptotic floor."""
    sigmas = []
    for K in (10, 20, 50):
        traj = long_k_trajectory(K=K, g_0=0.40)
        sigmas.append(traj.sigma_hat_final)
    # σ̂(K=10) > σ̂(K=20) > σ̂(K=50).
    assert sigmas[0] > sigmas[1] > sigmas[2]


def test_long_k_trajectory_rejects_diverged_g_0() -> None:
    """At g_0 above the convergence threshold, the script raises early."""
    with pytest.raises(RuntimeError, match="non-convergent"):
        long_k_trajectory(K=5, g_0=0.50)  # g_max_lf ≈ 0.42 canonical


def test_long_k_trajectory_K_must_be_positive() -> None:
    with pytest.raises(ValueError, match="K"):
        long_k_trajectory(K=0, g_0=0.40)


# --------------------------------------------------------------------------
# Plot generation
# --------------------------------------------------------------------------


def test_plot_long_k_trajectories_writes_svg(tmp_path: Path) -> None:
    out_path = tmp_path / "long-k-test.svg"
    path_str, trajectories = plot_long_k_trajectories(
        K_values=(10, 20),
        g_0=0.40,
        output_path=str(out_path),
    )
    assert Path(path_str).exists()
    assert Path(path_str).stat().st_size > 1000  # non-empty SVG
    assert len(trajectories) == 2
    assert trajectories[0].K == 10
    assert trajectories[1].K == 20
