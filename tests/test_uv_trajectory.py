"""Tests for `computations.uv_trajectory` (Milestone 6.3)."""

from __future__ import annotations

import math
from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.uv_trajectory import (
    ONE_LOOP_SU2_BETA_COEFF,
    UVTrajectory,
    UVTrajectoryStep,
    geometric_decay_rate,
    plot_uv_trajectory,
    uv_su2_trajectory,
)


# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------


def test_one_loop_beta_coeff_is_22_over_3():
    """SU(2): b_0 = (11/3) · C_2(adj) = (11/3) · 2 = 22/3."""
    assert ONE_LOOP_SU2_BETA_COEFF == pytest.approx(22.0 / 3.0)


# --------------------------------------------------------------------------
# Trajectory shape
# --------------------------------------------------------------------------


def test_trajectory_length_matches_k_max():
    traj = uv_su2_trajectory(k_max=5, g_0=0.30)
    assert isinstance(traj, UVTrajectory)
    assert len(traj.steps) == 6  # k = 0, 1, ..., 5


def test_g_k_monotone_decreasing():
    """The UV direction's signature property: g_k decreases monotonically."""
    traj = uv_su2_trajectory(k_max=10, g_0=0.30)
    for i in range(len(traj.steps) - 1):
        assert traj.steps[i + 1].g_k < traj.steps[i].g_k, (
            f"g_k should monotonically decrease at step {i}: "
            f"{traj.steps[i].g_k} ≮ {traj.steps[i + 1].g_k}"
        )
    assert traj.converges_to_zero is True


def test_a_k_decreases_geometrically():
    """a_k/a_0 = b^(-k) exactly."""
    b = 3.0
    traj = uv_su2_trajectory(k_max=5, b=b, g_0=0.30)
    for s in traj.steps:
        assert s.a_k_over_a_0 == pytest.approx(b ** (-s.k))


def test_g_evolves_via_one_loop_beta():
    """1/g_{k+1}² = 1/g_k² + (b_0/16π²)·log b."""
    b = 2.0
    g_0 = 0.30
    traj = uv_su2_trajectory(k_max=3, b=b, g_0=g_0)
    coeff = ONE_LOOP_SU2_BETA_COEFF / (16.0 * math.pi * math.pi)
    for i in range(len(traj.steps) - 1):
        g_now = traj.steps[i].g_k
        g_next = traj.steps[i + 1].g_k
        expected_inv_sq = 1.0 / (g_now * g_now) + coeff * math.log(b)
        actual_inv_sq = 1.0 / (g_next * g_next)
        assert actual_inv_sq == pytest.approx(expected_inv_sq)


# --------------------------------------------------------------------------
# η_k behavior in the UV direction
# --------------------------------------------------------------------------


def test_eta_k_vanishes_in_uv_direction():
    """In the UV direction, K_∩ is non-increasing (because K_sf, K_lf both
    decrease as g decreases), so Δ_∩ = max(0, K_next - K) = 0, and
    η_k = c_polymer · Δ_∩ / A_min = 0.

    This is a structural feature of the σ̂-budget framework: the UV
    direction is automatically "controlled" (the trajectory becomes
    increasingly tame), so the budget closure is trivial.
    """
    traj = uv_su2_trajectory(k_max=10, g_0=0.30)
    for s in traj.steps[:-1]:  # last step has η_k = 0 by convention anyway
        assert s.eta_k == 0.0, (
            f"in UV direction expected η_k = 0 at k={s.k}; got {s.eta_k}"
        )


def test_trivial_sigma_budget_closure_in_uv():
    """Since all η_k = 0 in the UV direction, Σ η_k = 0 < σ̂_0 trivially.
    This is the empirical content of the 'genuine infinite-tail closure'."""
    traj = uv_su2_trajectory(k_max=10, g_0=0.30)
    total_eta = sum(s.eta_k for s in traj.steps)
    assert total_eta == 0.0


# --------------------------------------------------------------------------
# Decay rate helper
# --------------------------------------------------------------------------


def test_decay_rate_returns_none_for_all_zero():
    traj = uv_su2_trajectory(k_max=5, g_0=0.30)
    assert geometric_decay_rate(traj) is None


# --------------------------------------------------------------------------
# Input validation
# --------------------------------------------------------------------------


def test_rejects_invalid_k_max():
    with pytest.raises(ValueError, match="k_max must be"):
        uv_su2_trajectory(k_max=-1)


def test_rejects_invalid_b():
    with pytest.raises(ValueError, match="block factor"):
        uv_su2_trajectory(b=0.5)
    with pytest.raises(ValueError, match="block factor"):
        uv_su2_trajectory(b=1.0)


def test_rejects_invalid_g_0():
    with pytest.raises(ValueError, match="must be positive"):
        uv_su2_trajectory(g_0=-0.1)


# --------------------------------------------------------------------------
# Convention dispatch
# --------------------------------------------------------------------------


def test_wilson_convention_runs():
    """Wilson conv should not crash; trajectory shape same (g_k decreases)."""
    traj = uv_su2_trajectory(k_max=5, g_0=0.50, t_choice=HeatKernelConvention.WILSON)
    assert traj.convention is HeatKernelConvention.WILSON
    assert traj.converges_to_zero is True


# --------------------------------------------------------------------------
# Figure
# --------------------------------------------------------------------------


def test_plot_writes_svg(tmp_path: Path):
    out = tmp_path / "uv.svg"
    result = plot_uv_trajectory(k_max=5, g_0=0.30, output_path=str(out))
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0
    text = out.read_text(encoding="utf-8")
    assert text.lstrip().startswith("<?xml")
    assert "</svg>" in text
