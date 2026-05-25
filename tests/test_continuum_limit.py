"""Tests for `computations.continuum_limit` (Milestone 7.1).

Covers:

  * σ̂_k trajectory shape (length, initial value).
  * σ̂_k monotone non-increasing under nonneg η_k.
  * σ̂_∞ > 0 in the UV-pilot regime.
  * `g_0` dependence — in the trivial η ≡ 0 regime, σ̂_∞ = σ̂_0 for all g_0.
  * Convergence-rate diagnostics on a synthetic geometric η.
  * Input validation.
  * The `eta_override` escape hatch for non-trivially-decaying η.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.continuum_limit import (
    ContinuumLimit,
    SigmaHatLimitStep,
    compare_g0_dependence,
    plot_continuum_limit,
    sigma_hat_uv_limit,
)
from computations.heat_kernel import HeatKernelConvention


# --------------------------------------------------------------------------
# Trajectory shape
# --------------------------------------------------------------------------


def test_trajectory_has_kmax_plus_one_steps():
    """k_max RG transitions produce k_max + 1 σ̂_k values (σ̂_0 through σ̂_{k_max})."""
    result = sigma_hat_uv_limit(g_0=0.30, k_max=10)
    assert len(result.steps) == 11


def test_initial_sigma_hat_matches_input():
    """σ̂_0 in the returned trajectory equals the requested sigma_hat_initial."""
    sigma_0 = 2.5
    result = sigma_hat_uv_limit(g_0=0.30, k_max=5, sigma_hat_initial=sigma_0)
    assert result.steps[0].sigma_hat_k == sigma_0
    assert result.sigma_hat_initial == sigma_0


def test_returns_continuum_limit_dataclass():
    result = sigma_hat_uv_limit(g_0=0.30, k_max=5)
    assert isinstance(result, ContinuumLimit)
    assert all(isinstance(s, SigmaHatLimitStep) for s in result.steps)


# --------------------------------------------------------------------------
# σ̂_k monotonicity (the structural σ̂-budget property)
# --------------------------------------------------------------------------


def test_sigma_hat_monotone_non_increasing_uv_pilot():
    """σ̂_k is monotone non-increasing under η_k ≥ 0; in the UV pilot
    with η_k ≡ 0, the sequence is constant (still non-increasing)."""
    result = sigma_hat_uv_limit(g_0=0.30, k_max=15)
    assert result.is_monotone_decreasing is True
    for i in range(len(result.steps) - 1):
        assert result.steps[i + 1].sigma_hat_k <= result.steps[i].sigma_hat_k


def test_sigma_hat_monotone_non_increasing_synthetic_geometric():
    """With a synthetic geometric η_k = 0.01 · 0.5^k, σ̂_k strictly decreases
    until η_k underflows to 0."""
    eta = [0.01 * (0.5 ** k) for k in range(20)]
    result = sigma_hat_uv_limit(
        g_0=0.30, k_max=20, sigma_hat_initial=1.0, eta_override=eta
    )
    assert result.is_monotone_decreasing is True
    # At least the first several steps should strictly decrease.
    assert result.steps[1].sigma_hat_k < result.steps[0].sigma_hat_k
    assert result.steps[5].sigma_hat_k < result.steps[4].sigma_hat_k


# --------------------------------------------------------------------------
# σ̂_∞ > 0 (the Phase 7.1 make-or-break condition)
# --------------------------------------------------------------------------


def test_sigma_hat_limit_positive_uv_pilot():
    """In the UV pilot regime (η ≡ 0), σ̂_∞ = σ̂_0 = 1.0 > 0 exactly."""
    result = sigma_hat_uv_limit(g_0=0.30, k_max=20)
    assert result.is_positive is True
    assert result.sigma_hat_limit == 1.0
    assert result.total_eta_consumed == 0.0


def test_sigma_hat_limit_positive_synthetic_geometric():
    """For a synthetic geometric η with Σ η = 0.01 / (1 - 0.5) = 0.02 < 1,
    σ̂_∞ ≈ 0.98 > 0."""
    eta = [0.01 * (0.5 ** k) for k in range(30)]
    result = sigma_hat_uv_limit(
        g_0=0.30, k_max=30, sigma_hat_initial=1.0, eta_override=eta
    )
    assert result.is_positive is True
    assert result.sigma_hat_limit == pytest.approx(0.98, abs=1e-6)


def test_sigma_hat_limit_negative_when_budget_exceeded():
    """If Σ η > σ̂_0, σ̂_∞ < 0 (the budget-closure failure case)."""
    # η_k = 0.5 for k=0,1,2 makes Σ η ≥ 1.5 > 1.
    eta = [0.5] * 10
    result = sigma_hat_uv_limit(
        g_0=0.30, k_max=10, sigma_hat_initial=1.0, eta_override=eta
    )
    assert result.is_positive is False
    assert result.sigma_hat_limit < 0


# --------------------------------------------------------------------------
# Convergence rate
# --------------------------------------------------------------------------


def test_convergence_rate_none_when_eta_identically_zero():
    """UV pilot has η ≡ 0, so |σ̂_k - σ̂_∞| = 0 throughout and no rate
    can be extracted."""
    result = sigma_hat_uv_limit(g_0=0.30, k_max=10)
    assert result.convergence_rate is None
    assert result.geometric_decay_rate is None


def test_convergence_rate_matches_geometric_decay():
    """For η_k = c · r^k, the distance |σ̂_k - σ̂_∞| also decays
    geometrically with ratio r (since |σ̂_k - σ̂_∞| = Σ_{j≥k} η_j =
    c · r^k / (1 - r))."""
    r = 0.4
    c = 0.005
    eta = [c * (r ** k) for k in range(40)]
    result = sigma_hat_uv_limit(
        g_0=0.30, k_max=40, sigma_hat_initial=1.0, eta_override=eta
    )
    assert result.convergence_rate is not None
    assert result.convergence_rate == pytest.approx(r, abs=0.05)


# --------------------------------------------------------------------------
# Telescoping invariant: σ̂_K = σ̂_0 - Σ_{k<K} η_k
# --------------------------------------------------------------------------


def test_telescoping_invariant():
    """For any η-sequence, σ̂_K must equal σ̂_0 - Σ_{k<K} η_k exactly
    (modulo floating-point)."""
    eta = [0.01, 0.02, 0.005, 0.003, 0.001]
    sigma_0 = 1.0
    result = sigma_hat_uv_limit(
        g_0=0.30, k_max=5, sigma_hat_initial=sigma_0, eta_override=eta
    )
    for k in range(len(result.steps)):
        expected = sigma_0 - sum(eta[:k])
        assert result.steps[k].sigma_hat_k == pytest.approx(expected, abs=1e-12)


# --------------------------------------------------------------------------
# g_0 dependence
# --------------------------------------------------------------------------


def test_g0_dependence_trivial_in_uv_pilot():
    """In the η ≡ 0 regime, σ̂_∞ = σ̂_0 for every g_0 — degenerate
    g_0-independence."""
    rows = compare_g0_dependence(k_max=15)
    assert len(rows) == 4  # canonical default sweep
    for row in rows:
        assert row.sigma_hat_limit == 1.0
        assert row.total_eta_consumed == 0.0


def test_g0_dependence_custom_values():
    """Caller can supply a custom g_0 sweep."""
    rows = compare_g0_dependence(g_0_values=[0.15, 0.25, 0.35], k_max=10)
    assert len(rows) == 3
    assert [row.g_0 for row in rows] == [0.15, 0.25, 0.35]


# --------------------------------------------------------------------------
# Input validation
# --------------------------------------------------------------------------


def test_rejects_invalid_k_max():
    with pytest.raises(ValueError, match="k_max must be ≥ 1"):
        sigma_hat_uv_limit(g_0=0.30, k_max=0)


def test_rejects_invalid_sigma_hat_initial():
    with pytest.raises(ValueError, match="sigma_hat_initial must be positive"):
        sigma_hat_uv_limit(g_0=0.30, k_max=5, sigma_hat_initial=-0.5)


def test_rejects_short_eta_override():
    with pytest.raises(ValueError, match="eta_override must have length"):
        sigma_hat_uv_limit(g_0=0.30, k_max=10, eta_override=[0.01, 0.02])


# --------------------------------------------------------------------------
# Wilson convention dispatch
# --------------------------------------------------------------------------


def test_wilson_convention_runs():
    result = sigma_hat_uv_limit(
        g_0=0.50, k_max=10, t_choice=HeatKernelConvention.WILSON
    )
    assert result.convention is HeatKernelConvention.WILSON
    # Wilson allows g_0 = 0.50 (within sf-window ~0.81).
    assert result.is_positive is True


# --------------------------------------------------------------------------
# Figure
# --------------------------------------------------------------------------


def test_plot_writes_svg(tmp_path: Path):
    out = tmp_path / "continuum.svg"
    result_path = plot_continuum_limit(g_0=0.30, k_max=10, output_path=str(out))
    assert Path(result_path) == out
    assert out.exists()
    assert out.stat().st_size > 0
    text = out.read_text(encoding="utf-8")
    assert text.lstrip().startswith("<?xml")
    assert "</svg>" in text


def test_plot_with_eta_override(tmp_path: Path):
    """The plot routine should accept eta_override for the non-trivial case."""
    eta = [0.01 * (0.5 ** k) for k in range(20)]
    out = tmp_path / "geom.svg"
    result_path = plot_continuum_limit(
        g_0=0.30, k_max=20, output_path=str(out), eta_override=eta
    )
    assert Path(result_path) == out
    assert out.exists()
