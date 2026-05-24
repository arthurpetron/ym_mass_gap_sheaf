"""Tests for `computations.sigma_hat_trajectory` (Milestone 3.4, post-upgrade)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.sigma_hat_trajectory import (
    BALABAN_POLYMER_RESIDUAL,
    DERIVED_ETA_COUPLING,
    WILSON_LOOP_MIN_AREA_DIMENSIONLESS,
    SigmaHatStep,
    SigmaHatTrajectory,
    compute_eta,
    derive_eta_coupling,
    derive_polymer_boundary_channel_count,
    plot_sigma_hat_trajectory,
    sigma_hat_trajectory,
)

CANONICAL = HeatKernelConvention.CANONICAL


# --------------------------------------------------------------------------
# Derived η-coupling: replaces the previous PLACEHOLDER_ETA_COUPLING = 0.5
# --------------------------------------------------------------------------


def test_derive_eta_coupling_default_value() -> None:
    """Default fiducials (c_polymer=2, A_min=4) give η-coupling = 0.5,
    matching the previous placeholder value but now sourced from
    ``derive_eta_coupling`` rather than a bare literal."""
    assert derive_eta_coupling() == pytest.approx(0.5)


# --------------------------------------------------------------------------
# Combinatorial derivation of c_polymer (notes/sigma-hat-derivation.md §2.3-derivation)
# --------------------------------------------------------------------------


def test_derive_polymer_boundary_channel_count_returns_2() -> None:
    """The triangle-inequality derivation: |ΔT(X)| ≤ |T_{k+1}(X')| +
    |T_k(X)| ≤ 2 · max(...), so c_polymer = 2 is the worst-case channel
    multiplicity.  See notes/sigma-hat-derivation.md §2.3-derivation.

    Status reclassification (2026-05-25): previously HEURISTIC, now
    DERIVED via this returns-2 function."""
    assert derive_polymer_boundary_channel_count() == 2


def test_balaban_polymer_residual_sourced_from_derivation() -> None:
    """BALABAN_POLYMER_RESIDUAL is derived from the channel-count
    function rather than a bare literal — the post-2026-05-25 status
    upgrade from HEURISTIC to DERIVED."""
    assert BALABAN_POLYMER_RESIDUAL == float(
        derive_polymer_boundary_channel_count()
    )


def test_polymer_boundary_channel_count_is_integer() -> None:
    """The derivation returns a Nat (worst-case multiplicity is a count).
    Integer-valued by construction; relevant for any future Q'-lift."""
    n = derive_polymer_boundary_channel_count()
    assert isinstance(n, int)
    assert n > 0


def test_derived_eta_coupling_constant_matches_helper() -> None:
    """The module-level ``DERIVED_ETA_COUPLING`` constant equals the
    helper's default return value."""
    assert DERIVED_ETA_COUPLING == derive_eta_coupling()


def test_derive_eta_coupling_uses_balaban_and_wilson_constants() -> None:
    """The default coupling is the explicit ratio of the two fiducial
    constants: ``BALABAN_POLYMER_RESIDUAL / WILSON_LOOP_MIN_AREA_DIMENSIONLESS``."""
    expected = BALABAN_POLYMER_RESIDUAL / WILSON_LOOP_MIN_AREA_DIMENSIONLESS
    assert derive_eta_coupling() == pytest.approx(expected)


def test_derive_eta_coupling_scales_linearly_with_polymer_residual() -> None:
    """Doubling the Bałaban polymer-residual prefactor doubles the coupling."""
    base = derive_eta_coupling(polymer_residual=2.0)
    doubled = derive_eta_coupling(polymer_residual=4.0)
    assert doubled == pytest.approx(2.0 * base)


def test_derive_eta_coupling_scales_inversely_with_wilson_loop_area() -> None:
    """Doubling the smallest-Wilson-loop area (i.e. requiring larger loops
    in the area-law bound) halves the coupling."""
    base = derive_eta_coupling(wilson_loop_min_area=4)
    larger_area = derive_eta_coupling(wilson_loop_min_area=8)
    assert larger_area == pytest.approx(0.5 * base)


def test_derive_eta_coupling_rejects_nonpositive_inputs() -> None:
    with pytest.raises(ValueError, match="polymer_residual"):
        derive_eta_coupling(polymer_residual=0.0)
    with pytest.raises(ValueError, match="polymer_residual"):
        derive_eta_coupling(polymer_residual=-1.0)
    with pytest.raises(ValueError, match="wilson_loop_min_area"):
        derive_eta_coupling(wilson_loop_min_area=0)
    with pytest.raises(ValueError, match="wilson_loop_min_area"):
        derive_eta_coupling(wilson_loop_min_area=-2)


def test_compute_eta_default_uses_derived_coupling() -> None:
    """``compute_eta`` defaults to ``DERIVED_ETA_COUPLING`` rather than
    a bare literal; passing the constant explicitly yields the same result."""
    eta_default = compute_eta(0.1, 0.2, CANONICAL)
    eta_explicit = compute_eta(0.1, 0.2, CANONICAL, eta_coupling=DERIVED_ETA_COUPLING)
    assert eta_default == pytest.approx(eta_explicit)


def test_derived_eta_coupling_is_b_independent() -> None:
    """The derivation is b-independent (the block factor enters only via
    Δ_∩ through the g_k trajectory).  The helper has no ``b`` argument."""
    import inspect

    sig = inspect.signature(derive_eta_coupling)
    assert "b" not in sig.parameters
    assert "block_factor" not in sig.parameters


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
