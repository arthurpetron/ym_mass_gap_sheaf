"""Tests for `computations.fiducial_sensitivity`."""

from __future__ import annotations

import pytest

from computations.fiducial_sensitivity import (
    format_sweep_result,
    max_g0_closure,
    run_all_sweeps,
    sweep_mu_plaq,
    sweep_polymer_residual,
    sweep_spectral_gap_coeff,
)
from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import (
    MU_PLAQUETTE_4D,
    MU_PLAQUETTE_CONSERVATIVE_4D,
)


# --------------------------------------------------------------------------
# sweep_spectral_gap_coeff
# --------------------------------------------------------------------------


class TestSweepSpectralGapCoeff:
    def test_basic_run(self):
        result = sweep_spectral_gap_coeff()
        assert result.fiducial_name == "BAŁABAN_SPECTRAL_GAP_COEFF"
        assert len(result.points) >= 4
        # Every point reports a g_max_sf.
        for p in result.points:
            assert p.g_max_sf is not None
            assert p.g_max_sf > 0

    def test_g_max_monotone_in_c_lambda(self):
        # g_max_sf = √(c_λ · conv_factor / μ_sf); monotone in c_λ.
        result = sweep_spectral_gap_coeff(values=[0.1, 0.5, 1.0, 2.0])
        values = [p.g_max_sf for p in result.points]
        for a, b in zip(values, values[1:]):
            assert a < b, (
                f"g_max_sf should be monotone increasing in c_λ; "
                f"got {values}"
            )

    def test_custom_values(self):
        result = sweep_spectral_gap_coeff(values=[0.25, 1.0])
        assert len(result.points) == 2
        assert result.points[0].fiducial_value == 0.25
        assert result.points[1].fiducial_value == 1.0

    def test_sigma_eta_decreases_with_larger_c_lambda(self):
        # Larger c_λ ↔ stronger small-field decay rate ↔ smaller K_sf in
        # the convergent regime ↔ smaller Δ_∩ ↔ smaller Σ η_k.  Strict
        # monotonicity once threading is in place (2026-05-24).
        result = sweep_spectral_gap_coeff(
            values=[0.5, 0.75, 1.0, 1.5], g_0=0.30, K=3, sigma_hat_initial=10.0,
        )
        totals = [
            p.sigma_hat_trajectory_total_eta for p in result.points
        ]
        assert all(t is not None for t in totals)
        for a, b in zip(totals, totals[1:]):
            assert a > b, (
                f"Σ η_k should be monotone decreasing in c_λ; got {totals}"
            )


# --------------------------------------------------------------------------
# sweep_mu_plaq
# --------------------------------------------------------------------------


class TestSweepMuPlaq:
    def test_basic_run(self):
        result = sweep_mu_plaq()
        assert result.fiducial_name == "MU_PLAQUETTE_4D"
        assert len(result.points) >= 4
        for p in result.points:
            assert p.g_max_lf is not None

    def test_includes_default_and_conservative(self):
        result = sweep_mu_plaq()
        values = [p.fiducial_value for p in result.points]
        assert MU_PLAQUETTE_4D in values
        # Conservative is included (within tolerance for float compare).
        assert any(abs(v - MU_PLAQUETTE_CONSERVATIVE_4D) < 1e-9 for v in values)

    def test_conservative_shrinks_g_max(self):
        # Larger μ_plaq ↔ smaller g_max_lf.
        result = sweep_mu_plaq(values=[MU_PLAQUETTE_4D, MU_PLAQUETTE_CONSERVATIVE_4D])
        g_default = result.points[0].g_max_lf
        g_conservative = result.points[1].g_max_lf
        assert g_conservative < g_default, (
            f"Conservative μ_plaq = 8e should shrink g_max_lf; "
            f"got default={g_default}, conservative={g_conservative}"
        )

    def test_g_max_monotone_in_mu_plaq(self):
        # g_max_lf monotonically decreases as μ_plaq grows (less room for
        # cluster expansion to converge).
        result = sweep_mu_plaq(values=[8.0, 16.0, 32.0, 64.0])
        values = [p.g_max_lf for p in result.points]
        for a, b in zip(values, values[1:]):
            assert a > b, (
                f"g_max_lf should be monotone decreasing in μ_plaq; "
                f"got {values}"
            )

    def test_sigma_eta_increases_with_larger_mu_plaq(self):
        # Larger μ_plaq → smaller g_max_lf → larger K_lf at any fixed
        # convergent g (more polymers admitted) → larger Δ_∩ → larger
        # Σ η_k.  Threading verified (since 2026-05-24).
        result = sweep_mu_plaq(
            values=[8.0, 16.0, 21.0], g_0=0.30, K=3, sigma_hat_initial=10.0,
        )
        totals = [
            p.sigma_hat_trajectory_total_eta for p in result.points
        ]
        assert all(t is not None for t in totals)
        for a, b in zip(totals, totals[1:]):
            assert a < b, (
                f"Σ η_k should be monotone increasing in μ_plaq; got {totals}"
            )


# --------------------------------------------------------------------------
# sweep_polymer_residual
# --------------------------------------------------------------------------


class TestSweepPolymerResidual:
    def test_basic_run(self):
        result = sweep_polymer_residual()
        assert result.fiducial_name == "BALABAN_POLYMER_RESIDUAL"
        assert len(result.points) >= 4
        # Each point has a Σ η_k.
        for p in result.points:
            assert p.sigma_hat_trajectory_total_eta is not None
            assert p.sigma_hat_trajectory_budget_closes is not None

    def test_eta_monotone_in_polymer_residual(self):
        # η_k = (c_polymer / A_min) · Δ_∩.  Larger c_polymer → larger η_k →
        # larger Σ η_k.  Monotone in the polymer residual.
        result = sweep_polymer_residual(values=[0.5, 1.0, 2.0, 4.0])
        totals = [
            p.sigma_hat_trajectory_total_eta for p in result.points
        ]
        for a, b in zip(totals, totals[1:]):
            assert a < b, (
                f"Σ η_k should be monotone increasing in c_polymer; "
                f"got {totals}"
            )

    def test_pilot_closes_at_default(self):
        # At default σ̂_0 = 1.0 and g_0 = 0.30, the default
        # polymer_residual = 2 gives Σ η_k ≈ 3e-3 ≪ 1.  Closure holds.
        result = sweep_polymer_residual(values=[2.0])
        p = result.points[0]
        assert p.sigma_hat_trajectory_budget_closes is True
        assert p.sigma_hat_trajectory_total_eta < 1.0

    def test_pilot_fails_at_extreme(self):
        # Pump σ̂_0 down to a value just slightly above the actual Σ η_k
        # at default c_polymer (≈3.09e-3); then doubling c_polymer should
        # break closure.
        # Step 1: measure default total η.
        default_run = sweep_polymer_residual(values=[2.0], sigma_hat_initial=1.0)
        baseline_eta = default_run.points[0].sigma_hat_trajectory_total_eta
        # Step 2: set σ̂_0 between baseline_eta and 2 · baseline_eta.
        tight_sigma_0 = baseline_eta * 1.5
        result = sweep_polymer_residual(
            values=[2.0, 4.0], sigma_hat_initial=tight_sigma_0
        )
        # At c_polymer = 2, Σ η ≈ baseline ≈ 2/3 of σ̂_0 → closure OK.
        # At c_polymer = 4, Σ η ≈ 2·baseline ≈ 4/3 of σ̂_0 → closure FAILS.
        assert result.points[0].sigma_hat_trajectory_budget_closes is True
        assert result.points[1].sigma_hat_trajectory_budget_closes is False


# --------------------------------------------------------------------------
# run_all_sweeps + format
# --------------------------------------------------------------------------


class TestRunAllAndFormat:
    def test_run_all_keys(self):
        sweeps = run_all_sweeps()
        assert set(sweeps.keys()) == {
            "BAŁABAN_SPECTRAL_GAP_COEFF",
            "MU_PLAQUETTE_4D",
            "BALABAN_POLYMER_RESIDUAL",
        }

    def test_format_smoke(self):
        sweeps = run_all_sweeps()
        for name, result in sweeps.items():
            formatted = format_sweep_result(result)
            assert name in formatted
            assert "value" in formatted
            assert "default value" in formatted

    def test_wilson_convention(self):
        # Sanity: the conventions plumb through without error.
        sweeps = run_all_sweeps(convention=HeatKernelConvention.WILSON)
        for result in sweeps.values():
            for p in result.points:
                assert p.convention is HeatKernelConvention.WILSON


# --------------------------------------------------------------------------
# max_g0_closure
# --------------------------------------------------------------------------


class TestMaxG0Closure:
    def test_default_in_known_range(self):
        # The default pilot fails at g_0 = 1.0 and passes well below
        # g_0 = 0.40 (sf threshold).  The bisection should land
        # somewhere in (0.30, 0.42) for the canonical convention.
        g_max = max_g0_closure(K=3, sigma_hat_initial=1.0)
        assert 0.10 < g_max < 0.50, f"unexpected default g_0_max: {g_max}"

    def test_conservative_mu_plaq_does_not_grow_window(self):
        # Larger μ_plaq tightens the convergent regime; the pilot
        # window cannot grow when switching to the conservative value.
        g_default = max_g0_closure(K=3, sigma_hat_initial=1.0)
        g_conservative = max_g0_closure(
            K=3, sigma_hat_initial=1.0,
            mu_plaq=MU_PLAQUETTE_CONSERVATIVE_4D,
        )
        assert g_conservative <= g_default + 1e-3, (
            f"conservative μ_plaq should not enlarge the pilot window; "
            f"default={g_default}, conservative={g_conservative}"
        )

    def test_tighter_sf_grows_window(self):
        # Larger c_λ → small-field expansion converges in a larger
        # g window → larger pilot window.
        g_default = max_g0_closure(K=3, sigma_hat_initial=1.0)
        g_tight = max_g0_closure(
            K=3, sigma_hat_initial=1.0, spectral_gap_coeff=1.0,
        )
        assert g_tight > g_default - 1e-3, (
            f"tighter sf (c_λ=1.0) should not shrink the window; "
            f"default={g_default}, tight={g_tight}"
        )

    def test_search_bounds_honoured(self):
        # If the upper end is set below the actual threshold, the result
        # is the upper end.
        g_max = max_g0_closure(g_search_range=(1e-3, 0.05))
        assert abs(g_max - 0.05) < 1e-3

    def test_loose_sf_shrinks_window(self):
        # Smaller c_λ → small-field expansion convergent window
        # shrinks → smaller pilot window (or pilot may fail entirely
        # if K_sf blows up at every g_0 in range).
        g_default = max_g0_closure(K=3, sigma_hat_initial=1.0)
        g_loose = max_g0_closure(
            K=3, sigma_hat_initial=1.0, spectral_gap_coeff=0.3,
        )
        assert g_loose <= g_default + 1e-3, (
            f"loose sf (c_λ=0.3) should not enlarge the window; "
            f"default={g_default}, loose={g_loose}"
        )
