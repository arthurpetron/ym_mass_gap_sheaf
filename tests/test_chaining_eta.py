"""Tests for the chaining tightening of η_k (Milestone 6.5-eta).

Verifies that threading the Phase-6.5 chaining factor into the
σ̂-budget derivation:

  (a) reduces each η_k strictly (c_chain ∈ (0, 1]);
  (b) reduces Σ η_k strictly;
  (c) lifts the constructive m_0 lower bound (or leaves it unchanged
      at the /1000 rational resolution when the underlying float
      uplift is sub-bin);
  (d) preserves the σ̂-budget closure (chaining never makes the
      budget fail when the baseline closes);
  (e) at g_k = 0 reduces to the baseline (c_chain(0) = 1);
  (f) respects the chaining regime check (g_k ≤ G_MAX_CHAIN).
"""

from __future__ import annotations

import math

import pytest

from computations.chaining_estimate import (
    G_MAX_CHAIN,
    PER_CHANNEL_CORRELATION_STRENGTH,
    SHARED_LINK_CHANNEL_MULTIPLICITY,
    chain_factor,
)
from computations.heat_kernel import HeatKernelConvention
from computations.mass_gap_bound import derive_mass_gap_bound
from computations.overlap_measure import standard_su2_trajectory
from computations.sigma_hat_trajectory import (
    compute_eta,
    sigma_hat_trajectory,
)


# --------------------------------------------------------------------------
# compute_eta
# --------------------------------------------------------------------------


def test_compute_eta_chaining_off_matches_baseline() -> None:
    """`use_chaining=False` matches the pre-2026-05-27 behavior."""
    g_k, g_k_next = 0.30, 0.3005
    base_off = compute_eta(g_k, g_k_next, HeatKernelConvention.CANONICAL,
                           use_chaining=False)
    legacy_call = compute_eta(g_k, g_k_next, HeatKernelConvention.CANONICAL)
    assert base_off == legacy_call


def test_compute_eta_chaining_strictly_smaller_at_positive_g() -> None:
    """At any g > 0, c_chain(g) < 1, so the chaining η is strictly smaller."""
    g_k, g_k_next = 0.30, 0.3005
    base = compute_eta(g_k, g_k_next, HeatKernelConvention.CANONICAL,
                       use_chaining=False)
    chain = compute_eta(g_k, g_k_next, HeatKernelConvention.CANONICAL,
                        use_chaining=True)
    assert chain < base
    # The ratio is c_chain(g_k) (since the rest of the η factor is shared).
    expected_ratio = chain_factor(g_k)
    assert math.isclose(chain / base, expected_ratio, rel_tol=1e-9)


def test_chain_factor_at_zero_is_unity() -> None:
    """At g = 0 the chaining factor c_chain(0) = exp(0) = 1, so the
    chaining bound recovers the union bound exactly.  (compute_eta
    itself rejects g_k = 0 upstream in the KP module, so we verify the
    chaining tightening's free-limit property at the factor level.)"""
    assert chain_factor(0.0) == 1.0


def test_compute_eta_chaining_factor_approaches_one_at_small_g() -> None:
    """c_chain(g) → 1 as g → 0, so the chaining and baseline η values
    converge in the deep weak-coupling limit."""
    g_small = 1e-4
    g_next = 1.1e-4
    base = compute_eta(g_small, g_next, HeatKernelConvention.CANONICAL,
                       use_chaining=False)
    chain = compute_eta(g_small, g_next, HeatKernelConvention.CANONICAL,
                        use_chaining=True)
    # At g = 1e-4, c_chain = exp(-4 * 1e-8 * 0.5) ≈ 1 - 2e-8
    # The two should be numerically nearly identical.
    if base > 0:
        assert math.isclose(chain, base, rel_tol=1e-6)


def test_compute_eta_chaining_fiducial_overrides() -> None:
    """`chain_n_share` and `chain_zeta` override the chaining fiducials."""
    g_k, g_k_next = 0.30, 0.3005
    eta_default = compute_eta(g_k, g_k_next, HeatKernelConvention.CANONICAL,
                              use_chaining=True)
    eta_no_share = compute_eta(g_k, g_k_next, HeatKernelConvention.CANONICAL,
                               use_chaining=True, chain_n_share=0)
    # With n_share=0, c_chain(g) = exp(0) = 1, so chaining = baseline
    eta_baseline = compute_eta(g_k, g_k_next, HeatKernelConvention.CANONICAL,
                               use_chaining=False)
    assert eta_no_share == eta_baseline
    assert eta_default < eta_no_share


def test_compute_eta_chaining_rejects_strong_coupling() -> None:
    """The chaining regime ends at g_k = G_MAX_CHAIN = 2.0."""
    with pytest.raises(RuntimeError, match="G_MAX_CHAIN"):
        compute_eta(G_MAX_CHAIN + 0.01, G_MAX_CHAIN + 0.005,
                    HeatKernelConvention.CANONICAL, use_chaining=True)


# --------------------------------------------------------------------------
# sigma_hat_trajectory
# --------------------------------------------------------------------------


def test_sigma_hat_trajectory_chaining_reduces_total_eta() -> None:
    """Σ η_k is strictly smaller with chaining at the canonical pilot."""
    g_traj = standard_su2_trajectory(k_max=3, g_0=0.30)[0]
    base = sigma_hat_trajectory(g_traj, use_chaining=False)
    chain = sigma_hat_trajectory(g_traj, use_chaining=True)
    assert chain.total_eta < base.total_eta


def test_sigma_hat_trajectory_chaining_eta_step_pattern() -> None:
    """Each per-step η_k satisfies the chaining-vs-baseline ratio = c_chain(g_k)."""
    g_traj = standard_su2_trajectory(k_max=3, g_0=0.30)[0]
    base = sigma_hat_trajectory(g_traj, use_chaining=False)
    chain = sigma_hat_trajectory(g_traj, use_chaining=True)
    for sb, sc in zip(base.steps[:-1], chain.steps[:-1]):
        if sb.eta_k > 0:
            ratio = sc.eta_k / sb.eta_k
            expected = chain_factor(sb.g_k)
            assert math.isclose(ratio, expected, rel_tol=1e-9)


def test_sigma_hat_trajectory_chaining_preserves_closure() -> None:
    """Chaining never breaks budget closure when baseline closes."""
    g_traj = standard_su2_trajectory(k_max=3, g_0=0.30)[0]
    base = sigma_hat_trajectory(g_traj, use_chaining=False)
    chain = sigma_hat_trajectory(g_traj, use_chaining=True)
    if base.budget_closure:
        assert chain.budget_closure


def test_sigma_hat_trajectory_chaining_canonical_uplift() -> None:
    """At canonical pilot, chaining gives a measurable Σ η reduction.

    Empirical (2026-05-27): chaining cuts Σ η by ≈16.5% at g_0 = 0.30,
    K = 3 (c_chain(0.30) ≈ 0.8353).
    """
    g_traj = standard_su2_trajectory(k_max=3, g_0=0.30)[0]
    base = sigma_hat_trajectory(g_traj, use_chaining=False)
    chain = sigma_hat_trajectory(g_traj, use_chaining=True)
    reduction = chain.total_eta / base.total_eta
    # Expect ~0.835, give wide tolerance for trajectory-evolution detail.
    assert 0.75 < reduction < 0.90


# --------------------------------------------------------------------------
# derive_mass_gap_bound — manuscript-quotable m_0 uplift
# --------------------------------------------------------------------------


def test_derive_mass_gap_bound_chaining_preserves_closure() -> None:
    """The constructive bound still closes under chaining at the canonical pilot."""
    bound = derive_mass_gap_bound(use_chaining=True)
    assert bound.bound_check_passes


def test_derive_mass_gap_bound_chaining_m_0_at_least_baseline() -> None:
    """Chaining m_0 ≥ baseline m_0 — the lower bound can never weaken."""
    base = derive_mass_gap_bound(use_chaining=False)
    chain = derive_mass_gap_bound(use_chaining=True)
    assert chain.m_0_float >= base.m_0_float


def test_derive_mass_gap_bound_chaining_m_0_uplift_at_K_10() -> None:
    """The headline manuscript claim: at K=10 chaining uplifts m_0
    from 997/1000 to 998/1000 (uplift ratio ≈ 1.001)."""
    base = derive_mass_gap_bound(K=10, use_chaining=False)
    chain = derive_mass_gap_bound(K=10, use_chaining=True)
    assert chain.m_0_numerator >= base.m_0_numerator + 1
    # Ratio is at least 1.0005, well above sub-resolution noise.
    assert chain.m_0_float / base.m_0_float >= 1.0005


def test_derive_mass_gap_bound_chaining_m_0_uplift_near_threshold() -> None:
    """Near the convergent threshold (g_0 = 0.40), chaining gives a
    substantial m_0 uplift — both numerator-bump and ratio-uplift."""
    base = derive_mass_gap_bound(g_0=0.40, K=5, use_chaining=False)
    chain = derive_mass_gap_bound(g_0=0.40, K=5, use_chaining=True)
    # Multi-percent uplift at the threshold.
    assert chain.m_0_float / base.m_0_float > 1.05


# --------------------------------------------------------------------------
# Wiring sanity
# --------------------------------------------------------------------------


def test_chaining_fiducials_documented() -> None:
    """The chaining fiducials referenced in the trajectory module match
    the chaining_estimate module's defaults."""
    assert SHARED_LINK_CHANNEL_MULTIPLICITY == 4
    assert PER_CHANNEL_CORRELATION_STRENGTH == 0.5
    # c_chain(0.30) ≈ 0.8353 (the canonical-pilot value).
    assert 0.83 < chain_factor(0.30) < 0.84
