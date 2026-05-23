"""Tests for `computations.small_field_kp` (Milestone 3.1, post-3.1-upgrade)."""

from __future__ import annotations

import math

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.small_field_kp import (
    BAŁABAN_SPECTRAL_GAP_COEFF,
    MU_CONNECTIVITY_4D,
    SmallFieldKP,
    compute_small_field_kp,
    convergence_threshold_g,
    eps_sf,
    first_few_rg_steps,
)

CANONICAL = HeatKernelConvention.CANONICAL
WILSON = HeatKernelConvention.WILSON
MANTON = HeatKernelConvention.MANTON


# --------------------------------------------------------------------------
# Structure
# --------------------------------------------------------------------------


def test_kp_is_SmallFieldKP() -> None:
    kp = compute_small_field_kp(g_k=1.0)
    assert isinstance(kp, SmallFieldKP)


def test_rho_sf_positive() -> None:
    for g in (0.1, 0.4, 0.8, 1.2, 2.0):
        assert compute_small_field_kp(g).rho_sf > 0


def test_K_sf_nonneg_or_infinite() -> None:
    """K_sf is either finite ≥ 0 or +∞."""
    for g in (0.1, 0.4, 0.8, 1.2, 2.0):
        kp = compute_small_field_kp(g)
        assert kp.K_sf >= 0  # ∞ ≥ 0 is True


def test_convergent_flag_is_bool() -> None:
    kp = compute_small_field_kp(g_k=0.2)
    assert isinstance(kp.convergent, bool)


# --------------------------------------------------------------------------
# Literature-grounded constants and convergence threshold
# --------------------------------------------------------------------------


def test_balaban_coefficient_is_one_half() -> None:
    """Fiducial value from the Bałaban-literature shape."""
    assert float(BAŁABAN_SPECTRAL_GAP_COEFF) == 0.5


def test_mu_connectivity_4d_is_log_8e() -> None:
    """4D cubic-lattice connectivity constant from Brydges–Federbush."""
    assert MU_CONNECTIVITY_4D == pytest.approx(math.log(8.0 * math.e))


def test_convergence_threshold_su2_canonical() -> None:
    """g_max = sqrt(c_λ / μ) ≈ 0.40 in canonical convention."""
    g_max = convergence_threshold_g(CANONICAL)
    assert g_max == pytest.approx(math.sqrt(0.5 / MU_CONNECTIVITY_4D), rel=1e-6)
    # Numerically ≈ 0.403.
    assert 0.39 < g_max < 0.41


def test_convergence_threshold_wilson_is_2x_canonical() -> None:
    """Wilson picks up factor 4 in rate → factor 2 in g_max."""
    g_max_can = convergence_threshold_g(CANONICAL)
    g_max_wil = convergence_threshold_g(WILSON)
    assert g_max_wil == pytest.approx(2.0 * g_max_can)


# --------------------------------------------------------------------------
# Convergence behavior
# --------------------------------------------------------------------------


def test_K_sf_finite_below_threshold() -> None:
    """At g_k well below g_max, K_sf is finite."""
    kp = compute_small_field_kp(g_k=0.1, t_choice=CANONICAL)
    assert kp.convergent is True
    assert math.isfinite(kp.K_sf)
    assert kp.K_sf >= 1.0  # K = 1/(1-exp(-(ρ-μ))) ≥ 1


def test_K_sf_infinite_above_threshold() -> None:
    """At g_k above g_max, K_sf is ∞ (cluster expansion diverges)."""
    kp = compute_small_field_kp(g_k=1.0, t_choice=CANONICAL)
    assert kp.convergent is False
    assert math.isinf(kp.K_sf)


def test_K_sf_finite_at_threshold_minus() -> None:
    """Just below g_max, K_sf is finite (and large)."""
    g_max = convergence_threshold_g(CANONICAL)
    kp = compute_small_field_kp(g_k=g_max * 0.95, t_choice=CANONICAL)
    assert kp.convergent is True
    assert math.isfinite(kp.K_sf)


def test_K_sf_infinite_at_threshold_plus() -> None:
    """Just above g_max, K_sf is ∞."""
    g_max = convergence_threshold_g(CANONICAL)
    kp = compute_small_field_kp(g_k=g_max * 1.05, t_choice=CANONICAL)
    assert kp.convergent is False


# --------------------------------------------------------------------------
# Convention handling
# --------------------------------------------------------------------------


def test_wilson_rho_sf_is_4x_canonical() -> None:
    kp_can = compute_small_field_kp(g_k=1.0, t_choice=CANONICAL)
    kp_wil = compute_small_field_kp(g_k=1.0, t_choice=WILSON)
    assert kp_wil.rho_sf == pytest.approx(4.0 * kp_can.rho_sf)


def test_manton_rejected() -> None:
    with pytest.raises(ValueError, match="Manton"):
        compute_small_field_kp(g_k=1.0, t_choice=MANTON)


# --------------------------------------------------------------------------
# g_k scaling
# --------------------------------------------------------------------------


def test_rho_sf_scales_as_one_over_g_squared() -> None:
    kp1 = compute_small_field_kp(g_k=0.2)
    kp2 = compute_small_field_kp(g_k=0.4)
    assert kp2.rho_sf == pytest.approx(kp1.rho_sf / 4.0)


def test_rho_sf_decreases_in_g() -> None:
    rhos = [compute_small_field_kp(g_k=g).rho_sf for g in (0.1, 0.2, 0.5, 1.0)]
    for i in range(len(rhos) - 1):
        assert rhos[i] > rhos[i + 1]


# --------------------------------------------------------------------------
# eps_sf budget
# --------------------------------------------------------------------------


def test_eps_sf_nonnegative() -> None:
    assert eps_sf(0.1, 0.2, CANONICAL) >= 0
    assert eps_sf(0.2, 0.1, CANONICAL) >= 0


def test_eps_sf_zero_when_g_unchanged() -> None:
    assert eps_sf(0.2, 0.2, CANONICAL) == pytest.approx(0.0)


def test_eps_sf_positive_when_g_increases() -> None:
    """When g grows, ρ_sf shrinks → eps_sf > 0."""
    assert eps_sf(0.1, 0.2, CANONICAL) > 0


# --------------------------------------------------------------------------
# Provenance + status
# --------------------------------------------------------------------------


def test_provenance_marks_literature_synthesis() -> None:
    """Provenance cites Bałaban + Brydges-Federbush; no more 'placeholder'."""
    kp = compute_small_field_kp(g_k=0.2)
    assert "Bałaban" in kp.provenance["rho_sf"]
    assert "Brydges" in kp.provenance["K_sf"]
    assert "literature-grounded" in kp.provenance["status"]


# --------------------------------------------------------------------------
# Input validation + trajectory
# --------------------------------------------------------------------------


def test_rejects_nonpositive_g() -> None:
    with pytest.raises(ValueError):
        compute_small_field_kp(g_k=0.0)
    with pytest.raises(ValueError):
        compute_small_field_kp(g_k=-1.0)


def test_rejects_negative_scale() -> None:
    with pytest.raises(ValueError):
        compute_small_field_kp(g_k=1.0, scale_k=-1)


def test_first_few_rg_steps_returns_per_scale() -> None:
    g_traj = [0.1, 0.15, 0.2, 0.25]
    kps = first_few_rg_steps(g_traj)
    assert len(kps) == 4
    for k, kp in enumerate(kps):
        assert kp.scale_k == k
        assert kp.g_k == g_traj[k]


def test_first_few_rg_steps_convergent_in_small_g_regime() -> None:
    g_traj = [0.1, 0.15, 0.2, 0.25]  # all below g_max ≈ 0.4
    kps = first_few_rg_steps(g_traj)
    for kp in kps:
        assert kp.convergent
        assert math.isfinite(kp.K_sf)
