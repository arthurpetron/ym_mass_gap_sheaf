"""Tests for `computations.small_field_kp` (Milestone 3.1)."""

from __future__ import annotations

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.small_field_kp import (
    SmallFieldKP,
    compute_small_field_kp,
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
    for g in (0.4, 0.8, 1.2, 2.0):
        assert compute_small_field_kp(g).rho_sf > 0


def test_K_sf_nonnegative() -> None:
    for g in (0.4, 0.8, 1.2, 2.0):
        assert compute_small_field_kp(g).K_sf >= 0


def test_provenance_marks_placeholder() -> None:
    kp = compute_small_field_kp(g_k=1.0)
    assert "placeholder" in kp.provenance["status"].lower()
    assert "PLACEHOLDER" in kp.provenance["rho_sf"]
    assert "PLACEHOLDER" in kp.provenance["K_sf"]


# --------------------------------------------------------------------------
# Convention handling
# --------------------------------------------------------------------------


def test_wilson_rho_sf_is_4x_canonical() -> None:
    """Wilson convention picks up the 2N = 4 factor."""
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
    """ρ_sf ∝ 1/g² in the placeholder: doubling g should quarter ρ_sf."""
    kp1 = compute_small_field_kp(g_k=1.0)
    kp2 = compute_small_field_kp(g_k=2.0)
    assert kp2.rho_sf == pytest.approx(kp1.rho_sf / 4.0)


def test_rho_sf_decreases_in_g() -> None:
    """ρ_sf decreases as g_k grows."""
    rhos = [compute_small_field_kp(g_k=g).rho_sf for g in (0.5, 1.0, 1.5, 2.0)]
    for i in range(len(rhos) - 1):
        assert rhos[i] > rhos[i + 1]


# --------------------------------------------------------------------------
# eps_sf budget
# --------------------------------------------------------------------------


def test_eps_sf_nonnegative() -> None:
    """ε_sf is non-negative (it's a degradation budget)."""
    assert eps_sf(g_k=0.8, g_k_next=1.0, t_choice=CANONICAL) >= 0
    assert eps_sf(g_k=1.0, g_k_next=0.8, t_choice=CANONICAL) >= 0


def test_eps_sf_zero_when_g_unchanged() -> None:
    """No degradation if the coupling doesn't change."""
    assert eps_sf(g_k=1.0, g_k_next=1.0, t_choice=CANONICAL) == pytest.approx(0.0)


def test_eps_sf_positive_when_g_increases() -> None:
    """Going in the confinement direction (g grows), ρ_sf decreases — ε > 0."""
    assert eps_sf(g_k=0.8, g_k_next=1.0, t_choice=CANONICAL) > 0


# --------------------------------------------------------------------------
# Input validation
# --------------------------------------------------------------------------


def test_rejects_nonpositive_g() -> None:
    with pytest.raises(ValueError):
        compute_small_field_kp(g_k=0.0)
    with pytest.raises(ValueError):
        compute_small_field_kp(g_k=-1.0)


def test_rejects_negative_scale() -> None:
    with pytest.raises(ValueError):
        compute_small_field_kp(g_k=1.0, scale_k=-1)


# --------------------------------------------------------------------------
# Trajectory
# --------------------------------------------------------------------------


def test_first_few_rg_steps_returns_per_scale() -> None:
    g_traj = [1.0, 1.1, 1.2, 1.3]
    kps = first_few_rg_steps(g_traj)
    assert len(kps) == 4
    for k, kp in enumerate(kps):
        assert kp.scale_k == k
        assert kp.g_k == g_traj[k]
