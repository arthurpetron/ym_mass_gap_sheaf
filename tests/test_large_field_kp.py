"""Tests for `computations.large_field_kp` (Milestone 3.2)."""

from __future__ import annotations

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import (
    LargeFieldKP,
    compute_large_field_kp,
    eps_lf,
    first_few_rg_steps,
)

CANONICAL = HeatKernelConvention.CANONICAL
WILSON = HeatKernelConvention.WILSON
MANTON = HeatKernelConvention.MANTON


def test_lf_kp_structure() -> None:
    kp = compute_large_field_kp(g_k=1.0)
    assert isinstance(kp, LargeFieldKP)
    assert kp.rho_lf > 0
    assert kp.K_lf >= 0


def test_lf_rho_canonical_is_three_quarters_at_g_one() -> None:
    """In canonical, ρ_lf at g=1 is exactly C_2(1/2) = 3/4."""
    kp = compute_large_field_kp(g_k=1.0, t_choice=CANONICAL)
    assert kp.rho_lf == pytest.approx(0.75)


def test_lf_rho_wilson_is_three_at_g_one() -> None:
    """In Wilson, ρ_lf at g=1 is 2N · C_2 = 3."""
    kp = compute_large_field_kp(g_k=1.0, t_choice=WILSON)
    assert kp.rho_lf == pytest.approx(3.0)


def test_lf_rho_scales_one_over_g_squared() -> None:
    kp1 = compute_large_field_kp(g_k=1.0)
    kp2 = compute_large_field_kp(g_k=2.0)
    assert kp2.rho_lf == pytest.approx(kp1.rho_lf / 4.0)


def test_lf_manton_rejected() -> None:
    with pytest.raises(ValueError, match="Manton"):
        compute_large_field_kp(g_k=1.0, t_choice=MANTON)


def test_lf_eps_nonnegative() -> None:
    assert eps_lf(0.8, 1.0, CANONICAL) >= 0
    assert eps_lf(1.0, 0.8, CANONICAL) >= 0


def test_lf_eps_positive_when_g_grows() -> None:
    assert eps_lf(0.8, 1.0, CANONICAL) > 0


def test_lf_provenance_marks_K_lf_placeholder() -> None:
    """rho_lf is DERIVED; K_lf is placeholder."""
    kp = compute_large_field_kp(g_k=1.0)
    assert "DERIVED" in kp.provenance["rho_lf"]
    assert "PLACEHOLDER" in kp.provenance["K_lf"]


def test_lf_input_validation() -> None:
    with pytest.raises(ValueError):
        compute_large_field_kp(g_k=0.0)
    with pytest.raises(ValueError):
        compute_large_field_kp(g_k=1.0, scale_k=-1)


def test_lf_trajectory_output() -> None:
    g_traj = [1.0, 1.1, 1.2]
    kps = first_few_rg_steps(g_traj)
    assert len(kps) == 3
    # rho_lf decreases as g_k grows.
    for i in range(len(kps) - 1):
        assert kps[i].rho_lf > kps[i + 1].rho_lf
