"""Tests for `computations.overlap_kp` (Milestone 3.3)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.overlap_kp import (
    DeltaCapBudgetResult,
    OverlapKP,
    compute_overlap_kp,
    delta_cap,
    delta_cap_budget,
    first_few_rg_steps,
    plot_delta_cap_budget,
)

CANONICAL = HeatKernelConvention.CANONICAL


def test_overlap_kp_structure() -> None:
    ok = compute_overlap_kp(g_k=1.0)
    assert isinstance(ok, OverlapKP)
    assert ok.rho_cap > 0
    assert ok.K_cap >= 0
    assert ok.proposition_7_1_satisfied


def test_proposition_7_1_rho_is_min() -> None:
    """ρ_∩ = min(ρ_sf, ρ_lf)."""
    ok = compute_overlap_kp(g_k=1.0)
    assert ok.rho_cap == min(ok.sf_part.rho_sf, ok.lf_part.rho_lf)


def test_proposition_7_1_K_at_upper_bound() -> None:
    """K_∩ = K_sf + K_lf (saturating Proposition 7.1's upper bound)."""
    ok = compute_overlap_kp(g_k=1.0)
    assert ok.K_cap == pytest.approx(ok.sf_part.K_sf + ok.lf_part.K_lf)


def test_overlap_kp_canonical_su2_g_one() -> None:
    """At g=1 canonical: ρ_sf = 1/2 (3.1 placeholder), ρ_lf = 3/4 (3.2 derived).
    Buffer ρ_∩ = min = 1/2."""
    ok = compute_overlap_kp(g_k=1.0, t_choice=CANONICAL)
    assert ok.sf_part.rho_sf == pytest.approx(0.5)
    assert ok.lf_part.rho_lf == pytest.approx(0.75)
    assert ok.rho_cap == pytest.approx(0.5)


def test_delta_cap_nonnegative() -> None:
    assert delta_cap(0.8, 1.0, CANONICAL) >= 0
    assert delta_cap(1.0, 1.0, CANONICAL) == 0  # no change → no growth


def test_delta_cap_with_placeholder_K_is_zero() -> None:
    """With placeholder K_sf = K_lf = 1.0 (g-independent), Δ_∩ = 0."""
    assert delta_cap(0.8, 1.2, CANONICAL) == 0.0


def test_overlap_kp_trajectory() -> None:
    g_traj = [1.0, 1.1, 1.2]
    oks = first_few_rg_steps(g_traj)
    assert len(oks) == 3
    for ok in oks:
        assert ok.proposition_7_1_satisfied


def test_delta_cap_budget_result_shape() -> None:
    g_traj = [1.0, 1.1, 1.2, 1.3]
    result = delta_cap_budget(g_traj)
    assert isinstance(result, DeltaCapBudgetResult)
    # n_steps = len(g_traj) - 1 (differences).
    assert result.n_steps == 3
    assert len(result.per_step) == 3
    assert len(result.partial_sums) == 3
    # Partial sums monotone.
    for i in range(len(result.partial_sums) - 1):
        assert result.partial_sums[i] <= result.partial_sums[i + 1]


def test_delta_cap_budget_total_is_sum() -> None:
    g_traj = [1.0, 1.1, 1.2]
    result = delta_cap_budget(g_traj)
    assert result.total == pytest.approx(sum(result.per_step))


def test_delta_cap_budget_zero_with_placeholders() -> None:
    """Placeholders give Δ_∩ = 0 per step; total = 0."""
    g_traj = [0.8, 0.9, 1.0, 1.1, 1.2]
    result = delta_cap_budget(g_traj)
    assert result.total == pytest.approx(0.0)


def test_overlap_kp_rho_cap_decreases_with_g() -> None:
    """ρ_cap ∝ 1/g² (inherited from sf/lf)."""
    rho1 = compute_overlap_kp(g_k=1.0).rho_cap
    rho2 = compute_overlap_kp(g_k=2.0).rho_cap
    assert rho2 < rho1


def test_overlap_kp_input_validation() -> None:
    with pytest.raises(ValueError):
        compute_overlap_kp(g_k=0.0)
    with pytest.raises(ValueError):
        compute_overlap_kp(g_k=1.0, scale_k=-1)


def test_plot_writes_svg(tmp_path: Path) -> None:
    out = tmp_path / "test.svg"
    result = plot_delta_cap_budget(output_path=str(out))
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0
