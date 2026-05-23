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
    """Use g in convergent regime (g < 0.4) so 3.1 K_sf is finite."""
    ok = compute_overlap_kp(g_k=0.2)
    assert isinstance(ok, OverlapKP)
    assert ok.rho_cap > 0
    assert ok.K_cap >= 0
    assert ok.proposition_7_1_satisfied


def test_proposition_7_1_rho_is_min() -> None:
    """ρ_∩ = min(ρ_sf, ρ_lf), regardless of convergence regime."""
    ok = compute_overlap_kp(g_k=0.2)
    assert ok.rho_cap == min(ok.sf_part.rho_sf, ok.lf_part.rho_lf)


def test_proposition_7_1_K_at_upper_bound() -> None:
    """K_∩ = K_sf + K_lf (saturating Proposition 7.1's upper bound).

    In convergent regime (small g) so both K's are finite."""
    ok = compute_overlap_kp(g_k=0.2)
    assert ok.K_cap == pytest.approx(ok.sf_part.K_sf + ok.lf_part.K_lf)


def test_overlap_kp_canonical_su2_g_one() -> None:
    """At g=1 canonical: ρ_sf = 0.5 (Bałaban c_λ/g²), ρ_lf = 3/4 (3.2 derived).
    Buffer ρ_∩ = min = 0.5.

    At g=1, K_sf = ∞ (cluster expansion diverges, post-3.1-upgrade),
    so K_∩ = ∞ as well."""
    import math

    ok = compute_overlap_kp(g_k=1.0, t_choice=CANONICAL)
    assert ok.sf_part.rho_sf == pytest.approx(0.5)
    assert ok.lf_part.rho_lf == pytest.approx(0.75)
    assert ok.rho_cap == pytest.approx(0.5)
    # K is infinite in the non-convergent regime.
    assert math.isinf(ok.K_cap)
    assert not ok.sf_part.convergent


def test_overlap_kp_canonical_su2_convergent_regime() -> None:
    """At g = 0.2 (below convergence threshold), K's are finite."""
    import math

    ok = compute_overlap_kp(g_k=0.2, t_choice=CANONICAL)
    assert math.isfinite(ok.K_cap)
    assert ok.sf_part.convergent


def test_delta_cap_nonnegative_in_convergent_regime() -> None:
    """In convergent regime (small g), Δ_∩ ≥ 0."""
    assert delta_cap(0.1, 0.2, CANONICAL) >= 0
    assert delta_cap(0.2, 0.1, CANONICAL) >= 0


def test_delta_cap_zero_when_g_unchanged_convergent() -> None:
    """No change in g → no Δ_∩, in convergent regime."""
    assert delta_cap(0.2, 0.2, CANONICAL) == 0.0


def test_delta_cap_infinite_in_non_convergent_regime() -> None:
    """Above the cluster-expansion threshold, K's are ∞ → Δ_∩ = ∞."""
    import math

    d = delta_cap(0.8, 1.0, CANONICAL)
    assert math.isinf(d)


def test_delta_cap_grows_when_g_grows_in_convergent_regime() -> None:
    """K_sf grows with g (closer to threshold) → Δ_∩ > 0."""
    d = delta_cap(0.1, 0.3, CANONICAL)
    assert d > 0
    import math

    assert math.isfinite(d)


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


def test_delta_cap_budget_finite_in_convergent_regime() -> None:
    """In convergent regime (g < 0.4), Δ_∩ budget is finite."""
    import math

    g_traj = [0.1, 0.15, 0.2, 0.25, 0.3]
    result = delta_cap_budget(g_traj)
    assert math.isfinite(result.total)
    assert result.total >= 0


def test_delta_cap_budget_infinite_above_threshold() -> None:
    """If trajectory crosses convergence threshold, budget is ∞."""
    import math

    g_traj = [0.3, 0.5, 0.8, 1.0]  # crosses g_max ≈ 0.4
    result = delta_cap_budget(g_traj)
    assert math.isinf(result.total)


def test_overlap_kp_rho_cap_decreases_with_g() -> None:
    """ρ_cap ∝ 1/g² (inherited from sf/lf)."""
    rho1 = compute_overlap_kp(g_k=0.2).rho_cap
    rho2 = compute_overlap_kp(g_k=0.3).rho_cap
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
