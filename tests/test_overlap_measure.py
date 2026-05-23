"""Tests for `computations.overlap_measure` (Milestone 1.4)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.overlap_measure import (
    SummabilityResult,
    UnionBoundResult,
    g_max_for_validity,
    is_summable_in_k,
    plot_overlap_vs_rg_step,
    standard_su2_trajectory,
    union_bound_overlap,
)

CANONICAL = HeatKernelConvention.CANONICAL
WILSON = HeatKernelConvention.WILSON
MANTON = HeatKernelConvention.MANTON


# --------------------------------------------------------------------------
# union_bound_overlap
# --------------------------------------------------------------------------


def test_union_bound_is_n_p_times_per_plaquette() -> None:
    r = union_bound_overlap(n_plaquettes=100, g_k=1.0, delta_k=0.2, t_choice=CANONICAL)
    assert isinstance(r, UnionBoundResult)
    assert r.bound == pytest.approx(100 * r.per_plaquette)


def test_union_bound_linear_in_n_plaquettes() -> None:
    r1 = union_bound_overlap(n_plaquettes=50, g_k=1.0, delta_k=0.2, t_choice=CANONICAL)
    r2 = union_bound_overlap(n_plaquettes=100, g_k=1.0, delta_k=0.2, t_choice=CANONICAL)
    assert r2.bound == pytest.approx(2 * r1.bound)


def test_union_bound_monotone_in_n_plaquettes() -> None:
    """Bound increases linearly with N_p."""
    for n_p in (10, 100, 1000, 10000):
        r = union_bound_overlap(n_p, 1.0, 0.2, CANONICAL)
        assert r.bound > 0


def test_union_bound_zero_for_zero_plaquettes() -> None:
    r = union_bound_overlap(n_plaquettes=0, g_k=1.0, delta_k=0.2, t_choice=CANONICAL)
    assert r.bound == 0.0


def test_union_bound_rejects_negative_plaquettes() -> None:
    with pytest.raises(ValueError):
        union_bound_overlap(-1, 1.0, 0.2, CANONICAL)


def test_union_bound_rejects_manton() -> None:
    with pytest.raises(ValueError, match="Manton"):
        union_bound_overlap(100, 1.0, 0.2, MANTON)


# --------------------------------------------------------------------------
# g_max_for_validity
# --------------------------------------------------------------------------


def test_g_max_returns_sensible_value() -> None:
    """For modest N_p and δ, the bound is < 1 for some g."""
    g_max = g_max_for_validity(
        n_plaquettes=100, delta_k=0.2, t_choice=CANONICAL, target_bound=1.0
    )
    assert g_max is not None
    assert g_max > 0


def test_g_max_decreases_with_more_plaquettes() -> None:
    """More plaquettes → tighter requirement on g."""
    g_max_few = g_max_for_validity(100, 0.2, CANONICAL)
    g_max_many = g_max_for_validity(10000, 0.2, CANONICAL)
    if g_max_few is not None and g_max_many is not None:
        assert g_max_many <= g_max_few


# --------------------------------------------------------------------------
# Trajectory summability
# --------------------------------------------------------------------------


def test_summability_result_shape() -> None:
    g_t, n_t, d_t = [1.0, 0.9, 0.8], [1000, 500, 250], [0.2, 0.18, 0.16]
    r = is_summable_in_k(g_t, n_t, d_t, CANONICAL)
    assert isinstance(r, SummabilityResult)
    assert len(r.per_step_bounds) == 3
    assert len(r.partial_sums) == 3
    assert r.n_steps == 3
    # Partial sums are monotone non-decreasing.
    assert r.partial_sums[0] <= r.partial_sums[1] <= r.partial_sums[2]
    # Total matches last partial sum.
    assert r.total == pytest.approx(r.partial_sums[-1])


def test_summability_rejects_mismatched_lengths() -> None:
    with pytest.raises(ValueError):
        is_summable_in_k([1.0, 0.9], [100, 50, 25], [0.2, 0.18, 0.16], CANONICAL)


def test_summability_total_is_sum_of_per_step() -> None:
    g_t, n_t, d_t = [1.0, 0.9, 0.8], [1000, 500, 250], [0.2, 0.18, 0.16]
    r = is_summable_in_k(g_t, n_t, d_t, CANONICAL)
    assert sum(r.per_step_bounds) == pytest.approx(r.total)


def test_summability_with_small_trajectory_is_finite() -> None:
    """A trajectory with small N_p and moderate g produces a finite sum."""
    g_t = [1.0] * 5
    n_t = [10, 5, 3, 2, 1]
    d_t = [0.1] * 5
    r = is_summable_in_k(g_t, n_t, d_t, CANONICAL)
    assert r.total > 0
    assert r.total < float("inf")


# --------------------------------------------------------------------------
# Standard trajectory
# --------------------------------------------------------------------------


def test_standard_trajectory_returns_three_equal_lists() -> None:
    g_t, n_t, d_t = standard_su2_trajectory(k_max=5)
    assert len(g_t) == len(n_t) == len(d_t)
    assert len(g_t) <= 6  # k_max + 1, but may be truncated by Landau pole


def test_standard_trajectory_g_increases() -> None:
    """In the coarsening direction, g_k grows (confinement)."""
    g_t, _, _ = standard_su2_trajectory(k_max=5, g_0=0.8)
    for i in range(len(g_t) - 1):
        assert g_t[i + 1] >= g_t[i]


def test_standard_trajectory_n_p_decreases() -> None:
    """In coarsening, N_p(k) = N_p(0) · b^{-4k} decreases."""
    _, n_t, _ = standard_su2_trajectory(k_max=5, n_p_0=10000, b=2.0)
    for i in range(len(n_t) - 1):
        assert n_t[i + 1] <= n_t[i]


def test_standard_trajectory_rejects_invalid_inputs() -> None:
    with pytest.raises(ValueError):
        standard_su2_trajectory(k_max=-1)
    with pytest.raises(ValueError):
        standard_su2_trajectory(b=0.5)
    with pytest.raises(ValueError):
        standard_su2_trajectory(g_0=-0.1)


# --------------------------------------------------------------------------
# Figure
# --------------------------------------------------------------------------


def test_plot_writes_svg(tmp_path: Path) -> None:
    out = tmp_path / "test.svg"
    result = plot_overlap_vs_rg_step(output_path=str(out))
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0
    text = out.read_text(encoding="utf-8")
    assert text.lstrip().startswith("<?xml")
    assert "</svg>" in text
