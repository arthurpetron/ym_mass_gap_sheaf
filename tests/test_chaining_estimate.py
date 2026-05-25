"""Tests for `computations.chaining_estimate` (Milestone 6.5)."""

from __future__ import annotations

import math
from pathlib import Path

import pytest

from computations.chaining_estimate import (
    G_MAX_CHAIN,
    PER_CHANNEL_CORRELATION_STRENGTH,
    SHARED_LINK_CHANNEL_MULTIPLICITY,
    ChainingBoundResult,
    ChainingVsUnionRow,
    ChainingVsUnionTrajectory,
    chain_factor,
    chaining_bound_overlap,
    compare_chaining_vs_union,
    is_summable_in_k_chaining,
    plot_chaining_vs_union,
)
from computations.heat_kernel import HeatKernelConvention
from computations.overlap_measure import (
    is_summable_in_k,
    standard_su2_trajectory,
    union_bound_overlap,
)


# --------------------------------------------------------------------------
# chain_factor properties
# --------------------------------------------------------------------------


def test_chain_factor_unity_at_zero():
    """`c_chain(0) = 1` (no tightening at the free limit)."""
    assert chain_factor(0.0) == pytest.approx(1.0)


def test_chain_factor_in_unit_interval():
    """`c_chain(g) ∈ (0, 1]` for every admissible g."""
    for g in [0.0, 0.1, 0.3, 0.5, 1.0, 1.5, 2.0]:
        cf = chain_factor(g)
        assert 0.0 < cf <= 1.0, f"chain_factor({g}) = {cf} ∉ (0, 1]"


def test_chain_factor_strictly_decreasing_in_g():
    """Stronger coupling → tighter chaining (smaller c_chain)."""
    g_values = [0.0, 0.1, 0.3, 0.5, 0.8, 1.0, 1.5, 2.0]
    cfs = [chain_factor(g) for g in g_values]
    for i in range(len(cfs) - 1):
        if g_values[i] > 0.0:
            assert cfs[i + 1] < cfs[i], (
                f"chain_factor not strictly decreasing at g={g_values[i]}"
            )


def test_chain_factor_matches_closed_form():
    """`c_chain(g) = exp(-n_share · g² · ζ)` literally."""
    g = 0.4
    expected = math.exp(
        -SHARED_LINK_CHANNEL_MULTIPLICITY * g * g * PER_CHANNEL_CORRELATION_STRENGTH
    )
    assert chain_factor(g) == pytest.approx(expected)


def test_chain_factor_sensitivity_to_n_share():
    """Doubling n_share at fixed g, ζ gives c_chain^2 (functional form check)."""
    g, zeta = 0.5, 0.5
    cf_base = chain_factor(g, n_share=2, zeta=zeta)
    cf_doubled = chain_factor(g, n_share=4, zeta=zeta)
    assert cf_doubled == pytest.approx(cf_base * cf_base)


def test_chain_factor_sensitivity_to_zeta():
    """Doubling ζ at fixed g, n_share gives c_chain^2."""
    g, n_share = 0.5, 4
    cf_base = chain_factor(g, n_share=n_share, zeta=0.25)
    cf_doubled = chain_factor(g, n_share=n_share, zeta=0.5)
    assert cf_doubled == pytest.approx(cf_base * cf_base)


# --------------------------------------------------------------------------
# Input validation / guard rails
# --------------------------------------------------------------------------


def test_chain_factor_rejects_negative_g():
    with pytest.raises(ValueError, match="g_k must be"):
        chain_factor(-0.1)


def test_chain_factor_raises_above_g_max():
    """Beyond G_MAX_CHAIN the small-positive-correlation model breaks down;
    the function must raise rather than silently return a misleading value."""
    with pytest.raises(RuntimeError, match="exceeds G_MAX_CHAIN"):
        chain_factor(G_MAX_CHAIN + 0.01)


def test_chain_factor_rejects_negative_fiducials():
    with pytest.raises(ValueError, match="n_share"):
        chain_factor(0.5, n_share=-1)
    with pytest.raises(ValueError, match="zeta"):
        chain_factor(0.5, zeta=-0.1)


# --------------------------------------------------------------------------
# chaining_bound_overlap — drop-in for union_bound_overlap
# --------------------------------------------------------------------------


def test_chaining_bound_lt_or_eq_union_bound():
    """Dominated-bound consistency: chaining ≤ union at every admissible (g, N_p, δ)."""
    for g in [0.1, 0.3, 0.5, 0.8, 1.0, 1.5]:
        result = chaining_bound_overlap(
            n_plaquettes=10_000, g_k=g, delta_k=0.5,
            t_choice=HeatKernelConvention.CANONICAL,
        )
        assert result.chaining_bound <= result.union_bound, (
            f"chaining {result.chaining_bound} > union {result.union_bound} at g={g}"
        )


def test_chaining_recovers_union_in_weak_coupling_limit():
    """As g → 0, chaining_bound → union_bound (chain_factor → 1).

    `single_plaquette_buffer_measure` itself rejects g_k = 0 (the heat
    kernel at infinite time isn't well-defined that way); we approach
    the limit with g_k = 1e-3, which gives chain_factor within 1e-6
    of 1 and the chaining/union ratio likewise."""
    result = chaining_bound_overlap(
        n_plaquettes=100, g_k=1e-3, delta_k=0.5,
        t_choice=HeatKernelConvention.CANONICAL,
    )
    assert result.chain_factor == pytest.approx(1.0, abs=1e-5)
    assert result.tightening_ratio == pytest.approx(1.0, abs=1e-5)
    assert result.chaining_bound == pytest.approx(result.union_bound, rel=1e-5)


def test_chaining_underlying_union_matches_direct_call():
    """The underlying_union should equal calling union_bound_overlap directly."""
    args = dict(n_plaquettes=500, g_k=0.5, delta_k=0.4,
                t_choice=HeatKernelConvention.CANONICAL)
    chain_result = chaining_bound_overlap(**args)
    direct_union = union_bound_overlap(**args)
    assert chain_result.underlying_union.bound == pytest.approx(direct_union.bound)


def test_chaining_returns_dataclass():
    result = chaining_bound_overlap(
        n_plaquettes=100, g_k=0.3, delta_k=0.5,
        t_choice=HeatKernelConvention.CANONICAL,
    )
    assert isinstance(result, ChainingBoundResult)


# --------------------------------------------------------------------------
# Trajectory-level comparison
# --------------------------------------------------------------------------


def test_compare_returns_per_step_rows():
    g_t, n_t, d_t = standard_su2_trajectory(k_max=5, g_0=0.8)
    g_t = [g for g in g_t if g <= G_MAX_CHAIN]
    n_t = n_t[: len(g_t)]
    d_t = d_t[: len(g_t)]
    comp = compare_chaining_vs_union(
        g_t, n_t, d_t, HeatKernelConvention.CANONICAL
    )
    assert isinstance(comp, ChainingVsUnionTrajectory)
    assert len(comp.rows) == len(g_t)
    assert all(isinstance(r, ChainingVsUnionRow) for r in comp.rows)


def test_trajectory_chaining_total_lt_union_total():
    """Σ chaining ≤ Σ union always."""
    g_t, n_t, d_t = standard_su2_trajectory(k_max=5, g_0=0.3)
    comp = compare_chaining_vs_union(
        g_t, n_t, d_t, HeatKernelConvention.CANONICAL
    )
    assert comp.total_chaining <= comp.total_union
    assert 0.0 <= comp.total_tightening_ratio <= 1.0


def test_chaining_wins_regime_exists():
    """For the standard g_0 = 0.8 trajectory there ARE steps where chaining
    is admissible (≤ 1) and union is not (> 1).  This is the milestone-6.5
    structural payoff."""
    g_t, n_t, d_t = standard_su2_trajectory(k_max=10, g_0=0.8)
    g_t_clip = [g for g in g_t if g <= G_MAX_CHAIN]
    n_t_clip = n_t[: len(g_t_clip)]
    d_t_clip = d_t[: len(g_t_clip)]
    comp = compare_chaining_vs_union(
        g_t_clip, n_t_clip, d_t_clip, HeatKernelConvention.CANONICAL
    )
    assert comp.n_chaining_wins > 0, (
        "expected at least one step where chaining beats union; got 0"
    )
    # Spot-check the wins-row invariants.
    for row in comp.rows:
        if row.chaining_wins:
            assert row.chaining_bound <= 1.0
            assert row.union_bound > 1.0


def test_compare_length_mismatch_raises():
    with pytest.raises(ValueError, match="equal length"):
        compare_chaining_vs_union(
            [0.3, 0.4], [100], [0.5, 0.6], HeatKernelConvention.CANONICAL
        )


# --------------------------------------------------------------------------
# is_summable_in_k_chaining — parallel to overlap_measure.is_summable_in_k
# --------------------------------------------------------------------------


def test_summable_chaining_total_lt_summable_union_total():
    """Trajectory total via chaining ≤ trajectory total via union."""
    g_t, n_t, d_t = standard_su2_trajectory(k_max=10, g_0=0.3)
    chaining = is_summable_in_k_chaining(
        g_t, n_t, d_t, HeatKernelConvention.CANONICAL
    )
    union = is_summable_in_k(g_t, n_t, d_t, HeatKernelConvention.CANONICAL)
    assert chaining.total <= union.total


def test_summable_chaining_admissibility():
    """For a moderate-g trajectory where union fails, chaining can succeed."""
    g_t, n_t, d_t = standard_su2_trajectory(k_max=5, g_0=0.85)
    g_t = [g for g in g_t if g <= G_MAX_CHAIN]
    n_t = n_t[: len(g_t)]
    d_t = d_t[: len(g_t)]
    chaining = is_summable_in_k_chaining(
        g_t, n_t, d_t, HeatKernelConvention.CANONICAL
    )
    union = is_summable_in_k(g_t, n_t, d_t, HeatKernelConvention.CANONICAL)
    # Chaining strictly tightens; the chaining total is strictly smaller.
    assert chaining.total < union.total


# --------------------------------------------------------------------------
# Figure smoke
# --------------------------------------------------------------------------


def test_plot_writes_svg(tmp_path: Path):
    g_t, n_t, d_t = standard_su2_trajectory(k_max=6, g_0=0.8)
    out = tmp_path / "chain.svg"
    result_path = plot_chaining_vs_union(
        g_t, n_t, d_t, output_path=str(out)
    )
    assert Path(result_path) == out
    assert out.exists()
    assert out.stat().st_size > 0
    text = out.read_text(encoding="utf-8")
    assert text.lstrip().startswith("<?xml")
    assert "</svg>" in text


def test_plot_default_trajectory(tmp_path: Path):
    """Plot with default trajectory (no explicit g_t/n_t/d_t) should work."""
    out = tmp_path / "default.svg"
    result_path = plot_chaining_vs_union(output_path=str(out))
    assert Path(result_path) == out
    assert out.exists()
