"""Tests for `computations.chaining_eta_uplift` (Milestone 6.5-eta)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.chaining_eta_uplift import (
    ChainingUpliftRow,
    chaining_uplift_row,
    chaining_uplift_table,
    plot_chaining_uplift,
)


# --------------------------------------------------------------------------
# chaining_uplift_row
# --------------------------------------------------------------------------


def test_chaining_uplift_row_canonical() -> None:
    row = chaining_uplift_row(g_0=0.30, K=10, m_0_denominator=1000)
    assert row.baseline_closure_ok
    assert row.chaining_closure_ok
    # K=10 at g_0=0.30 is the manuscript-quotable uplift point.
    assert row.numerator_delta >= 1
    assert row.m_0_uplift_ratio >= 1.0005


def test_chaining_uplift_row_chaining_ge_baseline() -> None:
    """Chaining m_0 ≥ baseline m_0 at every closed operating point."""
    for (g_0, K) in [(0.30, 3), (0.30, 5), (0.35, 3), (0.40, 3)]:
        row = chaining_uplift_row(g_0=g_0, K=K)
        if row.baseline_closure_ok and row.chaining_closure_ok:
            assert row.chaining_m_0 >= row.baseline_m_0


def test_chaining_uplift_row_numerator_delta_nonneg() -> None:
    """Chaining numerator never below baseline numerator (lower bound monotone)."""
    row = chaining_uplift_row(g_0=0.35, K=5)
    assert row.numerator_delta >= 0


# --------------------------------------------------------------------------
# chaining_uplift_table
# --------------------------------------------------------------------------


def test_chaining_uplift_table_default() -> None:
    rows = chaining_uplift_table()
    assert len(rows) == 8
    for row in rows:
        assert isinstance(row, ChainingUpliftRow)


def test_chaining_uplift_table_threshold_amplifies() -> None:
    """Near the convergent threshold (g_0=0.40), uplift ratios are
    substantially > 1.0 — the chaining payoff is largest where η
    matters most."""
    rows = chaining_uplift_table()
    near_threshold = [r for r in rows if r.g_0 >= 0.40 and r.baseline_closure_ok
                      and r.chaining_closure_ok]
    assert near_threshold  # at least one operating point
    for r in near_threshold:
        # At least 1% uplift at the threshold.
        assert r.m_0_uplift_ratio >= 1.01


# --------------------------------------------------------------------------
# plot_chaining_uplift
# --------------------------------------------------------------------------


def test_plot_chaining_uplift_writes_svg(tmp_path: Path) -> None:
    rows = chaining_uplift_table()
    out = tmp_path / "uplift-test.svg"
    written = plot_chaining_uplift(rows, output_path=str(out))
    assert Path(written).exists()
    assert Path(written).stat().st_size > 5000
