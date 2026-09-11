"""Tests for `computations.m_0_tornado` (Appendix D tornado plot)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import MU_PLAQUETTE_4D
from computations.m_0_tornado import (
    FIDUCIAL_REGISTRY,
    TornadoBar,
    compute_tornado_bars,
    plot_tornado,
)


# --------------------------------------------------------------------------
# FIDUCIAL_REGISTRY
# --------------------------------------------------------------------------


def test_registry_has_four_fiducials() -> None:
    """The tornado plot covers the four named project fiducials."""
    assert len(FIDUCIAL_REGISTRY) == 4
    names = {entry.display_name for entry in FIDUCIAL_REGISTRY}
    # Each name should reference its physical quantity in LaTeX.
    assert any("lambda" in n for n in names)
    assert any("plaq" in n for n in names)
    assert any("polymer" in n for n in names)
    assert any("min" in n for n in names)  # A_min


def test_registry_baselines_post_c_lambda_upgrade() -> None:
    """Post-2026-05-26: c_λ baseline is 3/4 (Casimir-gap).  Post-2026-07-25
    (SL.1): μ_plaq baseline is the derived 20e-majorant 1359141/25000 =
    54.36564 (was the unsupported Seiler 16)."""
    entries = {e.display_name: e.baseline for e in FIDUCIAL_REGISTRY}
    # Find by partial match.
    c_lambda_entry = next(e for n, e in entries.items() if "lambda" in n)
    mu_plaq_entry = next(e for n, e in entries.items() if "plaq" in n)
    c_polymer_entry = next(e for n, e in entries.items() if "polymer" in n)
    A_min_entry = next(e for n, e in entries.items() if "min" in n)

    assert c_lambda_entry == pytest.approx(0.75)  # 3/4 post-Casimir-gap
    assert mu_plaq_entry == pytest.approx(MU_PLAQUETTE_4D)
    assert mu_plaq_entry == pytest.approx(54.36564)
    assert c_polymer_entry == pytest.approx(2.0)
    assert A_min_entry == pytest.approx(4.0)


# --------------------------------------------------------------------------
# compute_tornado_bars
# --------------------------------------------------------------------------


def test_compute_tornado_bars_returns_four_bars() -> None:
    bars = compute_tornado_bars()
    assert len(bars) == 4
    for bar in bars:
        assert isinstance(bar, TornadoBar)


def test_compute_tornado_bars_sorted_by_sensitivity_descending() -> None:
    bars = compute_tornado_bars()
    for i in range(len(bars) - 1):
        assert bars[i].sensitivity >= bars[i + 1].sensitivity


def test_compute_tornado_bars_baseline_consistent() -> None:
    """All bars share the same baseline m_0."""
    bars = compute_tornado_bars()
    baseline = bars[0].baseline_m_0
    for bar in bars:
        assert bar.baseline_m_0 == pytest.approx(baseline)


def test_compute_tornado_bars_perturbation_at_20_percent() -> None:
    """At ±20%, each bar's low/high should equal baseline ± 20%."""
    bars = compute_tornado_bars(perturbation_fraction=0.20)
    for bar in bars:
        assert bar.low_value == pytest.approx(bar.baseline_value * 0.80)
        assert bar.high_value == pytest.approx(bar.baseline_value * 1.20)


def test_compute_tornado_bars_rejects_invalid_fraction() -> None:
    with pytest.raises(ValueError, match="perturbation_fraction"):
        compute_tornado_bars(perturbation_fraction=0.0)
    with pytest.raises(ValueError, match="perturbation_fraction"):
        compute_tornado_bars(perturbation_fraction=1.0)
    with pytest.raises(ValueError, match="perturbation_fraction"):
        compute_tornado_bars(perturbation_fraction=-0.1)


def test_m_0_robustness_envelope() -> None:
    """The headline robustness claim, re-pinned 2026-07-25 (μ_plaq → the
    derived 20e-majorant): the baseline m_0 moves 0.99960 → 0.99880, so
    the quotable rational floor drops 999/1000 → 998/1000.  m_0 stays in
    (0.998, 1.000) across all ±20% fiducial perturbations at the
    canonical pilot (measured range ≈ [0.99840, 0.99904])."""
    bars = compute_tornado_bars(perturbation_fraction=0.20)
    for bar in bars:
        assert 0.998 < bar.low_m_0 < 1.0, (
            f"low m_0 for {bar.display_name} = {bar.low_m_0} outside (0.998, 1)"
        )
        assert 0.998 < bar.high_m_0 < 1.0, (
            f"high m_0 for {bar.display_name} = {bar.high_m_0} outside (0.998, 1)"
        )


def test_m_0_sensitivity_ordering_post_mu_upgrade() -> None:
    """Re-pinned 2026-07-25: with μ_plaq at the derived 20e-majorant,
    K_lf at the pilot is ≈ 3.5× larger and the lf channel carries real
    weight, so c_λ is no longer the top bar.  Measured ±20% sensitivity
    ordering at the canonical pilot: A_min (6.4e-4) > μ_plaq (4.9e-4) >
    c_polymer (4.8e-4) > c_λ (4.2e-4) — all within a factor ≈ 1.5, i.e.
    no fiducial dominates."""
    bars = compute_tornado_bars()
    names_sorted = [b.display_name for b in bars]
    assert "min" in names_sorted[0]          # A_min now most sensitive
    assert "lambda" in names_sorted[-1]      # c_λ now least sensitive
    # No fiducial dominates: max/min sensitivity ratio stays modest.
    assert bars[0].sensitivity < 2.0 * bars[-1].sensitivity


# --------------------------------------------------------------------------
# TornadoBar.sensitivity
# --------------------------------------------------------------------------


def test_tornado_bar_sensitivity_is_range() -> None:
    bar = TornadoBar(
        display_name="test",
        baseline_value=1.0,
        baseline_m_0=0.500,
        low_value=0.8,
        low_m_0=0.400,
        high_value=1.2,
        high_m_0=0.600,
    )
    assert bar.sensitivity == pytest.approx(0.200)


def test_tornado_bar_sensitivity_handles_reversed() -> None:
    """Some fiducials shift m_0 in the OPPOSITE direction (e.g.,
    larger c_polymer → larger η → smaller m_0).  Sensitivity is the
    absolute range, sign-agnostic."""
    bar = TornadoBar(
        display_name="test",
        baseline_value=1.0,
        baseline_m_0=0.500,
        low_value=0.8,
        low_m_0=0.600,  # smaller fiducial → LARGER m_0
        high_value=1.2,
        high_m_0=0.400,  # larger fiducial → SMALLER m_0
    )
    assert bar.sensitivity == pytest.approx(0.200)


# --------------------------------------------------------------------------
# plot_tornado
# --------------------------------------------------------------------------


def test_plot_tornado_writes_svg(tmp_path: Path) -> None:
    out_path = tmp_path / "tornado-test.svg"
    result_path = plot_tornado(output_path=str(out_path))
    assert Path(result_path).exists()
    assert Path(result_path).stat().st_size > 5000  # non-trivial SVG


def test_plot_tornado_with_explicit_bars(tmp_path: Path) -> None:
    """When `bars` is supplied, plot_tornado uses them without recomputing."""
    bars = compute_tornado_bars()
    out_path = tmp_path / "tornado-supplied.svg"
    plot_tornado(bars=bars, output_path=str(out_path))
    assert Path(out_path).exists()