"""Tests for `computations.m_0_bootstrap` (Appendix D bootstrap)."""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.m_0_bootstrap import (
    ENVELOPES,
    BootstrapResult,
    FiducialEnvelope,
    plot_bootstrap,
    run_bootstrap,
)


# --------------------------------------------------------------------------
# ENVELOPES
# --------------------------------------------------------------------------


def test_envelopes_has_four_fiducials() -> None:
    assert len(ENVELOPES) == 4
    short_names = {env.short_name for env in ENVELOPES}
    assert short_names == {"c_lambda", "mu_plaq", "c_polymer", "A_min"}


def test_envelope_baseline_within_range() -> None:
    """Each envelope's baseline must lie in [low, high]."""
    for env in ENVELOPES:
        assert env.low <= env.baseline <= env.high, (
            f"{env.short_name}: baseline {env.baseline} not in [{env.low}, {env.high}]"
        )


def test_envelope_low_strictly_less_than_high() -> None:
    for env in ENVELOPES:
        assert env.low < env.high


def test_envelope_defensibility_bounds() -> None:
    """Specific defensibility bounds from notes/fiducials_notes.md."""
    by_name = {env.short_name: env for env in ENVELOPES}
    # c_lambda: low ~= pilot-tolerance threshold 0.29; high <= 2 * Casimir gap
    assert by_name["c_lambda"].low <= 0.30 + 1e-9
    assert by_name["c_lambda"].high >= 1.5 - 1e-9
    # mu_plaq: high ~= 20e ≈ 54.4 (BF-conservative)
    assert by_name["mu_plaq"].high >= 54.0
    # c_polymer: [1, 2] = [sign-preservation tightening, derived worst-case]
    assert by_name["c_polymer"].low == pytest.approx(1.0)
    assert by_name["c_polymer"].high == pytest.approx(2.0)
    # A_min: spec minimum at low
    assert by_name["A_min"].low == pytest.approx(4.0)


def test_envelope_validation_rejects_inverted() -> None:
    with pytest.raises(ValueError, match="low < high"):
        FiducialEnvelope(
            display_name="bad",
            short_name="bad",
            baseline=1.0,
            low=2.0,
            high=1.0,
            perturbation_callback=lambda v, kw: kw,
            rationale="test",
        )


def test_envelope_validation_rejects_baseline_outside() -> None:
    with pytest.raises(ValueError, match="baseline"):
        FiducialEnvelope(
            display_name="bad",
            short_name="bad",
            baseline=5.0,
            low=1.0,
            high=2.0,
            perturbation_callback=lambda v, kw: kw,
            rationale="test",
        )


# --------------------------------------------------------------------------
# run_bootstrap
# --------------------------------------------------------------------------


def test_run_bootstrap_returns_result() -> None:
    result = run_bootstrap(n_samples=50, seed=0)
    assert isinstance(result, BootstrapResult)
    assert result.n_samples == 50
    assert len(result.m_0_samples) == 50


def test_run_bootstrap_determinism_under_seed() -> None:
    """Two runs at the same seed yield identical m_0 samples."""
    r1 = run_bootstrap(n_samples=100, seed=42)
    r2 = run_bootstrap(n_samples=100, seed=42)
    assert r1.m_0_samples == r2.m_0_samples
    assert r1.percentiles == r2.percentiles


def test_run_bootstrap_different_seeds_differ() -> None:
    r1 = run_bootstrap(n_samples=200, seed=0)
    r2 = run_bootstrap(n_samples=200, seed=1)
    assert r1.m_0_samples != r2.m_0_samples


def test_run_bootstrap_samples_within_envelopes() -> None:
    """All fiducial draws must lie inside their envelopes."""
    result = run_bootstrap(n_samples=200, seed=0)
    envelopes_by_name = {env.short_name: env for env in result.envelopes}
    for short, draws in result.fiducial_samples.items():
        env = envelopes_by_name[short]
        for v in draws:
            assert env.low <= v <= env.high, (
                f"{short} draw {v} outside [{env.low}, {env.high}]"
            )


def test_run_bootstrap_g0_envelope_samples_and_determinism() -> None:
    """UV-flow extension: g_0 is sampled within its envelope, recorded,
    and deterministic under seed."""
    lo, hi = 0.25, 0.35
    r1 = run_bootstrap(n_samples=300, seed=7, g_0_envelope=(lo, hi))
    r2 = run_bootstrap(n_samples=300, seed=7, g_0_envelope=(lo, hi))
    assert "g_0" in r1.fiducial_samples
    g0_draws = r1.fiducial_samples["g_0"]
    assert len(g0_draws) == 300
    for v in g0_draws:
        assert lo <= v <= hi, f"g_0 draw {v} outside [{lo}, {hi}]"
    # Determinism: same seed -> identical samples (incl. the g_0 draws).
    assert r1.m_0_samples == r2.m_0_samples
    assert r1.fiducial_samples["g_0"] == r2.fiducial_samples["g_0"]


def test_run_bootstrap_g0_envelope_default_omits_g0() -> None:
    """Without g_0_envelope, g_0 is fixed and not added to the draws."""
    result = run_bootstrap(n_samples=50, seed=0)
    assert "g_0" not in result.fiducial_samples


def test_run_bootstrap_g0_envelope_rejects_inverted() -> None:
    import pytest

    with pytest.raises(ValueError):
        run_bootstrap(n_samples=10, seed=0, g_0_envelope=(0.40, 0.20))


def test_run_bootstrap_percentiles_monotone() -> None:
    """The percentile statistics are weakly monotone in percentile."""
    result = run_bootstrap(n_samples=500, seed=0)
    p1 = result.percentiles[1.0]
    p5 = result.percentiles[5.0]
    p50 = result.percentiles[50.0]
    p95 = result.percentiles[95.0]
    p99 = result.percentiles[99.0]
    assert p1 <= p5 <= p50 <= p95 <= p99


def test_run_bootstrap_rejects_invalid_n_samples() -> None:
    with pytest.raises(ValueError, match="n_samples"):
        run_bootstrap(n_samples=0)


def test_run_bootstrap_rejects_invalid_percentile() -> None:
    with pytest.raises(ValueError, match="robust_percentile"):
        run_bootstrap(n_samples=10, robust_percentile=0.0)
    with pytest.raises(ValueError, match="robust_percentile"):
        run_bootstrap(n_samples=10, robust_percentile=100.0)


# --------------------------------------------------------------------------
# Headline robustness claim
# --------------------------------------------------------------------------


def test_robust_lower_bound_at_least_950_per_1000() -> None:
    """The manuscript's headline claim: robust m_0 ≥ 950/1000 across the
    defensible envelopes at the canonical pilot."""
    result = run_bootstrap(n_samples=2000, seed=0)
    num = result.numerator_at_denom(1000)
    assert num >= 950, (
        f"5th-percentile m_0 = {result.percentiles[5.0]:.4f} implies "
        f"m_0 >= {num}/1000, below the 950/1000 headline threshold"
    )


def test_no_pilot_failures_in_envelope() -> None:
    """All draws within the defensible envelopes should yield finite m_0
    (n_failed = 0) — the envelopes were constructed to stay inside the
    convergent regime."""
    result = run_bootstrap(n_samples=1000, seed=0)
    assert result.n_failed == 0


def test_mean_close_to_baseline() -> None:
    """The bootstrap mean should be close to the tornado baseline m_0
    (~0.9996) since the envelopes are approximately centered."""
    result = run_bootstrap(n_samples=1000, seed=0)
    # Reasonable tolerance: envelopes are asymmetric (c_lambda envelope
    # extends further below baseline than above), so mean drifts slightly
    # downward from the baseline 0.9996.
    assert 0.97 < result.mean < 1.0


# --------------------------------------------------------------------------
# numerator_at_denom + quote_rational_lower_bound
# --------------------------------------------------------------------------


def test_numerator_at_denom_floors_correctly() -> None:
    result = run_bootstrap(n_samples=50, seed=0)
    p5 = result.percentiles[5.0]
    num = result.numerator_at_denom(1000)
    # floor(p5 * 1000) is conservative — never overshoots
    assert num / 1000 <= p5
    assert (num + 1) / 1000 > p5


def test_quote_rational_lower_bound_is_lower_bound() -> None:
    result = run_bootstrap(n_samples=100, seed=0)
    q = result.quote_rational_lower_bound(denom=1000)
    assert float(q) <= result.percentiles[5.0]


# --------------------------------------------------------------------------
# plot_bootstrap
# --------------------------------------------------------------------------


def test_plot_bootstrap_writes_svg(tmp_path: Path) -> None:
    out = tmp_path / "bootstrap-test.svg"
    result = run_bootstrap(n_samples=200, seed=0)
    written = plot_bootstrap(result=result, output_path=str(out))
    assert Path(written).exists()
    assert Path(written).stat().st_size > 5000


def test_plot_bootstrap_default_invocation(tmp_path: Path) -> None:
    """plot_bootstrap() with no args runs a default-sized bootstrap +
    writes to the default path."""
    out = tmp_path / "default-bootstrap.svg"
    plot_bootstrap(output_path=str(out), n_samples=100, seed=0)
    assert out.exists()
