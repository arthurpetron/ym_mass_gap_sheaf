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
    """At g=1 canonical, both 3.1 small-field and 3.2 large-field are outside
    their cluster-expansion convergence thresholds (sf: g < 0.49, lf: g < 0.42).

    Sanity checks:
      * Small-field rate ρ_sf = c_λ/g² = 0.75 (Casimir-gap derivation,
        2026-05-26: c_λ = C_2(1/2) = 3/4).
      * Large-field leading-asymptotic rate ρ_lf_asymptotic = 3/4 (outline §18.5).
      * Strict ρ_lf is negative (Z_t > 1 at this coupling: bound vacuous).
      * Both K_sf and K_lf are ∞ → K_∩ = ∞.
    """
    import math

    ok = compute_overlap_kp(g_k=1.0, t_choice=CANONICAL)
    assert ok.sf_part.rho_sf == pytest.approx(0.75)
    assert ok.lf_part.rho_lf_asymptotic == pytest.approx(0.75)
    assert ok.lf_part.rho_lf < 0  # strict rate is negative at this coupling
    assert not ok.lf_part.convergent
    assert not ok.sf_part.convergent
    # K is infinite in the joint non-convergent regime.
    assert math.isinf(ok.K_cap)


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


# --------------------------------------------------------------------------
# Conjecture 7.4 union-bound looseness (empirical evidence for [P2.1] part (b))
# --------------------------------------------------------------------------


class TestUnionBoundLooseness:
    def test_estimate_at_canonical_wire_in(self):
        """At canonical g = 0.30 (the SigmaHatPilot wire-in operating
        point), the union-bound looseness is well below the conjecture's
        allowed factor of 2."""
        from computations.overlap_kp import union_bound_looseness_estimate
        r = union_bound_looseness_estimate(0.30)
        # Re-pinned 2026-07-25 (μ_plaq → 20e-majorant): K_lf(0.30) grew
        # 0.0156 → 0.0552, so the looseness at the wire-in is ≈ 1.0549
        # (was ≈ 1.016).  Still far below the conjecture's factor 2.
        assert r.looseness_upper_bound < 1.06
        assert r.dominant_regime == "sf"
        assert r.K_sf > r.K_lf

    def test_estimate_at_deep_weak_coupling(self):
        """At very weak coupling, K_lf ≈ 0 and looseness ≈ 1."""
        from computations.overlap_kp import union_bound_looseness_estimate
        r = union_bound_looseness_estimate(0.10)
        assert r.looseness_upper_bound == pytest.approx(1.0, abs=1e-6)

    def test_trajectory_max_below_two(self):
        """The maximum looseness across the entire SU(2) canonical
        convergent regime stays below the conjecture's factor of 2 ---
        EMPIRICAL EVIDENCE for Conjecture 7.4.

        Post-2026-05-26 (c_λ = 3/4 Casimir-gap derivation): the
        canonical convergent regime widens to `g_max_sf ≈ 0.49`, and
        sampling near the new boundary brings the looseness closer to
        the conjecture's 2.0 bound (max ≈ 1.87 vs. previous 1.18 at
        the narrower regime).  The hard bound `< 2.0` (the conjecture's
        actual claim) still holds with margin.
        """
        from computations.overlap_kp import (
            union_bound_looseness_trajectory_max,
        )
        # Scan the canonical JOINT convergent regime in fine steps.
        # Post-c_λ-upgrade: sf-regime widens to ≈ 0.49; post-μ_plaq
        # upgrade (2026-07-25, 20e-majorant) the lf-regime shrinks to
        # g_max_lf ≈ 0.3733 and is the binding constraint.
        g_grid = [i / 100.0 for i in range(5, 37)]
        max_loose, g_at, regime = union_bound_looseness_trajectory_max(g_grid)
        assert max_loose < 2.0, (
            f"max looseness {max_loose:.4f} at g={g_at:.4f} should be "
            f"below 2 (conjecture's allowed bound)"
        )

    def test_trajectory_max_wilson_below_two(self):
        """Same conjecture validation in Wilson convention.

        Post-2026-05-26 (c_λ = 3/4): Wilson regime widens to
        `g_max_sf ≈ 0.99`; sampling near the boundary gives max
        looseness ≈ 1.90 (vs. previous 1.18 at the narrower regime),
        still safely below the conjecture's 2.0 bound.
        """
        import math
        from computations.heat_kernel import HeatKernelConvention
        from computations.overlap_kp import (
            union_bound_looseness_trajectory_max,
        )
        # Wilson joint convergent regime: lf-binding at ≈ 0.7466
        # (2 × canonical) post-μ_plaq upgrade (2026-07-25).
        g_grid = [i / 100.0 for i in range(10, 74)]
        max_loose, _, _ = union_bound_looseness_trajectory_max(
            g_grid, t_choice=HeatKernelConvention.WILSON,
        )
        assert math.isfinite(max_loose)
        assert max_loose < 2.0  # conjecture's allowed bound

    def test_dominant_regime_is_sf_in_convergent_window(self):
        """Throughout the joint convergent regime, K_sf > K_lf — the
        observation underpinning the semi-analytical lemma in
        union_bound_looseness_estimate's docstring."""
        from computations.overlap_kp import union_bound_looseness_estimate
        for g in (0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35):
            r = union_bound_looseness_estimate(g)
            assert r.K_sf >= r.K_lf, (
                f"sf-dominance expected at g={g}: K_sf={r.K_sf}, K_lf={r.K_lf}"
            )
            assert r.dominant_regime in ("sf", "tied")

    def test_looseness_dataclass_fields(self):
        """UnionBoundLoosenessResult carries the documented fields."""
        from computations.overlap_kp import union_bound_looseness_estimate
        r = union_bound_looseness_estimate(0.30)
        for key in ("K_sf", "K_lf", "K_sum", "K_max_lower_bound",
                    "looseness_upper_bound", "dominant_regime",
                    "g_k", "convention", "provenance"):
            assert hasattr(r, key)
        assert "status" in r.provenance


# --------------------------------------------------------------------------
# Diagram smoke test
# --------------------------------------------------------------------------


def test_plot_conjecture_7_4_looseness_writes_svg(tmp_path) -> None:
    """Conjecture 7.4 evidence diagram: writes a non-empty SVG."""
    from pathlib import Path
    from computations.overlap_kp import plot_conjecture_7_4_looseness
    out = tmp_path / "conj74.svg"
    result = plot_conjecture_7_4_looseness(
        g_range_canonical=(0.10, 0.35),
        g_range_wilson=(0.20, 0.70),
        n_points=20,
        output_path=str(out),
    )
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0
    text = out.read_text(encoding="utf-8")
    assert text.lstrip().startswith("<?xml")
    assert "</svg>" in text