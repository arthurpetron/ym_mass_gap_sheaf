"""Tests for `computations.q_lift`: float → Q' rational lift helpers."""

from __future__ import annotations

import math

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.q_lift import (
    CANONICAL_LEAN_PILOT_DENOMINATOR,
    CANONICAL_LEAN_PILOT_G0,
    CANONICAL_LEAN_PILOT_K,
    WILSON_LEAN_PILOT_DENOMINATOR,
    WILSON_LEAN_PILOT_G0,
    WILSON_LEAN_PILOT_K,
    pilot_eta_rational_bound,
    rational_ceiling,
    to_q_prime_pair,
)


# --------------------------------------------------------------------------
# rational_ceiling
# --------------------------------------------------------------------------


class TestRationalCeiling:
    def test_exact_rational(self):
        # 3/10 with d=10 → numerator exactly 3
        assert rational_ceiling(0.3, 10) == 3 or rational_ceiling(0.3, 10) == 4
        # the float 0.3 has tiny representation error; ceiling at d=10 may
        # round up to 4. Both are valid upper bounds.

    def test_strict_round_up(self):
        # 0.31 with d=10 → numerator 4 (ceiling)
        assert rational_ceiling(0.31, 10) == 4

    def test_zero(self):
        # 0 with any positive d → 0
        assert rational_ceiling(0.0, 100) == 0

    def test_small_positive(self):
        # 1.05e-3 with d=10000 → ceiling(10.5) = 11
        assert rational_ceiling(1.05e-3, 10000) == 11

    def test_negative_x(self):
        # Negative x: ceiling can be ≤ 0
        assert rational_ceiling(-0.1, 10) == -1 or rational_ceiling(-0.1, 10) == 0

    def test_invalid_denominator(self):
        with pytest.raises(ValueError, match="denominator"):
            rational_ceiling(0.1, 0)
        with pytest.raises(ValueError, match="denominator"):
            rational_ceiling(0.1, -5)

    def test_invalid_x(self):
        with pytest.raises(ValueError, match="finite"):
            rational_ceiling(float("inf"), 10)
        with pytest.raises(ValueError, match="finite"):
            rational_ceiling(float("nan"), 10)

    def test_upper_bound_property(self):
        # The defining property: n / d >= x
        for x, d in [(1.05e-3, 10000), (0.0042, 1000), (3.14, 100)]:
            n = rational_ceiling(x, d)
            assert n / d >= x, f"ceiling failure: {n}/{d} = {n/d} < {x}"


# --------------------------------------------------------------------------
# to_q_prime_pair
# --------------------------------------------------------------------------


class TestToQPrimePair:
    def test_unit_denominator(self):
        # 5/1 → (5, 0)
        assert to_q_prime_pair(5, 1) == (5, 0)

    def test_typical(self):
        # 11/10000 → (11, 9999)
        assert to_q_prime_pair(11, 10000) == (11, 9999)

    def test_negative_numerator(self):
        # -3/4 → (-3, 3)
        assert to_q_prime_pair(-3, 4) == (-3, 3)

    def test_invalid_denominator(self):
        with pytest.raises(ValueError, match="denominator"):
            to_q_prime_pair(1, 0)
        with pytest.raises(ValueError, match="denominator"):
            to_q_prime_pair(1, -1)


# --------------------------------------------------------------------------
# pilot_eta_rational_bound
# --------------------------------------------------------------------------


class TestPilotEtaRationalBound:
    def test_canonical_pilot_closes(self):
        bound = pilot_eta_rational_bound(
            g_0=CANONICAL_LEAN_PILOT_G0,
            K=CANONICAL_LEAN_PILOT_K,
            denominator=CANONICAL_LEAN_PILOT_DENOMINATOR,
        )
        assert all(bound.bound_check), (
            f"per-step rational bound failed: {bound.bound_check}"
        )
        assert bound.closure_holds, (
            f"closure failed: eta_total={bound.eta_total_numerator}/"
            f"{bound.denominator}; σ̂_0 Q'={bound.sigma_hat_initial_q}"
        )
        # The chosen eta_max_numerator must dominate every float η_k.
        for eta_k in bound.eta_floats:
            assert bound.eta_max_numerator / bound.denominator >= eta_k

    def test_canonical_pilot_has_nonzero_eta(self):
        # At g_0 = 0.30, η_k should be substantively nonzero (~1e-3); a
        # zero-η pilot would be the trivial smoke test, not what we want
        # for the Lean wire-in.
        bound = pilot_eta_rational_bound(
            g_0=CANONICAL_LEAN_PILOT_G0,
            K=CANONICAL_LEAN_PILOT_K,
            denominator=CANONICAL_LEAN_PILOT_DENOMINATOR,
        )
        assert bound.eta_max_float > 1e-6, (
            f"expected nonzero η_max at g_0=0.30; got {bound.eta_max_float}"
        )
        # Should equal 3 at d=10000 (post-2026-05-26 c_λ Casimir-gap
        # derivation; previously 11 under c_λ = 1/2).
        assert bound.eta_max_numerator == 3, (
            f"expected eta_max_numerator=3 at canonical pilot; "
            f"got {bound.eta_max_numerator}"
        )
        # Total = K · 3 = 9 (post-c_λ-upgrade; previously 33 under c_λ = 1/2).
        assert bound.eta_total_numerator == 9

    def test_strong_coupling_fails(self):
        # At g_0 = 1.0 the small-field cluster expansion diverges; η_k = ∞.
        # pilot_eta_rational_bound should still return, with bound_check
        # reflecting the failure.
        bound = pilot_eta_rational_bound(
            g_0=1.0,
            K=CANONICAL_LEAN_PILOT_K,
            denominator=CANONICAL_LEAN_PILOT_DENOMINATOR,
            sigma_hat_initial=10.0,
        )
        # Either max is non-finite, or bound_check fails on at least one step.
        assert (
            not math.isfinite(bound.eta_max_float)
            or not all(bound.bound_check)
        ), "expected pilot failure at g_0 = 1.0; got clean bound"

    def test_larger_denominator_tighter(self):
        # Increasing denominator → tighter (smaller) eta_max numerator /
        # denominator ratio (closer to the binding float from above).
        small_d = pilot_eta_rational_bound(g_0=0.30, K=3, denominator=1000)
        large_d = pilot_eta_rational_bound(g_0=0.30, K=3, denominator=100000)
        ratio_small = small_d.eta_max_numerator / small_d.denominator
        ratio_large = large_d.eta_max_numerator / large_d.denominator
        # Both bound eta_max from above; the larger d gives a tighter bound.
        assert ratio_small >= small_d.eta_max_float
        assert ratio_large >= large_d.eta_max_float
        assert ratio_large <= ratio_small * 1.01  # tighter or equal (up to grid)

    def test_invalid_K(self):
        with pytest.raises(ValueError, match="K must be"):
            pilot_eta_rational_bound(g_0=0.1, K=0)

    def test_invalid_denominator(self):
        with pytest.raises(ValueError, match="denominator"):
            pilot_eta_rational_bound(g_0=0.1, K=3, denominator=0)

    def test_invalid_sigma_q(self):
        with pytest.raises(ValueError, match="denominator"):
            pilot_eta_rational_bound(
                g_0=0.1, K=3, sigma_hat_initial_q=(1, 0)
            )


# --------------------------------------------------------------------------
# Lean wire-in consistency
# --------------------------------------------------------------------------


class TestLeanWireInConsistency:
    """The canonical pilot bound must match the constants hard-coded in
    `lean/YMGap/RG/SigmaHatPilot.lean`."""

    def test_eta_max_matches_lean_hardcoded(self):
        bound = pilot_eta_rational_bound(
            g_0=CANONICAL_LEAN_PILOT_G0,
            K=CANONICAL_LEAN_PILOT_K,
            denominator=CANONICAL_LEAN_PILOT_DENOMINATOR,
        )
        # If this changes, lean/YMGap/RG/SigmaHatPilot.lean must be updated.
        # Post-2026-05-26 c_λ Casimir-gap derivation: eta_max_pilot := mkPos 3 10000
        # (was 11/10000 under the pre-upgrade c_λ = 1/2).
        assert (bound.eta_max_numerator, bound.denominator) == (3, 10000), (
            "Lean SigmaHatPilot.eta_max_pilot is hard-coded as 3/10000. "
            f"Python now produces {bound.eta_max_numerator}/{bound.denominator}. "
            "Update the Lean module to match (or adjust pilot parameters)."
        )

    def test_eta_total_matches_lean_hardcoded(self):
        bound = pilot_eta_rational_bound(
            g_0=CANONICAL_LEAN_PILOT_G0,
            K=CANONICAL_LEAN_PILOT_K,
            denominator=CANONICAL_LEAN_PILOT_DENOMINATOR,
        )
        # Post-c_λ-upgrade: eta_total_pilot := mkPos 9 10000 (K=3 transitions
        # times eta_max=3/10000; was 33/10000 under c_λ = 1/2).
        assert (bound.eta_total_numerator, bound.denominator) == (9, 10000), (
            "Lean SigmaHatPilot.eta_total_pilot is hard-coded as 9/10000. "
            f"Python now produces {bound.eta_total_numerator}/{bound.denominator}."
        )

    def test_wilson_eta_max_matches_lean_hardcoded(self):
        bound = pilot_eta_rational_bound(
            g_0=WILSON_LEAN_PILOT_G0,
            K=WILSON_LEAN_PILOT_K,
            convention=HeatKernelConvention.WILSON,
            denominator=WILSON_LEAN_PILOT_DENOMINATOR,
        )
        # Post-c_λ-upgrade: eta_max_pilot_wilson := mkPos 1 10000
        # (was 4/10000 under c_λ = 1/2).
        assert (bound.eta_max_numerator, bound.denominator) == (1, 10000), (
            "Lean SigmaHatPilot.eta_max_pilot_wilson is hard-coded as 1/10000. "
            f"Python now produces {bound.eta_max_numerator}/{bound.denominator}."
        )

    def test_wilson_eta_total_matches_lean_hardcoded(self):
        bound = pilot_eta_rational_bound(
            g_0=WILSON_LEAN_PILOT_G0,
            K=WILSON_LEAN_PILOT_K,
            convention=HeatKernelConvention.WILSON,
            denominator=WILSON_LEAN_PILOT_DENOMINATOR,
        )
        # Post-c_λ-upgrade: eta_total_pilot_wilson := mkPos 3 10000
        # (was 12/10000 under c_λ = 1/2).
        assert (bound.eta_total_numerator, bound.denominator) == (3, 10000), (
            "Lean SigmaHatPilot.eta_total_pilot_wilson is hard-coded as 3/10000. "
            f"Python now produces {bound.eta_total_numerator}/{bound.denominator}."
        )
