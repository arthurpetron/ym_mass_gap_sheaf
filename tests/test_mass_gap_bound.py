"""Tests for `computations.mass_gap_bound` (Milestone 9.1).

Verifies that the explicit constructive mass-gap lower bound m_0:

  * Matches the values cited in `formal/mass-gap-theorem.tex`
    Propositions 3.1 and 3.2 (lockstep).
  * Passes the decidable witness check `m_0² ≤ σ̂_∞`.
  * Matches the Phase-3 SigmaHatPilot Lean module's pilot rational
    constants for the input data (lockstep regression).
  * Behaves correctly under sensitivity sweeps and input validation.
"""

from __future__ import annotations

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.mass_gap_bound import (
    MassGapBound,
    _cross_product_le,
    canonical_mass_gap_bound,
    derive_mass_gap_bound,
    format_mass_gap_bound,
    wilson_mass_gap_bound,
)


# --------------------------------------------------------------------------
# The cited paper values
# --------------------------------------------------------------------------


def test_canonical_bound_matches_paper_proposition_3_1():
    """`formal/mass-gap-theorem.tex` Prop 3.1: m_0_canonical = 999/1000
    **(tightened 2026-05-26 from 998/1000 via c_λ = 3/4 Casimir-gap
    derivation)**."""
    bound = canonical_mass_gap_bound()
    assert bound.m_0_numerator == 999
    assert bound.m_0_denominator == 1000
    assert bound.convention is HeatKernelConvention.CANONICAL
    assert bound.g_0 == 0.30
    assert bound.K == 3
    # σ̂_∞ ≥ 9991/10000 (tightened from 9967/10000 by c_λ-upgrade).
    assert bound.sigma_hat_inf_lower_num == 9991
    assert bound.sigma_hat_inf_lower_den == 10000
    # m_0² = 998001/1000000.
    assert bound.m_0_squared_num == 999 * 999
    assert bound.m_0_squared_den == 1000 * 1000
    # The witness condition.
    assert bound.bound_check_passes is True


def test_wilson_bound_matches_paper_proposition_3_2():
    """`formal/mass-gap-theorem.tex` Prop 3.2: m_0_wilson = 999/1000."""
    bound = wilson_mass_gap_bound()
    assert bound.m_0_numerator == 999
    assert bound.m_0_denominator == 1000
    assert bound.convention is HeatKernelConvention.WILSON
    assert bound.g_0 == 0.50
    assert bound.K == 3
    # σ̂_∞ ≥ 9997/10000 (tightened from 9988/10000 by c_λ-upgrade).
    assert bound.sigma_hat_inf_lower_num == 9997
    assert bound.sigma_hat_inf_lower_den == 10000
    # m_0² = 998001/1000000.
    assert bound.m_0_squared_num == 999 * 999
    assert bound.m_0_squared_den == 1000 * 1000
    assert bound.bound_check_passes is True


# --------------------------------------------------------------------------
# Pilot data lockstep with the Lean SigmaHatPilot module
# --------------------------------------------------------------------------


def test_canonical_pilot_data_matches_lean_module():
    """The Phase-3 pilot's eta_total_pilot in Lean is 9/10000 for canonical
    g_0 = 0.30, K = 3 (tightened from 33/10000 by c_λ-upgrade).  This
    module's bound derivation must consume that same value."""
    bound = canonical_mass_gap_bound()
    assert bound.eta_total_numerator == 9
    assert bound.eta_total_denominator == 10000


def test_wilson_pilot_data_matches_lean_module():
    """eta_total_pilot_wilson in Lean is 3/10000 for Wilson g_0 = 0.50, K = 3
    (tightened from 12/10000 by c_λ-upgrade)."""
    bound = wilson_mass_gap_bound()
    assert bound.eta_total_numerator == 3
    assert bound.eta_total_denominator == 10000


# --------------------------------------------------------------------------
# Mathematical correctness: m_0² ≤ ε
# --------------------------------------------------------------------------


def test_canonical_witness_inequality_holds():
    """The decidable cross-product 999² · 10000 ≤ 9991 · 1000²
    (post-c_λ-upgrade)."""
    # 999 * 999 = 998001; 998001 * 10000 = 9980010000.
    # 9991 * 1000000 = 9991000000.
    # 9980010000 ≤ 9991000000  ✓
    assert _cross_product_le(999 * 999, 1000 * 1000, 9991, 10000)


def test_wilson_witness_inequality_holds():
    """The decidable cross-product 999² · 10000 ≤ 9997 · 1000²
    (post-c_λ-upgrade)."""
    # 999² · 10000 = 9980010000.
    # 9997 · 10⁶ = 9997000000.
    # 9980010000 ≤ 9997000000  ✓
    assert _cross_product_le(999 * 999, 1000 * 1000, 9997, 10000)


def test_m_0_is_largest_below_sqrt_epsilon_at_chosen_denominator():
    """At m_0_denominator = 1000, m_0 = 999 is the LARGEST numerator with
    m_0² ≤ ε at canonical (post-c_λ-upgrade).  m_0 + 1 = 1000 trivially
    fails since √ε < 1."""
    eps_num, eps_den = 9991, 10000
    # 999² · 10000 = 9980010000 ≤ 9991 · 10⁶ = 9991000000  ✓
    assert _cross_product_le(999 * 999, 1000 * 1000, eps_num, eps_den)
    # 1000² · 10000 = 1e10 = 10000000000 > 9991 · 10⁶ = 9991000000.
    assert not _cross_product_le(1000 * 1000, 1000 * 1000, eps_num, eps_den)


# --------------------------------------------------------------------------
# Sensitivity sweep
# --------------------------------------------------------------------------


def test_m_0_increases_with_finer_denominator():
    """Larger m_0_denominator → better approximation of √ε, so m_0_float
    monotone-increases."""
    floats = []
    for d in [100, 1000, 10_000, 100_000]:
        bound = derive_mass_gap_bound(
            g_0=0.30, K=3,
            convention=HeatKernelConvention.CANONICAL,
            denominator=10000,
            m_0_denominator=d,
        )
        floats.append(bound.m_0_float)
    for i in range(len(floats) - 1):
        assert floats[i + 1] >= floats[i], (
            f"m_0 should not decrease as denominator grows; "
            f"got {floats[i]} → {floats[i + 1]}"
        )


def test_m_0_float_approaches_sqrt_epsilon():
    """As m_0_denominator → ∞, m_0_float → √(9991/10000) ≈ 0.999549
    (post-c_λ-upgrade; previously √(9967/10000) ≈ 0.998348)."""
    import math
    target = math.sqrt(9991.0 / 10000.0)
    bound = derive_mass_gap_bound(
        g_0=0.30, K=3,
        convention=HeatKernelConvention.CANONICAL,
        denominator=10000,
        m_0_denominator=1_000_000,
    )
    # At 1e6 resolution, m_0_float should agree with √ε to ~1e-6.
    assert abs(bound.m_0_float - target) < 1e-5


# --------------------------------------------------------------------------
# Wilson vs canonical comparison
# --------------------------------------------------------------------------


def test_wilson_m_0_at_least_canonical_m_0():
    """Wilson consumes less η than canonical (3 vs 9, post-c_λ-upgrade),
    so its ε is larger.  Post-c_λ-upgrade, m_0 at denominator 1000 saturates
    at 999/1000 in both conventions, so the comparison on m_0 is `≥`
    (with equality at the saturation); the strict separation lives in the
    ε floors. -/"""
    can = canonical_mass_gap_bound()
    wil = wilson_mass_gap_bound()
    assert wil.m_0_float >= can.m_0_float
    assert wil.sigma_hat_inf_lower_num > can.sigma_hat_inf_lower_num


# --------------------------------------------------------------------------
# Input validation
# --------------------------------------------------------------------------


def test_rejects_invalid_g_0():
    with pytest.raises(ValueError, match="g_0 must be positive"):
        derive_mass_gap_bound(g_0=-0.1, K=3,
                              convention=HeatKernelConvention.CANONICAL)


def test_rejects_invalid_K():
    with pytest.raises(ValueError, match="K must be ≥ 1"):
        derive_mass_gap_bound(g_0=0.30, K=0,
                              convention=HeatKernelConvention.CANONICAL)


def test_rejects_invalid_denominator():
    with pytest.raises(ValueError, match="denominator must be ≥ 1"):
        derive_mass_gap_bound(
            g_0=0.30, K=3,
            convention=HeatKernelConvention.CANONICAL,
            denominator=0,
        )


def test_rejects_invalid_m_0_denominator():
    with pytest.raises(ValueError, match="m_0_denominator must be ≥ 1"):
        derive_mass_gap_bound(
            g_0=0.30, K=3,
            convention=HeatKernelConvention.CANONICAL,
            m_0_denominator=0,
        )


def test_rejects_invalid_sigma_hat_initial():
    with pytest.raises(ValueError, match="sigma_hat_initial must be positive"):
        derive_mass_gap_bound(
            g_0=0.30, K=3,
            convention=HeatKernelConvention.CANONICAL,
            sigma_hat_initial=-1.0,
        )


# --------------------------------------------------------------------------
# Cross-product helper
# --------------------------------------------------------------------------


def test_cross_product_le_basic():
    # 1/2 ≤ 3/4: 1*4 = 4 ≤ 3*2 = 6  ✓
    assert _cross_product_le(1, 2, 3, 4)
    # 1/2 ≤ 1/2: 1*2 = 2 ≤ 1*2 = 2  ✓ (≤, not <)
    assert _cross_product_le(1, 2, 1, 2)
    # 3/4 ≤ 1/2: 3*2 = 6 ≤ 1*4 = 4  ✗
    assert not _cross_product_le(3, 4, 1, 2)


def test_cross_product_le_rejects_nonpositive_denominator():
    with pytest.raises(ValueError, match="denominators must be positive"):
        _cross_product_le(1, 0, 1, 2)
    with pytest.raises(ValueError, match="denominators must be positive"):
        _cross_product_le(1, 2, 1, -1)


# --------------------------------------------------------------------------
# Dataclass & formatting
# --------------------------------------------------------------------------


def test_returns_mass_gap_bound_dataclass():
    bound = canonical_mass_gap_bound()
    assert isinstance(bound, MassGapBound)


def test_format_mass_gap_bound_is_multiline_string():
    summary = format_mass_gap_bound(canonical_mass_gap_bound())
    assert "convention" in summary
    assert "m_0" in summary
    # Post-c_λ-upgrade, canonical m_0 is 999/1000 (was 998/1000).
    assert "999/1000" in summary
    # Multi-line (multiple newlines).
    assert summary.count("\n") >= 5
