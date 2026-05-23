"""Tests for `computations.heat_kernel` (Milestone 1.2).

Coverage:

- The three named conventions (WILSON, MANTON, CANONICAL) are distinct.
- ``t_W · t_M = 1`` (Wilson and Manton are reciprocal identifications).
- Round-trip: ``g → t → g`` is the identity (up to float).
- ``kappa_from_casimir`` returns:
    * Wilson: ``2 N · C_2_min``.
    * Canonical: ``C_2_min``.
    * Manton: raises (different bound shape).
- ``manton_exponent_coefficient`` returns ``C_2_min / (2N)``.
- The exact-rational version produces the same values as ``Fraction``.
- SU(2) spot values match `outline.md` §18.5 verbatim:
    * ``KAPPA_SU2_CANONICAL = 3/4`` (the outline's κ).
    * ``KAPPA_SU2_WILSON = 3``.
    * ``MANTON_COEFF_SU2 = 3/16``.
- Input validation (positive g, t, C_2_min; N ≥ 1).
"""

from __future__ import annotations

from fractions import Fraction

import pytest

from computations.heat_kernel import (
    C_2_SU2_FUNDAMENTAL,
    KAPPA_SU2_CANONICAL,
    KAPPA_SU2_WILSON,
    MANTON_COEFF_SU2,
    N_SU2,
    HeatKernelConvention,
    kappa_from_casimir,
    kappa_from_casimir_exact,
    manton_exponent_coefficient,
    manton_g_from_t,
    manton_t_from_g,
    wilson_g_from_t,
    wilson_t_from_g,
)

# --------------------------------------------------------------------------
# t ↔ g conversions
# --------------------------------------------------------------------------


def test_wilson_t_from_g_su2() -> None:
    """For SU(2), g=1: t_W = 2·2/1 = 4."""
    assert wilson_t_from_g(g=1.0, N=2) == pytest.approx(4.0)


def test_manton_t_from_g_su2() -> None:
    """For SU(2), g=1: t_M = 1/(2·2) = 1/4."""
    assert manton_t_from_g(g=1.0, N=2) == pytest.approx(0.25)


def test_wilson_and_manton_are_reciprocal() -> None:
    """``t_W · t_M = 1`` for any positive g and N ≥ 1."""
    for g in (0.5, 1.0, 1.5, 2.0):
        for N in (2, 3, 5):
            t_W = wilson_t_from_g(g, N)
            t_M = manton_t_from_g(g, N)
            assert t_W * t_M == pytest.approx(1.0)


def test_wilson_round_trip() -> None:
    for g in (0.5, 1.0, 1.5, 2.0, 3.0):
        for N in (2, 3, 5):
            t = wilson_t_from_g(g, N)
            assert wilson_g_from_t(t, N) == pytest.approx(g)


def test_manton_round_trip() -> None:
    for g in (0.5, 1.0, 1.5, 2.0, 3.0):
        for N in (2, 3, 5):
            t = manton_t_from_g(g, N)
            assert manton_g_from_t(t, N) == pytest.approx(g)


# --------------------------------------------------------------------------
# Input validation
# --------------------------------------------------------------------------


def test_wilson_t_from_g_rejects_nonpositive_g() -> None:
    with pytest.raises(ValueError, match="positive"):
        wilson_t_from_g(0.0, 2)
    with pytest.raises(ValueError, match="positive"):
        wilson_t_from_g(-1.0, 2)


def test_wilson_t_from_g_rejects_small_N() -> None:
    with pytest.raises(ValueError, match="≥ 1"):
        wilson_t_from_g(1.0, 0)


def test_manton_t_from_g_rejects_nonpositive() -> None:
    with pytest.raises(ValueError):
        manton_t_from_g(0.0, 2)


def test_kappa_from_casimir_rejects_invalid() -> None:
    with pytest.raises(ValueError, match="positive"):
        kappa_from_casimir(C_2_min=0.0, N=2, t_choice=HeatKernelConvention.CANONICAL)
    with pytest.raises(ValueError, match="≥ 1"):
        kappa_from_casimir(C_2_min=0.75, N=0, t_choice=HeatKernelConvention.CANONICAL)


# --------------------------------------------------------------------------
# kappa_from_casimir — the three conventions
# --------------------------------------------------------------------------


def test_kappa_canonical_returns_C_2_directly() -> None:
    """Canonical: κ = C_2_min."""
    for C_2 in (0.5, 0.75, 1.0, 2.0):
        kappa = kappa_from_casimir(
            C_2_min=C_2, N=2, t_choice=HeatKernelConvention.CANONICAL
        )
        assert kappa == pytest.approx(C_2)


def test_kappa_wilson_returns_2N_times_C_2() -> None:
    """Wilson: κ = 2N · C_2_min."""
    for C_2 in (0.5, 0.75, 1.0, 2.0):
        for N in (2, 3, 5):
            kappa = kappa_from_casimir(
                C_2_min=C_2, N=N, t_choice=HeatKernelConvention.WILSON
            )
            assert kappa == pytest.approx(2 * N * C_2)


def test_kappa_manton_raises() -> None:
    """Manton has bound shape exp(-c·g²); kappa_from_casimir refuses."""
    with pytest.raises(ValueError, match="Manton"):
        kappa_from_casimir(
            C_2_min=0.75, N=2, t_choice=HeatKernelConvention.MANTON
        )


def test_manton_exponent_coefficient_su2() -> None:
    """SU(2), C_2(1/2) = 3/4: Manton coefficient is (3/4)/(2·2) = 3/16."""
    c = manton_exponent_coefficient(C_2_min=0.75, N=2)
    assert c == pytest.approx(3.0 / 16.0)


# --------------------------------------------------------------------------
# Exact rational form (for Lean Q' interop)
# --------------------------------------------------------------------------


def test_kappa_exact_canonical_for_su2() -> None:
    result = kappa_from_casimir_exact(
        C_2_min=Fraction(3, 4), N=2, t_choice=HeatKernelConvention.CANONICAL
    )
    assert result.convention is HeatKernelConvention.CANONICAL
    assert result.kappa == Fraction(3, 4)


def test_kappa_exact_wilson_for_su2() -> None:
    result = kappa_from_casimir_exact(
        C_2_min=Fraction(3, 4), N=2, t_choice=HeatKernelConvention.WILSON
    )
    assert result.kappa == Fraction(3)


def test_kappa_exact_manton_returns_none() -> None:
    result = kappa_from_casimir_exact(
        C_2_min=Fraction(3, 4), N=2, t_choice=HeatKernelConvention.MANTON
    )
    assert result.convention is HeatKernelConvention.MANTON
    assert result.kappa is None


# --------------------------------------------------------------------------
# SU(2) spot values: must match outline.md §18.5 verbatim
# --------------------------------------------------------------------------


def test_C_2_su2_fundamental_is_three_quarters() -> None:
    """Mirror of `su2_representations` C_2(1/2) = 3/4."""
    assert C_2_SU2_FUNDAMENTAL == Fraction(3, 4)


def test_N_su2_is_two() -> None:
    assert N_SU2 == 2


def test_kappa_su2_canonical_matches_outline() -> None:
    """outline.md §18.5: exp(-3/(4 g²)). κ in this form is 3/4."""
    assert KAPPA_SU2_CANONICAL == Fraction(3, 4)


def test_kappa_su2_wilson_is_three() -> None:
    """Wilson SU(2) κ = 2N · C_2 = 4 · 3/4 = 3."""
    assert KAPPA_SU2_WILSON == Fraction(3)


def test_manton_coeff_su2_is_three_sixteenths() -> None:
    """Manton SU(2) bound is exp(-(3/16) · g²)."""
    assert MANTON_COEFF_SU2 == Fraction(3, 16)


def test_kappa_su2_consistency_canonical_vs_wilson() -> None:
    """Canonical and Wilson differ by exactly the 2N factor for SU(2)."""
    assert KAPPA_SU2_WILSON == 2 * N_SU2 * KAPPA_SU2_CANONICAL


def test_manton_su2_consistency() -> None:
    """Manton coefficient = C_2 / (2N) for SU(2)."""
    assert MANTON_COEFF_SU2 == C_2_SU2_FUNDAMENTAL / (2 * N_SU2)
