"""Tests for `computations.su3_character_sum` (Milestone 10.4).

The load-bearing property is rigour: ``upper_bound`` must be a genuine upper
bound on the true (infinite) character sum ``Z_t``, even when the exact box is
small (so the geometric tail estimate carries the weight).  We check this
against a dense brute-force truncation that under-estimates the true ``Z_t``.
"""

from __future__ import annotations

import math

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.su3_character_sum import (
    Su3CharacterTailSum,
    majorant_g,
    majorant_ratio,
    su3_heat_kernel_character_tail_Z,
)
from computations.su3_representations import Su3Irrep

CANON = HeatKernelConvention.CANONICAL
WILSON = HeatKernelConvention.WILSON


def brute_force_Z(t: float, box: int = 80) -> float:
    """Dense truncation Σ_{(p,q)≠(0,0), p,q≤box} dim² e^{-t C_2}.

    A *lower* estimate of the true infinite ``Z_t`` (all dropped terms are
    positive), so a valid upper bound must dominate it.
    """
    total = 0.0
    for p in range(box + 1):
        for q in range(box + 1):
            if p == 0 and q == 0:
                continue
            irr = Su3Irrep(p, q)
            total += (irr.dimension * irr.dimension) * math.exp(-t * float(irr.casimir))
    return total


@pytest.mark.parametrize("g", [0.20, 0.30, 0.40, 0.45, 0.485, 0.50])
def test_upper_bound_dominates_dense_truncation(g: float) -> None:
    """Rigour: the bound (default box) exceeds a dense brute-force truncation."""
    z = su3_heat_kernel_character_tail_Z(g, CANON)
    brute = brute_force_Z(z.t)
    assert z.upper_bound >= brute


@pytest.mark.parametrize("box_m", [1, 2, 3, 5, 8])
def test_small_box_still_upper_bounds(box_m: int) -> None:
    """Rigour stress test: even a tiny exact box must upper-bound the true Z_t.

    With a small box the geometric tail term carries most of the mass, so this
    exercises the 2-D tail formula, not just the exact partial sum.
    """
    g = 0.45  # t ≈ 4.94, comfortably in the geometric-tail regime
    z = su3_heat_kernel_character_tail_Z(g, CANON, j_max_int=box_m)
    brute = brute_force_Z(z.t)
    assert z.tail_finite
    assert z.upper_bound >= brute


def test_bound_tightens_as_box_grows() -> None:
    """Larger box ⇒ tighter (non-increasing) upper bound, converging to Z_t."""
    g = 0.45
    uppers = [
        su3_heat_kernel_character_tail_Z(g, CANON, j_max_int=m).upper_bound
        for m in (1, 2, 4, 8, 16)
    ]
    for a, b in zip(uppers, uppers[1:], strict=False):
        assert a >= b - 1e-15
    # Converges to the true value (dense brute force).
    t = 1.0 / (g * g)
    assert uppers[-1] == pytest.approx(brute_force_Z(t), rel=1e-9)


def test_reproduces_spike_value() -> None:
    """The rigorous bound reproduces the closure-spike Z_t to working precision."""
    for g in (0.30, 0.40, 0.485):
        z = su3_heat_kernel_character_tail_Z(g, CANON)
        assert z.upper_bound == pytest.approx(brute_force_Z(z.t), rel=1e-10)


def test_termwise_majorant_holds() -> None:
    """a(p,q) = dim² e^{-t C_2} ≤ g(p)·g(q) for the factorized majorant."""
    t = 4.5
    for p in range(40):
        for q in range(40):
            irr = Su3Irrep(p, q)
            a = (irr.dimension * irr.dimension) * math.exp(-t * float(irr.casimir))
            assert a <= majorant_g(p, t) * majorant_g(q, t) * (1.0 + 1e-12)


def test_majorant_ratio_decreasing_and_threshold() -> None:
    """ρ(x) is decreasing in x and < 1 in the convergent regime."""
    t = 4.25
    ratios = [majorant_ratio(x, t) for x in range(10)]
    for a, b in zip(ratios, ratios[1:], strict=False):
        assert b < a
    assert ratios[0] < 1.0


def test_monotone_in_coupling() -> None:
    """Z_t increases with g (weaker suppression at larger coupling)."""
    gs = [0.20, 0.25, 0.30, 0.35, 0.40, 0.45]
    zs = [su3_heat_kernel_character_tail_Z(g, CANON).upper_bound for g in gs]
    for a, b in zip(zs, zs[1:], strict=False):
        assert b > a


def test_large_field_threshold_near_0_485() -> None:
    """q = μ_plaq·Z_t crosses 1 (μ=16) near g ≈ 0.485 (matches the spike)."""
    mu = 16.0
    z_below = su3_heat_kernel_character_tail_Z(0.48, CANON).upper_bound
    z_above = su3_heat_kernel_character_tail_Z(0.49, CANON).upper_bound
    assert mu * z_below < 1.0
    assert mu * z_above > 1.0


def test_wilson_convention_time() -> None:
    """Wilson uses t = 2N/g² = 6/g² for SU(3)."""
    g = 0.5
    z = su3_heat_kernel_character_tail_Z(g, WILSON)
    assert z.t == pytest.approx(6.0 / (g * g))


def test_return_type_and_fields() -> None:
    z = su3_heat_kernel_character_tail_Z(0.3, CANON)
    assert isinstance(z, Su3CharacterTailSum)
    # Drop-in field compatibility with large_field_kp.CharacterTailSum.
    assert z.upper_bound == z.partial_sum + z.tail_bound
    assert z.j_max_int >= 1


def test_invalid_inputs() -> None:
    with pytest.raises(ValueError, match="positive"):
        su3_heat_kernel_character_tail_Z(0.0, CANON)
    with pytest.raises(ValueError, match="≥ 1"):
        su3_heat_kernel_character_tail_Z(0.3, CANON, j_max_int=0)
    with pytest.raises(ValueError, match="Manton"):
        su3_heat_kernel_character_tail_Z(0.3, HeatKernelConvention.MANTON)
