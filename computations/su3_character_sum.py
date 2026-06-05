"""Rigorous upper bound on the SU(3) heat-kernel character sum ``Z_t``.

Milestone 10.4 (`docs/su3-campaign-plan.md`).  Replaces the closure-spike's
high-order truncation (`scripts/su3_closure_spike.py`) with a *rigorous*
upper bound carrying an explicit, provable tail estimate — the SU(3) analogue
of `computations.large_field_kp.heat_kernel_character_tail_Z`, which sums over a
1-D half-integer spin index.  SU(3) irreps live on the 2-D ``(p, q)`` lattice, so
the tail bound is genuinely two-dimensional.

The large-field activity bound needs
::

    Z_t  :=  Σ_{(p,q) ≠ (0,0)} dim(p,q)² · exp(-t · C_2(p,q)),

with ``dim`` and ``C_2`` from `computations.su3_representations`.

## The rigorous bound

Sum the true terms exactly over a box ``[0, M]²`` (``M = j_max_int``) and bound
the tail (everything outside the box) by a **factorizable majorant**.  Writing
``u = p+1, v = q+1`` (so ``u, v ≥ 1``):

  * ``dim(p,q)² = u²v²(u+v)²/4 ≤ u⁴v⁴ = (p+1)⁴(q+1)⁴``,
    because ``u + v ≤ 2uv`` for ``u, v ≥ 1`` (equivalently ``1/u + 1/v ≤ 2``).
  * ``C_2(p,q) = f(p) + f(q) + p q / 3 ≥ f(p) + f(q)``, with
    ``f(x) = (x² + 3x)/3`` (dropping the non-negative cross term ``pq/3``).

Hence, **termwise**,
::

    a(p,q) := dim(p,q)² e^{-t C_2(p,q)}  ≤  g(p) · g(q),
    g(x) := (x+1)⁴ · exp(-t · f(x)).

``g`` factorizes, so the tail over the box complement
``{p ≥ M+1} ∪ {q ≥ M+1}`` is, by the union bound,
::

    Σ_{(p,q) ∉ box} a(p,q)  ≤  2 · (Σ_{p ≥ M+1} g(p)) · (Σ_{x ≥ 0} g(x)).

Each 1-D sum is bounded geometrically: the ratio
``g(x+1)/g(x) = ((x+2)/(x+1))⁴ · exp(-t (2x+4)/3)`` is *decreasing* in ``x`` (both
factors decrease), so once ``ρ(X) := g(X+1)/g(X) < 1`` the tail from ``X`` on is a
true geometric series,
::

    Σ_{x ≥ X} g(x)  ≤  g(X) / (1 - ρ(X)).

When ``ρ(M+1) ≥ 1`` (strong coupling, where ``Z_t`` is far above the
cluster-expansion threshold anyway) the tail is reported as ``+∞`` — rigorous and
vacuous, mirroring the SU(2) module.

The returned object exposes the same field names as
`large_field_kp.CharacterTailSum` (``upper_bound``, ``partial_sum``,
``tail_bound``, ``tail_ratio``, ``tail_finite``, ``j_max_int``, ``t``), so
`su3_heat_kernel_character_tail_Z` is a drop-in replacement for
`heat_kernel_character_tail_Z` in `compute_large_field_kp` (the Milestone 10.6-py
``GaugeGroup`` hook).

All exact inputs (``dim``: ``int``; ``C_2``: ``Fraction``) are ℚ′-encodable; the
``exp`` makes ``Z_t`` a float bound, exactly as on the SU(2) side, with the
rational rounding deferred to the Lean wire-in (Milestone 10.5).
"""

from __future__ import annotations

import math
from dataclasses import dataclass

from computations.heat_kernel import HeatKernelConvention
from computations.su3_representations import N_SU3, Su3Irrep

J_MAX_DEFAULT: int = 16
"""Default box half-width ``M`` for the ``[0, M]²`` exact-sum region.

At the couplings of interest (``t ≳ 4``, i.e. ``g ≲ 0.5`` canonical) the terms
beyond ``p, q ≈ 8`` are below ``1e-12``, so ``M = 16`` makes the exact box
effectively complete and the rigorous tail negligible.
"""


@dataclass(frozen=True)
class Su3CharacterTailSum:
    """Rigorous upper bound on the SU(3) character sum ``Z_t``.

    Field names mirror `large_field_kp.CharacterTailSum` for drop-in use.

      * ``partial_sum`` — exact sum of true terms over ``[0, M]² \\ {(0,0)}``.
      * ``tail_bound`` — rigorous bound on the box complement (``+∞`` if the
        geometric ratio test fails at the cutoff).
      * ``upper_bound`` — ``partial_sum + tail_bound`` (a true upper bound on
        ``Z_t``).
      * ``tail_ratio`` — ``ρ(M+1)``; the tail is geometric iff ``< 1``.
      * ``tail_finite`` — ``ρ(M+1) < 1``.
      * ``j_max_int`` — the box half-width ``M`` (named for SU(2) compatibility).
      * ``t`` — the heat-kernel time used.
    """

    partial_sum: float
    tail_bound: float
    upper_bound: float
    tail_ratio: float
    tail_finite: bool
    j_max_int: int
    t: float


def _t_from_g_su3(g_k: float, t_choice: HeatKernelConvention) -> float:
    """Heat-kernel time ``t`` for SU(3): ``CANONICAL: 1/g²``; ``WILSON: 2N/g² = 6/g²``."""
    if t_choice is HeatKernelConvention.CANONICAL:
        return 1.0 / (g_k * g_k)
    if t_choice is HeatKernelConvention.WILSON:
        return 2.0 * N_SU3 / (g_k * g_k)  # 2N = 6
    raise ValueError(
        f"Manton convention has bound shape exp(-c·g²); Z_t requires "
        f"CANONICAL or WILSON.  Got: {t_choice!r}"
    )


def _f(x: int) -> float:
    """``f(x) = (x² + 3x)/3`` — the per-index lower bound on ``C_2`` (``pq/3`` dropped)."""
    return (x * x + 3 * x) / 3.0


def majorant_g(x: int, t: float) -> float:
    """``g(x) = (x+1)⁴ · exp(-t · f(x))`` — the factorized per-index majorant."""
    return (x + 1) ** 4 * math.exp(-t * _f(x))


def majorant_ratio(x: int, t: float) -> float:
    """``ρ(x) = g(x+1)/g(x) = ((x+2)/(x+1))⁴ · exp(-t (2x+4)/3)`` (decreasing in ``x``)."""
    return ((x + 2.0) / (x + 1.0)) ** 4 * math.exp(-t * (2 * x + 4) / 3.0)


def _geometric_tail_1d(x_start: int, t: float) -> float:
    """Rigorous bound on ``Σ_{x ≥ x_start} g(x)``.

    ``= g(x_start) / (1 - ρ(x_start))`` when ``ρ(x_start) < 1`` (the ratio is
    decreasing, so ``ρ(x) ≤ ρ(x_start) < 1`` for all ``x ≥ x_start`` and the
    geometric bound is valid); ``+∞`` otherwise.
    """
    r = majorant_ratio(x_start, t)
    if r < 1.0:
        return majorant_g(x_start, t) / (1.0 - r)
    return float("inf")


def su3_heat_kernel_character_tail_Z(
    g_k: float,
    t_choice: HeatKernelConvention,
    j_max_int: int = J_MAX_DEFAULT,
) -> Su3CharacterTailSum:
    """Rigorous upper bound on ``Z_t = Σ_{(p,q)≠(0,0)} dim(p,q)² e^{-t C_2(p,q)}``.

    Exact box sum over ``[0, M]²`` (``M = j_max_int``) plus the two-dimensional
    geometric tail bound derived in the module docstring.  Drop-in compatible
    with `large_field_kp.heat_kernel_character_tail_Z`.
    """
    if g_k <= 0:
        raise ValueError(f"g_k must be positive; got {g_k}")
    if j_max_int < 1:
        raise ValueError(f"j_max_int (box half-width) must be ≥ 1; got {j_max_int}")

    t = _t_from_g_su3(g_k, t_choice)
    box_m = j_max_int

    # Exact partial sum of TRUE terms over the box, excluding the trivial irrep.
    partial = 0.0
    g_full_box = 0.0  # Σ_{x=0}^{M} g(x), for the 1-D majorant full sum
    for x in range(box_m + 1):
        g_full_box += majorant_g(x, t)
    for p in range(box_m + 1):
        for q in range(box_m + 1):
            if p == 0 and q == 0:
                continue
            irr = Su3Irrep(p, q)
            partial += (irr.dimension * irr.dimension) * math.exp(-t * float(irr.casimir))

    # 1-D tail Σ_{x ≥ M+1} g(x) and the full 1-D majorant G = Σ_{x ≥ 0} g(x).
    tail_1d = _geometric_tail_1d(box_m + 1, t)
    g_full = g_full_box + tail_1d  # rigorous upper bound on Σ_{x ≥ 0} g(x)

    # 2-D tail over the box complement {p ≥ M+1} ∪ {q ≥ M+1}, union bound:
    #   ≤ (Σ_{p ≥ M+1} g(p))·G + G·(Σ_{q ≥ M+1} g(q)) = 2 · tail_1d · G.
    if math.isfinite(tail_1d) and math.isfinite(g_full):
        tail_bound = 2.0 * tail_1d * g_full
        tail_finite = True
    else:
        tail_bound = float("inf")
        tail_finite = False

    upper = partial + tail_bound

    return Su3CharacterTailSum(
        partial_sum=partial,
        tail_bound=tail_bound,
        upper_bound=upper,
        tail_ratio=majorant_ratio(box_m + 1, t),
        tail_finite=tail_finite,
        j_max_int=box_m,
        t=t,
    )


if __name__ == "__main__":
    print("SU(3) heat-kernel character sum Z_t (rigorous upper bound)")
    print("=" * 64)
    print(f"  {'g':>5} {'t':>8} {'partial':>14} {'tail':>12} {'Z_upper':>14} {'finite':>7}")
    for g in (0.20, 0.25, 0.30, 0.35, 0.40, 0.45, 0.485, 0.50):
        z = su3_heat_kernel_character_tail_Z(g, HeatKernelConvention.CANONICAL)
        tail_str = f"{z.tail_bound:.3e}" if math.isfinite(z.tail_bound) else "inf"
        print(f"  {g:>5.3f} {z.t:>8.3f} {z.partial_sum:>14.6e} {tail_str:>12} "
              f"{z.upper_bound:>14.6e} {str(z.tail_finite):>7}")
    print()
    print("  q = mu_plaq·Z_t < 1 (mu=16) is the large-field convergence test;")
    print("  Z_t < 1/16 = 0.0625 is the threshold (g_max_lf ≈ 0.485).")
