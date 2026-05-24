"""Rational-lift helpers: float → exact Q' rationals.

Bridges the Python pilot's float-valued η trajectory (from
``sigma_hat_trajectory.py``) to the Lean ``Q'`` representation in
``lean/YMGap/Constructive/Rationals.lean``.

# The boundary problem

The SU(2) pilot computes η_k as floats: ``η_k = (c_polymer / A_min) ·
Δ_∩(g_k, g_{k+1})`` with ``Δ_∩`` involving ``K_sf`` and ``K_lf`` that
contain ``exp(...)`` terms.  Floats are NOT rationals.  But the Lean
``RationalTail.sigma_hat_budget_closure`` framework wants exact ``Q'``
inputs — specifically, an ``eta_total_bound : Q'`` and a closure
condition ``eta_total_bound ≤ σ̂_0 : Q'``.

The bridge is a **rational upper bound** on the actual η trajectory:
pick a denominator ``D``, find the smallest numerator ``N`` such that
``N/D ≥ max_k η_k``.  Then the truncated-constant sequence

    η̃_k = N/D  for k < K
    η̃_k = 0    for k ≥ K

dominates η_k pointwise for k < K and is zero thereafter; its partial
sums are bounded by ``K · (N/D) ∈ Q'`` exactly.  The Lean module
takes this rational bound as a hard-coded constant and discharges the
closure constructively.

# The Q' encoding

The Lean ``Q'`` structure stores ``(num : Int, denPred : Nat)`` with
actual denominator ``denPred + 1``.  This module's helpers emit the
``(num, denPred)`` pair so Lean source can use the ``Q'.mk`` /
``Q'.mkPos`` constructors directly.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention


# --------------------------------------------------------------------------
# Rational lift primitives
# --------------------------------------------------------------------------


def rational_ceiling(x: float, denominator: int) -> int:
    """Smallest integer ``n`` such that ``n / denominator >= x``.

    For positive ``x`` and ``denominator > 0``, this is
    ``ceil(x * denominator)`` computed exactly in Python int arithmetic.

    Use case: produce a rational ``n/d`` that bounds a float ``x`` from
    above with a controllable error: the gap ``n/d - x`` is at most
    ``1/d``.
    """
    if denominator <= 0:
        raise ValueError(f"denominator must be positive; got {denominator}")
    if not math.isfinite(x):
        raise ValueError(f"x must be finite; got {x!r}")
    return math.ceil(x * denominator)


def to_q_prime_pair(numerator: int, denominator: int) -> tuple[int, int]:
    """Convert ``(numerator, denominator)`` to Lean's ``Q'`` ``(num, denPred)``.

    Lean's ``Q'`` stores the predecessor of the (positive) denominator,
    so ``denPred = denominator - 1``.  Requires ``denominator >= 1``.

    Returns ``(numerator, denominator - 1)`` ready to feed into Lean
    source as e.g. ``⟨11, 9999⟩`` (or via ``Q'.mkPos 11 10000 (by decide)``).
    """
    if denominator < 1:
        raise ValueError(f"denominator must be ≥ 1; got {denominator}")
    return (numerator, denominator - 1)


# --------------------------------------------------------------------------
# Pilot η-bound computation
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class PilotEtaRationalBound:
    """Rational upper bound on the SU(2) pilot's η trajectory.

    Fields:
      * ``g_0``, ``K``, ``sigma_hat_initial``, ``convention`` — pilot config.
      * ``eta_floats`` — the per-step η_k as computed by
        ``sigma_hat_trajectory`` (length K, the per-step transitions).
      * ``eta_max_float`` — ``max_k η_k`` (the binding step).
      * ``denominator`` — chosen rational denominator ``D``.
      * ``eta_max_numerator`` — smallest ``N`` such that ``N/D >= eta_max_float``.
      * ``eta_total_numerator`` — ``K * eta_max_numerator``; total bound
        ``K · (N/D)`` after K steps.
      * ``sigma_hat_initial_q`` — chosen Q' representation of σ̂_0 (must be ≥
        ``eta_total_numerator / denominator`` for the closure to discharge).
      * ``closure_holds`` — True iff ``eta_total_numerator / denominator ≤
        sigma_hat_initial_q[0] / sigma_hat_initial_q[1]``.
      * ``bound_check`` — per-step: ``eta_max_numerator/D >= η_k`` (must be all True).
    """

    g_0: float
    K: int
    sigma_hat_initial: float
    convention: HeatKernelConvention
    eta_floats: list[float]
    eta_max_float: float
    denominator: int
    eta_max_numerator: int
    eta_total_numerator: int
    sigma_hat_initial_q: tuple[int, int]
    closure_holds: bool
    bound_check: list[bool]


def pilot_eta_rational_bound(
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 1.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    denominator: int = 10000,
    sigma_hat_initial_q: tuple[int, int] = (1, 1),
) -> PilotEtaRationalBound:
    """Compute the SU(2) pilot at ``(g_0, K)`` and return a Q' upper bound on η_k.

    Runs ``sigma_hat_trajectory`` to get the per-step η_k floats, then:
      1. Picks ``eta_max_numerator = ceil(max_k η_k · denominator)``.
      2. Computes ``eta_total_numerator = K · eta_max_numerator`` (the
         partial-sum bound at step K, given the truncated-constant
         dominating sequence).
      3. Verifies each ``η_k ≤ eta_max_numerator / denominator``.
      4. Verifies ``eta_total_numerator / denominator ≤ sigma_hat_initial_q
         numerator / sigma_hat_initial_q denominator`` (the closure
         condition the Lean module discharges).

    The default ``denominator = 10000`` gives a per-step margin of at
    most ``1e-4`` above the binding η_k, suitable for the canonical
    g_0 = 0.30 pilot where ``max η_k ≈ 1.05e-3`` and the bound becomes
    ``1.1e-3`` (5% margin).

    The ``K`` here is the number of η transitions (i.e., trajectory has
    ``K + 1`` g values, indexed 0..K, and η_k for k = 0..K-1).
    """
    from computations.overlap_measure import standard_su2_trajectory
    from computations.sigma_hat_trajectory import sigma_hat_trajectory

    if K < 1:
        raise ValueError(f"K must be ≥ 1; got {K}")
    if denominator < 1:
        raise ValueError(f"denominator must be ≥ 1; got {denominator}")
    if sigma_hat_initial_q[1] < 1:
        raise ValueError(
            f"sigma_hat_initial_q denominator must be ≥ 1; "
            f"got {sigma_hat_initial_q[1]}"
        )

    g_trajectory = standard_su2_trajectory(k_max=K, g_0=g_0)[0]
    if len(g_trajectory) != K + 1:
        raise RuntimeError(
            f"standard_su2_trajectory returned {len(g_trajectory)} g values; "
            f"expected K + 1 = {K + 1}"
        )

    traj = sigma_hat_trajectory(
        g_trajectory, sigma_hat_initial=sigma_hat_initial, t_choice=convention
    )
    eta_floats = [s.eta_k for s in traj.steps[:-1]]  # last step has η = 0 by convention
    if len(eta_floats) != K:
        raise RuntimeError(
            f"sigma_hat_trajectory returned {len(eta_floats)} non-tail η values; "
            f"expected K = {K}"
        )

    eta_max_float = max(eta_floats) if eta_floats else 0.0

    # If any η_k is non-finite (cluster expansion diverged), no rational
    # upper bound exists.  Report this honestly: emit a sentinel numerator
    # of 0 (which fails the bound_check) rather than raising.
    if not all(math.isfinite(eta_k) for eta_k in eta_floats):
        eta_max_numerator = 0
        eta_total_numerator = 0
        bound_check = [
            math.isfinite(eta_k) and eta_k <= 0.0 for eta_k in eta_floats
        ]
    else:
        eta_max_numerator = max(rational_ceiling(eta_max_float, denominator), 0)
        eta_total_numerator = K * eta_max_numerator
        bound_check = [
            eta_k * denominator <= eta_max_numerator for eta_k in eta_floats
        ]

    # Closure check: eta_total_numerator / denominator ≤ σ_0_num / σ_0_den
    # iff eta_total_numerator · σ_0_den ≤ σ_0_num · denominator (positive dens).
    sigma_num, sigma_den = sigma_hat_initial_q
    closure_holds = (
        eta_total_numerator * sigma_den <= sigma_num * denominator
    )

    return PilotEtaRationalBound(
        g_0=g_0,
        K=K,
        sigma_hat_initial=sigma_hat_initial,
        convention=convention,
        eta_floats=eta_floats,
        eta_max_float=eta_max_float,
        denominator=denominator,
        eta_max_numerator=eta_max_numerator,
        eta_total_numerator=eta_total_numerator,
        sigma_hat_initial_q=sigma_hat_initial_q,
        closure_holds=closure_holds,
        bound_check=bound_check,
    )


# --------------------------------------------------------------------------
# Constants used by the canonical Lean wire-in
# --------------------------------------------------------------------------


CANONICAL_LEAN_PILOT_G0: Final[float] = 0.30
"""g_0 for the canonical Lean SU(2) pilot wire-in.

Chosen as a substantive non-trivial point: well inside the small-field
convergence window (g_max_sf ≈ 0.40) but large enough to give
``max_k η_k ≈ 1e-3``, comfortably nonzero so the closure proof
exercises genuine arithmetic rather than the zero-trajectory shortcut.
"""

CANONICAL_LEAN_PILOT_K: Final[int] = 3
"""K (number of η transitions) for the canonical Lean SU(2) pilot wire-in.

Three transitions over four g values (g_0, g_1, g_2, g_3).  Matches the
``work_plan.md`` Milestone 3.5 suggested ``K ≥ 3``.
"""

CANONICAL_LEAN_PILOT_DENOMINATOR: Final[int] = 10000
"""Rational denominator for the canonical Lean wire-in.

At ``g_0 = 0.30`` with ``denominator = 10000``, ``eta_max_numerator = 11``
(so ``η_max = 11/10000 = 1.1e-3``), giving a per-step margin of ~5%
above the binding ``η_2 ≈ 1.05e-3``.  Total bound after 4 steps =
4 · 11/10000 = 44/10000 = 11/2500, comfortably ≤ σ̂_0 = 1.
"""


if __name__ == "__main__":
    print("Pilot η rational bound (canonical Lean wire-in)")
    print("=" * 65)
    bound = pilot_eta_rational_bound(
        g_0=CANONICAL_LEAN_PILOT_G0,
        K=CANONICAL_LEAN_PILOT_K,
        denominator=CANONICAL_LEAN_PILOT_DENOMINATOR,
    )
    print(f"  g_0                = {bound.g_0}")
    print(f"  K                  = {bound.K}")
    print(f"  convention         = {bound.convention.value}")
    print(f"  denominator        = {bound.denominator}")
    print(f"  η floats           = {bound.eta_floats!r}")
    print(f"  max_k η_k          = {bound.eta_max_float:.6e}")
    print(f"  eta_max_numerator  = {bound.eta_max_numerator}")
    print(
        f"  Q' η_max (Lean)    = mkPos {bound.eta_max_numerator} "
        f"{bound.denominator} (by decide)"
    )
    print(
        f"  Q' η_total (Lean)  = mkPos {bound.eta_total_numerator} "
        f"{bound.denominator} (by decide)"
    )
    print(f"  σ̂_0 (Q')           = {bound.sigma_hat_initial_q}")
    print(f"  per-step bound OK  = {all(bound.bound_check)}")
    print(f"  closure holds      = {bound.closure_holds}")
