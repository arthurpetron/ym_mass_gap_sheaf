"""Union-bound overlap measure for SU(2).

Milestone 1.4 of `work_plan.md`.  Aggregates the per-plaquette
buffer-shell bound of 1.3 over all plaquettes at scale k via the
union bound, then checks whether the resulting per-step bounds are
summable across an RG trajectory.

The aggregate bound at scale k is

    μ_k(Ω_k^∩)  ≤  N_p(k) · P_plaquette(δ_k, g_k)
                 ≤  N_p(k) · C(δ_k) · exp(-κ/g_k²) · g_k^β

(per `context.md` §3.4 / `outline.md` §18.5), where:

  * `N_p(k)` is the number of plaquettes at scale k (geometry-dependent;
    typically `(L_0 / a_k)^4 = (L_0/a_0)^4 · b^{-4k}` in 4D
    block-spinning with factor `b`),
  * `P_plaquette(δ_k, g_k)` is the 1.3 single-plaquette bound,
  * the (C, κ, β) factorization is inherited from 1.3.

The summability check Σ_k μ_k(Ω_k^∩) < ∞ is the test of context.md
§3.4's structural claim that "the overlap measure is summable in k"
because κ is convention-controlled and N_p(k) decays geometrically
in block-spinning.

# What this module does NOT do

- Does not optimize the union bound.  The bound is the union bound,
  full stop; tightening (chaining / correlated-plaquette estimates)
  is `docs/outline.md` §17.1's deferred analytic obligation, and the
  union-bound looseness identified in 1.3's notes propagates.
- Does not commit to a specific β-function running.  The
  ``g_trajectory`` and ``delta_trajectory`` are inputs supplied by
  the caller; this module's job is to aggregate the bound, not to
  derive the RG running.  Concrete trajectories are 3.x's input data.
- Does not check the FULL Phase-3 budget closure ``Σ_k η_k < σ̂_0``.
  That is 3.4.  This module checks ``Σ_k μ_k(Ω_k^∩) < ∞``, the
  weaker structural summability of the overlap measure itself.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Final

import numpy as np
from numpy.typing import NDArray

from computations.buffer_shell import (
    BufferShellBound,
    single_plaquette_buffer_measure,
)
from computations.heat_kernel import HeatKernelConvention

# --------------------------------------------------------------------------
# Per-step aggregate bound
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class UnionBoundResult:
    """The per-scale aggregate bound on μ_k(Ω_k^∩).

    Carries both the value and the inputs for downstream audit.
    """

    bound: float
    """The aggregate bound ``N_p · P_plaquette``."""
    per_plaquette: float
    """The 1.3 single-plaquette bound at (δ_k, g_k).  Defaults to
    ``BufferShellBound.uniform_value()`` since the 2026-05-24 Haar-floor
    audit; pass ``use_uniform=False`` to use the legacy work_plan-spec
    ``value()`` (which is NOT a uniform upper bound at small g)."""
    n_plaquettes: int
    """Plaquette count `N_p(k)`."""
    g_k: float
    delta_k: float
    convention: HeatKernelConvention
    plaquette_bound_breakdown: BufferShellBound
    """The full (C, κ, β, haar_floor) breakdown from 1.3."""
    use_uniform: bool
    """True if the per-plaquette bound came from ``uniform_value()``
    (the verified uniform upper bound); False if from legacy ``value()``."""


def union_bound_overlap(
    n_plaquettes: int,
    g_k: float,
    delta_k: float,
    t_choice: HeatKernelConvention,
    use_uniform: bool = True,
) -> UnionBoundResult:
    """Aggregate bound: ``N_p · P_plaquette(δ_k, g_k)``.

    Per work_plan 1.4.  Raises for Manton (inherited from 1.3).

    Since the 2026-05-24 Haar-floor audit
    (``notes/single-plaquette-derivation.md`` §4), the default per-plaquette
    bound is ``BufferShellBound.uniform_value()`` — the verified-uniform
    Haar-floor + correctly-shaped tail term that dominates the direct
    heat-kernel integral over the full physical range.  Pass
    ``use_uniform=False`` to fall back to the legacy work_plan-spec
    ``value()`` (which is NOT a uniform upper bound at small g and is
    retained for asymptotic-reference and audit-trail purposes).
    """
    if n_plaquettes < 0:
        raise ValueError(f"n_plaquettes must be ≥ 0; got {n_plaquettes}")
    plaquette_bound = single_plaquette_buffer_measure(delta_k, g_k, t_choice)
    pp_value = (
        plaquette_bound.uniform_value() if use_uniform else plaquette_bound.value()
    )
    return UnionBoundResult(
        bound=n_plaquettes * pp_value,
        per_plaquette=pp_value,
        n_plaquettes=n_plaquettes,
        g_k=g_k,
        delta_k=delta_k,
        convention=t_choice,
        plaquette_bound_breakdown=plaquette_bound,
        use_uniform=use_uniform,
    )


def g_max_for_validity(
    n_plaquettes: int,
    delta_k: float,
    t_choice: HeatKernelConvention,
    target_bound: float = 1.0,
    g_search_range: tuple[float, float] = (0.1, 5.0),
    n_search: int = 200,
    use_uniform: bool = True,
) -> float | None:
    """The largest g_k such that the union bound is ≤ ``target_bound``.

    Returns ``None`` if the union bound exceeds ``target_bound`` for
    every g_k in the search range (trivial / vacuous bound), or the
    upper edge of the search range if the bound is always valid.

    Useful for context.md §3.4's "threshold `g_max` above which the
    union bound fails."  ``use_uniform`` selects the per-plaquette
    bound shape; see ``union_bound_overlap``.
    """
    g_values = np.linspace(g_search_range[0], g_search_range[1], n_search)
    valid_gs = [
        float(g)
        for g in g_values
        if union_bound_overlap(
            n_plaquettes, float(g), delta_k, t_choice, use_uniform=use_uniform
        ).bound
        <= target_bound
    ]
    if not valid_gs:
        return None
    return max(valid_gs)


# --------------------------------------------------------------------------
# Trajectory-level summability check
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SummabilityResult:
    """The result of summing the per-step bounds across an RG trajectory.

    Tracks per-step bounds, partial sums, and the eventual total.
    Carries flags indicating whether each step's bound was valid
    (i.e., < 1, since a bound > 1 on a probability is trivial).
    """

    per_step_bounds: list[float]
    partial_sums: list[float]
    total: float
    """The full sum Σ_k μ_k_bound across the supplied trajectory."""
    all_steps_valid: bool
    """True iff every per-step bound is ≤ 1 (probability admissible)."""
    n_steps: int
    convention: HeatKernelConvention


def is_summable_in_k(
    g_trajectory: list[float],
    n_p_trajectory: list[int],
    delta_trajectory: list[float],
    t_choice: HeatKernelConvention,
    use_uniform: bool = True,
) -> SummabilityResult:
    """Compute the partial sums of ``μ_k(Ω_k^∩)`` bounds across the trajectory.

    The three trajectories must have equal length: (g_k, N_p(k), δ_k)
    for k = 0, 1, …, K.

    The "summability" check is empirical: returns the full total and
    each partial sum; the caller decides whether the sum is "small
    enough."  Per work_plan 1.4 this is the test of whether
    Σ_k μ_k(Ω_k^∩) < ∞ structurally.

    Default ``use_uniform=True`` uses the verified-uniform per-plaquette
    bound (Haar-floor audit landing 2026-05-24); pass False for the
    legacy work_plan-spec ``value()`` (asymptotic-reference only).
    """
    if not (len(g_trajectory) == len(n_p_trajectory) == len(delta_trajectory)):
        raise ValueError(
            "g_trajectory, n_p_trajectory, delta_trajectory must have equal length"
        )
    per_step: list[float] = []
    partials: list[float] = []
    running_total = 0.0
    all_valid = True
    for g, n_p, d in zip(g_trajectory, n_p_trajectory, delta_trajectory, strict=True):
        result = union_bound_overlap(n_p, g, d, t_choice, use_uniform=use_uniform)
        per_step.append(result.bound)
        running_total += result.bound
        partials.append(running_total)
        if result.bound > 1.0:
            all_valid = False
    return SummabilityResult(
        per_step_bounds=per_step,
        partial_sums=partials,
        total=running_total,
        all_steps_valid=all_valid,
        n_steps=len(g_trajectory),
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# Standard SU(2) RG trajectory generator (for the figure / test fixtures)
# --------------------------------------------------------------------------


def standard_su2_trajectory(
    k_max: int = 10,
    b: float = 2.0,
    g_0: float = 1.2,
    n_p_0: int = 10_000,
    delta_alpha: float = 0.5,
) -> tuple[list[float], list[int], list[float]]:
    """A canonical SU(2) RG trajectory for testing / plotting.

    Returns ``(g_trajectory, n_p_trajectory, delta_trajectory)`` of
    length ``k_max + 1``.

    Conventions used:
      * Block factor `b > 1`, with `N_p(k) = n_p_0 · b^{-4k}` (4D coarsening).
      * Two-loop SU(2) β-function approximation:
        ``1/g_k² ≈ 1/g_0² + (b_0/16π²) · k · log b``
        where ``b_0 = 22/3`` for SU(2) at one loop.
      * δ_k = g_k^delta_alpha, with ``delta_alpha`` the smallness
        exponent (outline §6.4 has ``δ_k ~ g_k^α`` for α ∈ (0,1)).

    This is a PLACEHOLDER trajectory: numerically-reasonable shape
    but not a derived RG flow.  Real RG running is 3.x's input from
    the small-field calculation.
    """
    if k_max < 0:
        raise ValueError(f"k_max must be ≥ 0; got {k_max}")
    if b <= 1.0:
        raise ValueError(f"block factor b must be > 1; got {b}")
    if g_0 <= 0:
        raise ValueError(f"initial coupling g_0 must be positive; got {g_0}")

    # One-loop SU(2) β: b_0 = (11/3) C_2(adj) = (11/3) · 2 = 22/3.
    b_0 = 22.0 / 3.0
    log_b = math.log(b)

    g_traj: list[float] = []
    n_p_traj: list[int] = []
    delta_traj: list[float] = []

    inv_g_sq_0 = 1.0 / (g_0 * g_0)
    for k in range(k_max + 1):
        # Coarsening direction: increasing k → larger a_k, larger g_k (confinement direction).
        # One-loop: 1/g_k² = 1/g_0² - (b_0 / 16π²) · k · log b.
        # (Negative second term because we go TOWARDS strong coupling as k grows.)
        inv_g_sq_k = inv_g_sq_0 - (b_0 / (16.0 * math.pi * math.pi)) * k * log_b
        if inv_g_sq_k <= 0.0:
            # Coupling blows up (Landau pole); cap k at this point.
            break
        g_k = 1.0 / math.sqrt(inv_g_sq_k)
        g_traj.append(g_k)
        n_p_traj.append(max(1, int(round(n_p_0 * b ** (-4.0 * k)))))
        delta_traj.append(g_k ** delta_alpha)

    return g_traj, n_p_traj, delta_traj


# --------------------------------------------------------------------------
# Figure: overlap measure across the RG trajectory
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = (
    "visualizations/pilot/su2/overlap-vs-rg-step.svg"
)


def plot_overlap_vs_rg_step(
    g_trajectory: list[float] | None = None,
    n_p_trajectory: list[int] | None = None,
    delta_trajectory: list[float] | None = None,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
) -> str:
    """Plot μ_k(Ω_k^∩) per-step bound and cumulative sum vs k.

    If trajectories are not supplied, uses ``standard_su2_trajectory()``.
    """
    from pathlib import Path

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if g_trajectory is None or n_p_trajectory is None or delta_trajectory is None:
        g_trajectory, n_p_trajectory, delta_trajectory = standard_su2_trajectory()

    result = is_summable_in_k(g_trajectory, n_p_trajectory, delta_trajectory, t_choice)
    k_values: NDArray[np.float64] = np.arange(len(g_trajectory), dtype=np.float64)

    fig, (ax_left, ax_right) = plt.subplots(1, 2, figsize=(10.0, 4.5))
    ax_left.plot(k_values, result.per_step_bounds, "o-", color="tab:blue", markersize=5)
    ax_left.set_yscale("log")
    ax_left.set_xlabel("RG step k")
    ax_left.set_ylabel(r"per-step bound on $\mu_k$")
    ax_left.set_title("Union-bound per-step overlap measure")
    ax_left.grid(True, alpha=0.3)

    ax_right.plot(k_values, result.partial_sums, "o-", color="tab:green", markersize=5)
    ax_right.set_xlabel("RG step k")
    ax_right.set_ylabel(r"partial sum $\sum_{j \leq k} \mu_j$")
    ax_right.set_title(f"Cumulative sum (total = {result.total:.3e})")
    ax_right.grid(True, alpha=0.3)

    fig.suptitle(
        f"SU(2) overlap measure across RG steps "
        f"({t_choice.value} convention, {result.n_steps} steps)"
    )
    fig.tight_layout()

    target_path = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent / DEFAULT_PLOT_PATH
    target_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target_path, format="svg")
    plt.close(fig)
    return str(target_path)


if __name__ == "__main__":
    g_t, n_t, d_t = standard_su2_trajectory(k_max=10)
    print(f"Standard SU(2) trajectory ({len(g_t)} steps):")
    for k, (g, n_p, d) in enumerate(zip(g_t, n_t, d_t, strict=True)):
        print(f"  k={k:2d}  g={g:.4f}  N_p={n_p:8d}  δ={d:.4f}")
    result = is_summable_in_k(g_t, n_t, d_t, HeatKernelConvention.CANONICAL)
    print(f"\nTotal Σ μ_k(Ω_k^∩) = {result.total:.6e}")
    print(f"All per-step bounds ≤ 1: {result.all_steps_valid}")
    path = plot_overlap_vs_rg_step()
    print(f"Figure written to {path}")
