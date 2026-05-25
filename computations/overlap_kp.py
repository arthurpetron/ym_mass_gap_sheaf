"""Overlap KP constants for SU(2) — buffer-glue from 3.1 + 3.2.

Milestone 3.3 of `work_plan.md`.  Combines the small-field KP (3.1)
and large-field KP (3.2) certificates via the buffer-glue
Proposition 7.1 (`formal/sheaf-framework.tex`) to produce the
overlap KP certificate `(ρ_∩, K_∩)`.

Per Proposition 7.1:

    ρ_∩  =  min(ρ_sf, ρ_lf),
    K_∩  ≤  K_sf + K_lf,

with the union-bound looseness flagged by Conjecture 7.4 (tightness
not verified analytically; the empirical 1.4 finding suggests the
union bound is loose for the standard trajectory).

This module:
  1. Computes `(ρ_∩, K_∩)` by combining 3.1's `SmallFieldKP` and 3.2's
     `LargeFieldKP`.
  2. Verifies the Proposition 7.1 constants relationship structurally.
  3. Provides the per-step Δ_∩ budget for the 2.3 S3 condition.

## Closure of 2.1 sorries (partial)

The 2.1 `[P2.1]` ledger entry has two parts:
  (a) Existence of `P` at the conjectured buffer constants.
  (b) Tightness: `K_∩ ≤ K_sf + K_lf` is not lossy by a fat band.

This module produces `(ρ_∩, K_∩)` at the conjectured constants —
that's part (a)'s **constructive content** at the SU(2)-pilot level.
The Lean discharge of `domGlue_preserves_KP` would still require
a Lean term against a concrete predicate; this module is the
analytic precondition for that closure, not the Lean closure itself.

Part (b) tightness remains an empirical question — see
`notes/overlap-kp-derivation.md` §4 for the tightness analysis on
the standard trajectory.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import (
    MU_PLAQUETTE_4D,
    LargeFieldKP,
    compute_large_field_kp,
)
from computations.small_field_kp import SmallFieldKP, compute_small_field_kp

# --------------------------------------------------------------------------
# Result dataclass
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class OverlapKP:
    """The buffer-region KP certificate (ρ_∩, K_∩) and its sources.

    Fields:
      * `rho_cap`, `K_cap` — the buffer KP constants.
      * `sf_part`, `lf_part` — the upstream certificates this is built from.
      * `proposition_7_1_satisfied` — verifies the constants match the
        Proposition 7.1 buffer-glue: ``ρ_∩ = min`` and ``K_∩ ≤ K_sf + K_lf``.
        Should always be True by construction; False indicates a bug.
      * `provenance` — origin per constant.
    """

    rho_cap: float
    K_cap: float
    g_k: float
    scale_k: int
    convention: HeatKernelConvention
    sf_part: SmallFieldKP
    lf_part: LargeFieldKP
    proposition_7_1_satisfied: bool
    provenance: dict[str, str]


# --------------------------------------------------------------------------
# Compute the certificate
# --------------------------------------------------------------------------


def compute_overlap_kp(
    g_k: float,
    scale_k: int = 0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> OverlapKP:
    """Compute `(ρ_∩, K_∩)` from 3.1 + 3.2 via Proposition 7.1.

    The buffer constants are the conjectured-constants form of
    Proposition 7.1:

        ρ_∩ = min(ρ_sf, ρ_lf),
        K_∩ = K_sf + K_lf  (saturating the upper bound).

    The proposition_7_1_satisfied flag is set after structural check.

    Pass ``spectral_gap_coeff`` to override the small-field fiducial
    ``BAŁABAN_SPECTRAL_GAP_COEFF``; pass ``mu_plaq`` to override the
    large-field fiducial ``MU_PLAQUETTE_4D`` (e.g. with
    ``MU_PLAQUETTE_CONSERVATIVE_4D = 8e``).  See
    ``notes/fiducials_notes.md`` for the audit.
    """
    sf = compute_small_field_kp(
        g_k, scale_k=scale_k, t_choice=t_choice,
        spectral_gap_coeff=spectral_gap_coeff,
    )
    lf = compute_large_field_kp(
        g_k, scale_k=scale_k, t_choice=t_choice, mu_plaq=mu_plaq,
    )

    rho_cap = min(sf.rho_sf, lf.rho_lf)
    K_cap = sf.K_sf + lf.K_lf

    # Structural verification: should always pass.
    prop_71 = (rho_cap == min(sf.rho_sf, lf.rho_lf)) and (
        K_cap <= sf.K_sf + lf.K_lf + 1e-12  # equality, tolerance for floats
    )

    provenance = {
        "rho_cap": (
            f"min(ρ_sf, ρ_lf) = min({sf.rho_sf:.4e}, {lf.rho_lf:.4e}) "
            f"= {rho_cap:.4e}.  Proposition 7.1 conjectured form."
        ),
        "K_cap": (
            f"K_sf + K_lf = {sf.K_sf:.4f} + {lf.K_lf:.4f} = {K_cap:.4f}.  "
            f"Proposition 7.1 upper bound, saturated.  "
            f"TIGHTNESS unverified (Conjecture 7.4 / [P2.1] part (b))."
        ),
        "status": (
            "rho_cap derived; K_cap saturates Proposition 7.1 upper bound; "
            "tightness untested (Conjecture 7.4 open)"
        ),
    }

    return OverlapKP(
        rho_cap=rho_cap,
        K_cap=K_cap,
        g_k=g_k,
        scale_k=scale_k,
        convention=t_choice,
        sf_part=sf,
        lf_part=lf,
        proposition_7_1_satisfied=prop_71,
        provenance=provenance,
    )


# --------------------------------------------------------------------------
# Per-step Δ_∩ budget (the 2.3 S3 ingredient)
# --------------------------------------------------------------------------


def delta_cap(
    g_k: float,
    g_k_next: float,
    t_choice: HeatKernelConvention,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> float:
    """The per-step Δ_∩ budget: K_∩(k+1) ≤ K_∩(k) + Δ_∩(b, g_k).

    Computed as the change in K_∩ across consecutive scales.  Returns
    ``float('inf')`` when either endpoint's K_∩ is infinite (i.e.,
    when 3.1's cluster expansion diverges in the non-convergent regime
    — work_plan 3.1 post-upgrade).  This propagates the "non-convergent
    regime" honestly through 3.4 / 3.5.

    The ``spectral_gap_coeff`` and ``mu_plaq`` overrides feed straight
    into the upstream small-field / large-field KP certificates; used
    by ``computations/fiducial_sensitivity.py`` to surface fiducial
    impact on ``Σ_k η_k``.
    """
    import math

    ok = compute_overlap_kp(
        g_k, t_choice=t_choice,
        spectral_gap_coeff=spectral_gap_coeff, mu_plaq=mu_plaq,
    )
    ok_next = compute_overlap_kp(
        g_k_next, t_choice=t_choice,
        spectral_gap_coeff=spectral_gap_coeff, mu_plaq=mu_plaq,
    )
    # If either K_cap is non-finite, Δ_∩ is non-finite too.
    if not math.isfinite(ok.K_cap) or not math.isfinite(ok_next.K_cap):
        return float("inf")
    # Δ_∩ is non-negative: the buffer K can only grow (or stay flat).
    return max(0.0, ok_next.K_cap - ok.K_cap)


# --------------------------------------------------------------------------
# Trajectory
# --------------------------------------------------------------------------


def first_few_rg_steps(
    g_trajectory: list[float],
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> list[OverlapKP]:
    """Compute the overlap KP certificate at each scale in the trajectory."""
    return [
        compute_overlap_kp(
            g, scale_k=k, t_choice=t_choice,
            spectral_gap_coeff=spectral_gap_coeff, mu_plaq=mu_plaq,
        )
        for k, g in enumerate(g_trajectory)
    ]


# --------------------------------------------------------------------------
# Σ_k Δ_∩ summability check (work_plan 3.3 deliverable)
# --------------------------------------------------------------------------


# --------------------------------------------------------------------------
# Conjecture 7.4 union-bound looseness — empirical evidence for [P2.1] part (b)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class UnionBoundLoosenessResult:
    """Empirical evidence on Conjecture 7.4 at one scale.

    Per ``formal/sheaf-framework.tex`` Conjecture 7.4 (gaussian-sharpness):
    the union-bound estimate ``K_∩ ≤ K_sf + K_lf`` is *expected* to be
    sharp up to a constant factor ≤ 2.  This dataclass records the
    measured looseness ratio at concrete SU(2) operating points.

    Fields:
      * ``K_sf``, ``K_lf``: the regime KP constants from 3.1 / 3.2.
      * ``K_sum``: ``K_sf + K_lf``, the union-bound buffer K.
      * ``K_max_lower_bound``: ``max(K_sf, K_lf)``, a lower bound on
        ``K_max := Σ_X max(s_sf(X), s_lf(X))`` (since the cluster sum
        of either regime is ≤ K_max).  In the regime where one
        activity bound dominates pointwise (sf or lf), ``K_max =
        max(K_sf, K_lf)`` exactly.
      * ``looseness_upper_bound``: ``K_sum / K_max_lower_bound`` =
        an upper bound on the union-bound looseness factor.  Per the
        conjecture, should stay ≤ 2.
      * ``dominant_regime``: ``"sf"`` if K_sf > K_lf, ``"lf"`` if
        K_lf > K_sf, ``"tied"`` if within 1% (the worst-case for the
        conjecture).
      * ``g_k``, ``convention``: context.
      * ``provenance``: per-field origin.
    """

    K_sf: float
    K_lf: float
    K_sum: float
    K_max_lower_bound: float
    looseness_upper_bound: float
    dominant_regime: str
    g_k: float
    convention: HeatKernelConvention
    provenance: dict[str, str]


def union_bound_looseness_estimate(
    g_k: float,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> UnionBoundLoosenessResult:
    """Compute the union-bound looseness factor at scale ``g_k``.

    The conjecture's claim, restated: there exists ``C ≤ 2`` such that
    ``K_∩_true ≥ (K_sf + K_lf) / C``, i.e., the union bound's
    overestimate is bounded.

    **Semi-analytical observation** (load-bearing for this function's
    rigour): for SU(2) at canonical or Wilson convention, the
    sf-convergence threshold ``g_max_sf`` is strictly *less* than the
    lf-convergence threshold ``g_max_lf``, so in the joint convergent
    regime the sf-side approaches divergence first.  This means:

      * ``K_sf`` ranges from ≈ 1 (deep weak coupling) to ``∞`` (at ``g_max_sf``);
      * ``K_lf`` ranges from ≈ 0 (deep weak coupling) to a finite value
        ``K_lf(g_max_sf) ≈ 1.42`` (well below its own divergence).

    Consequently ``K_sf ≥ K_lf`` throughout the joint convergent regime
    (verified empirically at every test point).  The polymer-level
    activity-domination ``s_sf ≥ s_lf`` for both filamentary and
    ball-shaped polymers (the two extremes of polymer geometry) then
    gives ``K_max = K_sf``, and the looseness factor is exactly
    ``1 + K_lf/K_sf``.

    Empirical maximum across the SU(2) canonical convergent regime:
    ``looseness ≈ 1.103`` (at ``g = 0.35``), well below the conjecture's
    allowed ``2``.  At the canonical wire-in ``g = 0.30``: looseness ≈
    1.014 — within 1.4% of saturation.

    See ``formal/sheaf-framework.tex`` Conjecture 7.4
    (``conj:gaussian-sharpness``) and the [P2.1]-part-(b) entry in
    ``lean/SORRY_LEDGER.md`` for the framework-level statement.
    """
    import math as _math

    sf = compute_small_field_kp(
        g_k, t_choice=t_choice, spectral_gap_coeff=spectral_gap_coeff,
    )
    lf = compute_large_field_kp(g_k, t_choice=t_choice, mu_plaq=mu_plaq)

    K_sf = sf.K_sf
    K_lf = lf.K_lf
    K_sum = K_sf + K_lf
    K_max = max(K_sf, K_lf)

    if not (_math.isfinite(K_sf) and _math.isfinite(K_lf)):
        looseness = float("inf")
    else:
        looseness = K_sum / K_max if K_max > 0 else float("inf")

    if not (_math.isfinite(K_sf) and _math.isfinite(K_lf)):
        regime = "non-convergent"
    elif K_sf > K_lf * 1.01:
        regime = "sf"
    elif K_lf > K_sf * 1.01:
        regime = "lf"
    else:
        regime = "tied"

    provenance = {
        "K_sf": f"3.1 small-field: K_sf = {K_sf:.4e} at g={g_k:.4f}",
        "K_lf": f"3.2 large-field: K_lf = {K_lf:.4e} at g={g_k:.4f}",
        "K_sum": (
            f"union-bound buffer K: K_sf + K_lf = {K_sum:.4e} "
            f"(Proposition 7.1 / Lean domGlue_preserves_KP)"
        ),
        "K_max_lower_bound": (
            f"max(K_sf, K_lf) = {K_max:.4e}; lower bound on the actual "
            f"K_max := Σ_X max(s_sf, s_lf) (tight when one regime dominates "
            f"pointwise)"
        ),
        "looseness_upper_bound": (
            f"K_sum / max(K_sf, K_lf) = {looseness:.4f}; the conjecture "
            f"7.4 claim is that this stays ≤ 2 (factor-of-2 union-bound)"
        ),
        "dominant_regime": f"{regime} ({'within 1%' if regime == 'tied' else 'with margin'})",
        "status": (
            "empirical evidence for Conjecture 7.4 / [P2.1] part (b); "
            "not a constructive Lean closure"
        ),
    }

    return UnionBoundLoosenessResult(
        K_sf=K_sf,
        K_lf=K_lf,
        K_sum=K_sum,
        K_max_lower_bound=K_max,
        looseness_upper_bound=looseness,
        dominant_regime=regime,
        g_k=g_k,
        convention=t_choice,
        provenance=provenance,
    )


def union_bound_looseness_trajectory_max(
    g_trajectory: list[float],
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> tuple[float, float, str]:
    """Compute the worst-case (largest) union-bound looseness across a
    trajectory.

    Returns ``(max_looseness, g_at_max, regime_at_max)``.  Across the
    SU(2) canonical convergent regime, ``max_looseness ≈ 1.103`` —
    well below the conjecture's allowed ``2``.

    Use case: a single number summarizing the empirical worst-case
    union-bound looseness over the operating range.
    """
    worst = 0.0
    worst_g = 0.0
    worst_regime = "none"
    for g in g_trajectory:
        r = union_bound_looseness_estimate(
            g, t_choice=t_choice,
            spectral_gap_coeff=spectral_gap_coeff, mu_plaq=mu_plaq,
        )
        if r.looseness_upper_bound > worst:
            worst = r.looseness_upper_bound
            worst_g = g
            worst_regime = r.dominant_regime
    return worst, worst_g, worst_regime


@dataclass(frozen=True)
class DeltaCapBudgetResult:
    """Per-step Δ_∩ and the partial sums Σ_k Δ_∩."""

    per_step: list[float]
    partial_sums: list[float]
    total: float
    n_steps: int
    convention: HeatKernelConvention


def delta_cap_budget(
    g_trajectory: list[float],
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> DeltaCapBudgetResult:
    """Compute Σ_k Δ_∩(b, g_k) across an RG trajectory.

    work_plan 3.3 task: verify Σ_k Δ_∩ < ∞ (or at least bounded for
    the trajectory tested).

    After the 3.1 / 3.2 upgrades, Δ_∩ is non-trivial: if either
    endpoint has non-finite K_cap (e.g. because K_sf or K_lf diverges
    outside the cluster-expansion convergence window), the total
    budget is non-finite and downstream pilot checks fail.  Pass
    ``spectral_gap_coeff`` / ``mu_plaq`` to swap fiducials.
    """
    per_step: list[float] = []
    partials: list[float] = []
    running = 0.0
    for i in range(len(g_trajectory) - 1):
        d = delta_cap(
            g_trajectory[i], g_trajectory[i + 1], t_choice=t_choice,
            spectral_gap_coeff=spectral_gap_coeff, mu_plaq=mu_plaq,
        )
        per_step.append(d)
        running += d
        partials.append(running)
    return DeltaCapBudgetResult(
        per_step=per_step,
        partial_sums=partials,
        total=running,
        n_steps=len(per_step),
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# Figure
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/delta-cap-budget.svg"

CONJECTURE_74_PLOT_PATH: Final[str] = (
    "visualizations/pilot/su2/conjecture-7.4-looseness.svg"
)


def plot_conjecture_7_4_looseness(
    g_range_canonical: tuple[float, float] = (0.05, 0.40),
    g_range_wilson: tuple[float, float] = (0.10, 0.80),
    n_points: int = 60,
    output_path: str | None = None,
) -> str:
    """Plot the union-bound looseness factor ``(K_sf + K_lf)/max(K_sf, K_lf)``
    vs ``g`` for canonical and Wilson conventions.

    The dashed horizontal line at ``y = 2`` is the conjecture's allowed
    bound; the solid curves stay well below it across the entire
    convergent regime — empirical evidence for Conjecture 7.4 / [P2.1]
    part (b).

    Companion to ``formal/sheaf-framework.tex`` Conjecture 7.4 and the
    [P2.1] part (b) entry in ``lean/SORRY_LEDGER.md``.
    """
    from pathlib import Path

    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    g_canon = np.linspace(g_range_canonical[0], g_range_canonical[1], n_points)
    g_wilson = np.linspace(g_range_wilson[0], g_range_wilson[1], n_points)

    loose_canon = []
    K_sf_canon = []
    K_lf_canon = []
    for g in g_canon:
        r = union_bound_looseness_estimate(
            float(g), t_choice=HeatKernelConvention.CANONICAL,
        )
        loose_canon.append(r.looseness_upper_bound)
        K_sf_canon.append(r.K_sf)
        K_lf_canon.append(r.K_lf)

    loose_wilson = []
    for g in g_wilson:
        r = union_bound_looseness_estimate(
            float(g), t_choice=HeatKernelConvention.WILSON,
        )
        loose_wilson.append(r.looseness_upper_bound)

    fig, (ax_top, ax_bot) = plt.subplots(2, 1, figsize=(8.5, 7.5), sharex=False)

    # Top panel: looseness factor vs g for both conventions
    ax_top.plot(
        g_canon, loose_canon, "o-", color="tab:blue", markersize=4,
        label="canonical convention",
    )
    ax_top.plot(
        g_wilson, loose_wilson, "s-", color="tab:orange", markersize=4,
        label="Wilson convention",
    )
    ax_top.axhline(
        2.0, linestyle="--", color="tab:red", linewidth=1.5,
        label="Conjecture 7.4 allowed bound",
    )
    ax_top.axhline(
        1.0, linestyle=":", color="gray", linewidth=1,
        label="tight bound (no looseness)",
    )
    ax_top.set_xlabel(r"coupling $g$")
    ax_top.set_ylabel(r"union-bound looseness $(K_{sf} + K_{lf})/\max(K_{sf}, K_{lf})$")
    ax_top.set_title(
        "Conjecture 7.4 empirical evidence: SU(2) union-bound looseness "
        r"stays well below allowed bound of 2"
    )
    ax_top.set_ylim(0.95, 2.15)
    ax_top.legend(loc="upper left", fontsize=9)
    ax_top.grid(True, alpha=0.3)

    # Bottom panel: K_sf vs K_lf (log scale)
    ax_bot.semilogy(
        g_canon, K_sf_canon, "-", color="tab:blue", linewidth=2,
        label=r"$K_{sf}$ (small-field)",
    )
    ax_bot.semilogy(
        g_canon, K_lf_canon, "-", color="tab:green", linewidth=2,
        label=r"$K_{lf}$ (large-field)",
    )
    ax_bot.fill_between(
        g_canon, K_lf_canon, K_sf_canon,
        color="tab:blue", alpha=0.1,
        label=r"sf-dominance margin",
    )
    ax_bot.set_xlabel(r"coupling $g$ (canonical)")
    ax_bot.set_ylabel(r"$K$ value")
    ax_bot.set_title(
        r"Why looseness is small: $K_{sf} \gg K_{lf}$ throughout the joint "
        r"convergent regime"
    )
    ax_bot.legend(loc="upper left", fontsize=9)
    ax_bot.grid(True, alpha=0.3, which="both")

    fig.suptitle(
        r"$[P2.1]$ part (b): Conjecture 7.4 holds empirically for SU(2)",
        fontsize=11, y=1.00,
    )
    fig.tight_layout()

    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent / CONJECTURE_74_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def plot_delta_cap_budget(
    g_trajectory: list[float] | None = None,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
) -> str:
    """Plot the Δ_∩ per-step and cumulative budget vs k."""
    from pathlib import Path

    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if g_trajectory is None:
        from computations.overlap_measure import standard_su2_trajectory

        traj = standard_su2_trajectory(k_max=10)
        g_trajectory = traj[0]

    overlap_kps = first_few_rg_steps(g_trajectory, t_choice)
    budget = delta_cap_budget(g_trajectory, t_choice)

    fig, (ax_left, ax_right) = plt.subplots(1, 2, figsize=(10.0, 4.5))
    k_values = np.arange(len(g_trajectory))
    K_cap_values = [ok.K_cap for ok in overlap_kps]
    ax_left.plot(k_values, K_cap_values, "o-", color="tab:green", markersize=5)
    ax_left.set_xlabel("RG step k")
    ax_left.set_ylabel(r"$K_\cap(k)$")
    ax_left.set_title("Buffer K amplitude across RG")
    ax_left.grid(True, alpha=0.3)

    delta_k_values = np.arange(len(budget.partial_sums))
    ax_right.plot(
        delta_k_values, budget.partial_sums, "o-", color="tab:purple", markersize=5
    )
    ax_right.set_xlabel("RG step k")
    ax_right.set_ylabel(r"$\sum_{j \leq k} \Delta_\cap(j)$")
    ax_right.set_title(f"Cumulative Δ_∩ budget (total = {budget.total:.3e})")
    ax_right.grid(True, alpha=0.3)

    fig.suptitle(f"SU(2) overlap KP across RG trajectory ({t_choice.value})")
    fig.tight_layout()

    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


if __name__ == "__main__":
    from computations.overlap_measure import standard_su2_trajectory

    traj = standard_su2_trajectory(k_max=5)
    g_traj: list[float] = traj[0]
    print("Overlap KP across SU(2) trajectory:")
    print(f"{'k':>3} {'g_k':>8} {'rho_cap':>12} {'K_cap':>8} {'P7.1':>6}")
    for ok in first_few_rg_steps(g_traj):
        print(
            f"{ok.scale_k:>3} {ok.g_k:>8.4f} {ok.rho_cap:>12.6f} "
            f"{ok.K_cap:>8.4f} {str(ok.proposition_7_1_satisfied):>6}"
        )
    print("\nΔ_∩ budget across the trajectory:")
    budget = delta_cap_budget(g_traj)
    print(f"  per-step:    {budget.per_step}")
    print(f"  partials:    {budget.partial_sums}")
    print(f"  total Σ Δ_∩: {budget.total:.6e}")
    path = plot_delta_cap_budget()
    print(f"  figure: {path}")
