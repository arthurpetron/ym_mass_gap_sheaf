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
from computations.large_field_kp import LargeFieldKP, compute_large_field_kp
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
) -> OverlapKP:
    """Compute `(ρ_∩, K_∩)` from 3.1 + 3.2 via Proposition 7.1.

    The buffer constants are the conjectured-constants form of
    Proposition 7.1:

        ρ_∩ = min(ρ_sf, ρ_lf),
        K_∩ = K_sf + K_lf  (saturating the upper bound).

    The proposition_7_1_satisfied flag is set after structural check.
    """
    sf = compute_small_field_kp(g_k, scale_k=scale_k, t_choice=t_choice)
    lf = compute_large_field_kp(g_k, scale_k=scale_k, t_choice=t_choice)

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
    g_k: float, g_k_next: float, t_choice: HeatKernelConvention
) -> float:
    """The per-step Δ_∩ budget: K_∩(k+1) ≤ K_∩(k) + Δ_∩(b, g_k).

    Computed as the change in K_∩ across consecutive scales.  Since
    K_sf and K_lf are placeholder-constants in 3.1 / 3.2, Δ_∩ is
    currently ZERO with the placeholder values — when the actual
    K_sf(g_k), K_lf(g_k) lands, this gives the real per-step growth.
    """
    ok = compute_overlap_kp(g_k, t_choice=t_choice)
    ok_next = compute_overlap_kp(g_k_next, t_choice=t_choice)
    # Δ_∩ is non-negative: the buffer K can only grow (or stay flat).
    return max(0.0, ok_next.K_cap - ok.K_cap)


# --------------------------------------------------------------------------
# Trajectory
# --------------------------------------------------------------------------


def first_few_rg_steps(
    g_trajectory: list[float],
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> list[OverlapKP]:
    """Compute the overlap KP certificate at each scale in the trajectory."""
    return [
        compute_overlap_kp(g, scale_k=k, t_choice=t_choice)
        for k, g in enumerate(g_trajectory)
    ]


# --------------------------------------------------------------------------
# Σ_k Δ_∩ summability check (work_plan 3.3 deliverable)
# --------------------------------------------------------------------------


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
) -> DeltaCapBudgetResult:
    """Compute Σ_k Δ_∩(b, g_k) across an RG trajectory.

    work_plan 3.3 task: verify Σ_k Δ_∩ < ∞ (or at least bounded for
    the trajectory tested).

    Note: with placeholder K_sf, K_lf the per-step Δ_∩ is identically
    zero — this trivially passes summability.  When the actual
    g_k-dependent K_sf(g_k), K_lf(g_k) land, this produces the
    real per-step growth.
    """
    per_step: list[float] = []
    partials: list[float] = []
    running = 0.0
    for i in range(len(g_trajectory) - 1):
        d = delta_cap(g_trajectory[i], g_trajectory[i + 1], t_choice=t_choice)
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
