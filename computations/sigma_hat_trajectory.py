"""σ̂ trajectory and the global budget Σ_k η_k < σ̂_0.

Milestone 3.4 of `work_plan.md`.  Computes the per-step
degradation η_k of the renormalized string tension σ̂_k across an
RG trajectory and checks the global budget closure

    Σ_k η_k  <  σ̂_0,

which is the make-or-break inductive-step closure of the SU(2)
pilot (per `docs/context.md` §3.3 condition 4, `docs/outline.md` §10.4).

This module:
  1. Computes η_k per step from upstream Δ_∩ (3.3), modulated by
    the polymer-expansion-residual factor.
  2. Aggregates Σ_k η_k.
  3. Tests against a chosen σ̂_0 starting value.
  4. Generates the σ̂ trajectory figure.

## Re-examination of the Q'-boundary (Decision 1 record)

The Phase-3 kickoff Decision 1 left a recorded re-examination point
at 3.4: does the ℚ-only Q' representation suffice for the global
budget Σ_k η_k < σ̂_0, or does it need a separate constructive-limit
argument?

**Empirical answer for the placeholder trajectory:** Σ_k η_k = 0
because Δ_∩ = 0 throughout (3.3 with placeholder K-values).  This
is a trivial pass; it tells us nothing about whether Q' suffices
when real g-dependent K-values land.

**Structural answer:** even with real, non-trivial Δ_∩ values, the
SUM Σ_k η_k of finitely many rational terms is itself rational —
ℚ suffices for ANY FINITE truncation of the sum.  The genuine
question is convergence as K → ∞: does Σ_{k=0}^∞ η_k stay below
σ̂_0?

That is a constructive-limit statement, NOT a statement about
finite rational sums.  Concretely it requires either:

  (i) A rational tail bound: for some K_0 and explicit q : Q',
      Σ_{k ≥ K_0} η_k ≤ q.  Then the full sum is bounded by
      finite-sum + q, both rational.  Q' suffices.

  (ii) A genuine Cauchy / constructive-limit argument: the partial
      sums S_K = Σ_{k ≤ K} η_k form a Cauchy sequence (with
      explicit modulus), and the limit is bounded.  This needs
      more than Q' — a constructive-reals layer.

For the SU(2) pilot at finite K (work_plan 3.5 picks K ≥ 3), we
can use option (i) — a rational tail bound from the geometric
decay of N_p(k) and the bounded per-plaquette factors.  Q' suffices
at the truncation, with a rational tail-bound argument.

For the FULL Phase-1-output mass gap (Σ_{k=0}^∞), a separate
constructive-limit module (call it `YMGap/Constructive/Limit.lean`)
would be needed.  That's downstream of 3.5 and beyond Phase 3's
scope.

Decision: Q' SUFFICES for the SU(2) pilot at finite K.  Recording
this here.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.overlap_kp import delta_cap

# --------------------------------------------------------------------------
# Placeholder constants
# --------------------------------------------------------------------------

PLACEHOLDER_ETA_COUPLING: Final[float] = 0.5
"""Placeholder coupling between Δ_∩ and η_k.

The actual relationship between the buffer-K growth Δ_∩ and the
string-tension degradation η is set by the polymer-expansion-residual
factor in the σ̂-transport derivation.  Placeholder: η_k = coupling · Δ_∩.

When the actual derivation lands, this is the replacement point.
"""


# --------------------------------------------------------------------------
# Result dataclasses
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SigmaHatStep:
    """One step of the σ̂ trajectory."""

    scale_k: int
    sigma_hat: float
    g_k: float
    eta_k: float  # the degradation FROM scale k to k+1
    convention: HeatKernelConvention


@dataclass(frozen=True)
class SigmaHatTrajectory:
    """The full σ̂ trajectory with the global budget check."""

    steps: list[SigmaHatStep]
    sigma_hat_initial: float
    total_eta: float
    """Σ_k η_k across the trajectory."""
    budget_closure: bool
    """True iff Σ_k η_k < σ̂_0 — the make-or-break Phase-3 condition."""
    convention: HeatKernelConvention


# --------------------------------------------------------------------------
# Compute the trajectory
# --------------------------------------------------------------------------


def compute_eta(
    g_k: float,
    g_k_next: float,
    t_choice: HeatKernelConvention,
    eta_coupling: float = PLACEHOLDER_ETA_COUPLING,
) -> float:
    """Per-step η_k from Δ_∩ via the polymer-expansion-residual factor.

    Placeholder: η_k = `eta_coupling` · Δ_∩(g_k, g_k_next).  The
    relationship between Δ_∩ and η is set by the σ̂-transport
    analysis (Bałaban-style; deferred).
    """
    d = delta_cap(g_k, g_k_next, t_choice)
    return eta_coupling * d


def sigma_hat_trajectory(
    g_trajectory: list[float],
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    eta_coupling: float = PLACEHOLDER_ETA_COUPLING,
) -> SigmaHatTrajectory:
    """The σ̂ trajectory σ̂_0, σ̂_1, …, σ̂_K and the budget closure check.

    σ̂_{k+1} = σ̂_k - η_k, with η_k from `compute_eta`.

    Per work_plan 3.4, returns the cumulative degradation and a
    boolean indicating whether Σ_k η_k < σ̂_0 (the inductive-step
    budget closure).
    """
    if sigma_hat_initial <= 0:
        raise ValueError(f"sigma_hat_initial must be positive; got {sigma_hat_initial}")

    steps: list[SigmaHatStep] = []
    sigma_hat = sigma_hat_initial
    total_eta = 0.0

    for k in range(len(g_trajectory)):
        # η_k is the FROM-this-step transition.  For the last k there's no next.
        if k < len(g_trajectory) - 1:
            eta_k = compute_eta(
                g_trajectory[k], g_trajectory[k + 1], t_choice, eta_coupling
            )
        else:
            eta_k = 0.0
        steps.append(
            SigmaHatStep(
                scale_k=k,
                sigma_hat=sigma_hat,
                g_k=g_trajectory[k],
                eta_k=eta_k,
                convention=t_choice,
            )
        )
        total_eta += eta_k
        sigma_hat -= eta_k  # for the NEXT step

    budget_closure = total_eta < sigma_hat_initial

    return SigmaHatTrajectory(
        steps=steps,
        sigma_hat_initial=sigma_hat_initial,
        total_eta=total_eta,
        budget_closure=budget_closure,
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# Figure
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/sigma-hat-trajectory.svg"


def plot_sigma_hat_trajectory(
    g_trajectory: list[float] | None = None,
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
) -> str:
    """Plot σ̂_k vs k and the cumulative η budget."""
    from pathlib import Path

    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if g_trajectory is None:
        from computations.overlap_measure import standard_su2_trajectory

        traj = standard_su2_trajectory(k_max=10)
        g_trajectory = traj[0]

    result = sigma_hat_trajectory(g_trajectory, sigma_hat_initial, t_choice)
    k_values = np.arange(len(result.steps))
    sigma_values = [s.sigma_hat for s in result.steps]
    eta_values = [s.eta_k for s in result.steps]
    cumulative_eta = np.cumsum(eta_values)

    fig, (ax_left, ax_right) = plt.subplots(1, 2, figsize=(10.0, 4.5))
    ax_left.plot(k_values, sigma_values, "o-", color="tab:blue", markersize=5,
                 label=r"$\widehat{\sigma}_k$")
    ax_left.axhline(sigma_hat_initial, linestyle="--", alpha=0.4, color="gray",
                    label=r"$\widehat{\sigma}_0$ (initial)")
    ax_left.set_xlabel("RG step k")
    ax_left.set_ylabel(r"$\widehat{\sigma}_k$")
    ax_left.set_title("Renormalized string tension trajectory")
    ax_left.grid(True, alpha=0.3)
    ax_left.legend()

    ax_right.plot(
        k_values, cumulative_eta, "o-", color="tab:red", markersize=5,
        label=r"$\sum_{j \leq k} \eta_j$"
    )
    ax_right.axhline(
        sigma_hat_initial, linestyle="--", alpha=0.4, color="gray",
        label=r"$\widehat{\sigma}_0$ budget cap"
    )
    ax_right.set_xlabel("RG step k")
    ax_right.set_ylabel(r"cumulative $\sum \eta$")
    ax_right.set_title(
        f"η budget closure: Σ η = {result.total_eta:.3e}; "
        f"closes: {result.budget_closure}"
    )
    ax_right.grid(True, alpha=0.3)
    ax_right.legend()

    fig.suptitle(
        f"SU(2) σ̂-trajectory + budget closure ({t_choice.value}, σ̂_0 = {sigma_hat_initial})"
    )
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
    result = sigma_hat_trajectory(g_traj, sigma_hat_initial=1.0)
    print(f"σ̂ trajectory (σ̂_0 = {result.sigma_hat_initial}, "
          f"{len(result.steps)} steps):")
    for s in result.steps:
        print(f"  k={s.scale_k:2d}  g={s.g_k:.4f}  σ̂={s.sigma_hat:.4f}  "
              f"η_k={s.eta_k:.4e}")
    print(f"\n  Total Σ η_k       = {result.total_eta:.6e}")
    print(f"  Budget closes?    = {result.budget_closure}")
    print(f"  σ̂_K (final)      = {result.steps[-1].sigma_hat:.6f}")
    path = plot_sigma_hat_trajectory()
    print(f"  figure: {path}")
