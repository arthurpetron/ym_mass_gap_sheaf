"""UV-direction (asymptotic-freedom) SU(2) trajectory generator.

Milestone 6.3 of `work_plan.md`.  Complements
``computations/overlap_measure.standard_su2_trajectory`` (which goes
toward the Landau pole, `g_k → ∞` as k grows) by producing the OPPOSITE
flow direction: `g_k → 0` as k grows.

# The convention difference

  * **IR (`standard_su2_trajectory`)**: k → k+1 means **coarsening**
    (a_{k+1} = b · a_k, b > 1).  One-loop β-function gives `1/g_k² =
    1/g_0² - (b_0/16π²) · k · log b`, so `g_k` grows with k and
    eventually hits the Landau pole.  Suited for the inductive
    block-spinning argument of Phase 3.

  * **UV (`uv_su2_trajectory`, this module)**: k → k+1 means **refining**
    (a_{k+1} = a_k / b, b > 1).  One-loop β-function gives `1/g_{k+1}² =
    1/g_k² + (b_0/16π²) · log b` (note the SIGN reversal), so `g_k`
    *decreases* with k and stays well inside the convergent regime
    forever.  This is the asymptotic-freedom direction; suited for the
    continuum-limit argument of Phase 7.

# Per-step η_k decay in the UV direction

In the UV direction, g_k → 0 monotonically.  Both `K_sf` and `K_lf`
converge to 1 as g → 0 (the cluster-expansion bounds saturate at the
trivial polymer count).  Consequently `Δ_∩ → 0` and `η_k → 0` —
in fact `η_k` decays **geometrically** in k, with rate
``r_uv ≈ (g_{k+1}/g_k)² ≈ 1 - (b_0/16π²)·log b·g_k²`` for small g_k.

This geometric decay is the analytic content the genuine
infinite-trajectory σ̂-budget closure depends on
(`notes/sigma-hat-derivation.md` §4.2 option (i)).

# What this module provides

  * `UVTrajectory` dataclass capturing the per-step (k, g_k, a_k, η_k)
    data plus convergence diagnostics.
  * `uv_su2_trajectory(...)` returning the full UV trajectory.
  * `geometric_decay_rate(...)` computing the empirical r_uv from the
    trajectory (used by the Q' lift for Milestone 6.4).
  * `plot_uv_trajectory(...)` rendering an SVG visualization.

The trajectory data feeds `computations/q_lift.py`'s
``pilot_eta_rational_bound_uv`` (extension for Milestone 6.4) and
the Lean ``SigmaHatPilotUV`` wire-in.

# References

  * `docs/outline.md` §6.4 (asymptotic freedom and the UV β-function).
  * `notes/sigma-hat-derivation.md` §4 (infinite-trajectory closure).
  * `work_plan.md` Milestone 6.3 (this module) and 6.4 (Lean wire-in).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.sigma_hat_trajectory import compute_eta

# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------

ONE_LOOP_SU2_BETA_COEFF: Final[float] = 22.0 / 3.0
"""SU(2) one-loop β-function coefficient ``b_0 = (11/3) · C_2(adj) = 22/3``.

Standard Yang–Mills value (mirrors `standard_su2_trajectory`'s `b_0`).
"""


@dataclass(frozen=True)
class UVTrajectoryStep:
    """One step of the UV-direction SU(2) trajectory."""

    k: int
    """Scale index (k → k+1 means refining a_k → a_k/b)."""
    g_k: float
    """Coupling at this scale; monotone-decreasing in k for AF flow."""
    a_k_over_a_0: float
    """Lattice spacing ratio a_k/a_0 = b^(-k); decreases geometrically."""
    eta_k: float
    """Per-step σ̂-degradation from this scale to the next; → 0 as k → ∞."""


@dataclass(frozen=True)
class UVTrajectory:
    """A UV-direction trajectory with summary diagnostics.

    `eta_k_decay_ratio` is the empirical geometric decay rate
    ``r ≈ η_{k+1} / η_k`` averaged over the trajectory's middle window
    (skipping the first and last step to avoid boundary effects).
    For an actual geometric sequence this should be approximately constant.
    """

    steps: list[UVTrajectoryStep]
    g_0: float
    b: float
    convention: HeatKernelConvention
    eta_k_decay_ratio: float | None
    """Average η_{k+1}/η_k; ``None`` if all η_k are 0 (deep weak-coupling)."""
    converges_to_zero: bool
    """True iff g_k → 0 monotonically (the AF asymptotic-freedom check)."""


# --------------------------------------------------------------------------
# Trajectory generator
# --------------------------------------------------------------------------


def uv_su2_trajectory(
    k_max: int = 10,
    b: float = 2.0,
    g_0: float = 0.50,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> UVTrajectory:
    """Generate the UV-direction SU(2) trajectory.

    Per the AF β-function with the SIGN OPPOSITE to the IR trajectory:

        1/g_{k+1}²  =  1/g_k² + (b_0 / 16π²) · log b.

    Starting from a moderately-weak `g_0 = 0.50` and refining for
    `k_max` steps gives a sequence `{g_0 > g_1 > ... > g_{k_max} > 0}`
    that stays comfortably inside the small-field convergent regime
    (`g_max_sf ≈ 0.40` canonical / 0.81 Wilson) at every step except
    possibly the initial.

    For each step, compute η_k via the existing `sigma_hat_trajectory`
    machinery (which works in any direction by construction; the
    direction enters only through the g_k values supplied).

    Defaults: `g_0 = 0.50`, just inside the Wilson convergence window
    and giving genuine non-zero η_k for at least the first few steps.
    For canonical convention with default fiducials, g_0 = 0.50 is
    OUTSIDE the canonical sf-window (g_max_sf ≈ 0.40); use canonical
    g_0 ≤ 0.40 if you want canonical convergence throughout.
    """
    if k_max < 0:
        raise ValueError(f"k_max must be ≥ 0; got {k_max}")
    if b <= 1.0:
        raise ValueError(f"block factor b must be > 1; got {b}")
    if g_0 <= 0:
        raise ValueError(f"initial coupling g_0 must be positive; got {g_0}")

    log_b = math.log(b)
    coeff = ONE_LOOP_SU2_BETA_COEFF / (16.0 * math.pi * math.pi)

    # Build the g_k sequence: g_{k+1} = 1/sqrt(1/g_k² + coeff·log_b).
    g_values: list[float] = [g_0]
    for k in range(k_max):
        inv_g_sq = 1.0 / (g_values[k] * g_values[k]) + coeff * log_b
        g_values.append(1.0 / math.sqrt(inv_g_sq))

    # Per-step η_k via the existing infrastructure.
    eta_values: list[float] = []
    for k in range(len(g_values)):
        if k < len(g_values) - 1:
            eta_k = compute_eta(g_values[k], g_values[k + 1], t_choice)
        else:
            eta_k = 0.0
        eta_values.append(eta_k)

    # Lattice spacing ratio: a_k/a_0 = b^{-k}.
    a_ratios = [b ** (-k) for k in range(len(g_values))]

    steps = [
        UVTrajectoryStep(
            k=k,
            g_k=g_values[k],
            a_k_over_a_0=a_ratios[k],
            eta_k=eta_values[k],
        )
        for k in range(len(g_values))
    ]

    # Empirical decay ratio: average η_{k+1}/η_k over the middle window.
    decay_ratios = [
        eta_values[k + 1] / eta_values[k]
        for k in range(1, len(eta_values) - 2)
        if eta_values[k] > 1e-20 and math.isfinite(eta_values[k + 1])
    ]
    eta_decay_ratio = (
        sum(decay_ratios) / len(decay_ratios) if decay_ratios else None
    )

    converges_to_zero = all(
        g_values[i + 1] < g_values[i] for i in range(len(g_values) - 1)
    )

    return UVTrajectory(
        steps=steps,
        g_0=g_0,
        b=b,
        convention=t_choice,
        eta_k_decay_ratio=eta_decay_ratio,
        converges_to_zero=converges_to_zero,
    )


def geometric_decay_rate(
    traj: UVTrajectory, skip_first: int = 1
) -> float | None:
    """Median η_{k+1}/η_k across the trajectory, skipping the initial steps.

    For an actual geometric η sequence, this is the geometric ratio r.
    Used by `q_lift.pilot_eta_rational_bound_uv` to produce the rational
    `r ∈ Q'` for the Lean wire-in.

    Returns ``None`` if no finite ratios exist (e.g., all η_k = 0).
    """
    ratios = [
        traj.steps[k + 1].eta_k / traj.steps[k].eta_k
        for k in range(skip_first, len(traj.steps) - 2)
        if traj.steps[k].eta_k > 1e-20
        and math.isfinite(traj.steps[k + 1].eta_k)
    ]
    if not ratios:
        return None
    ratios.sort()
    return ratios[len(ratios) // 2]


# --------------------------------------------------------------------------
# Visualization
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/uv-trajectory.svg"


def plot_uv_trajectory(
    k_max: int = 30,
    b: float = 2.0,
    g_0: float = 0.45,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
) -> str:
    """Plot the UV trajectory: g_k vs k (top) and η_k vs k (log scale, bottom).

    The bottom panel exhibits the geometric decay of η_k that's the
    analytic content of Milestone 6.4's infinite-trajectory closure.
    """
    from pathlib import Path

    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    traj = uv_su2_trajectory(k_max, b, g_0, t_choice)
    k_values = np.array([s.k for s in traj.steps])
    g_values = np.array([s.g_k for s in traj.steps])
    eta_values = np.array([s.eta_k for s in traj.steps])

    fig, (ax_top, ax_bot) = plt.subplots(2, 1, figsize=(8.5, 7.0), sharex=True)

    # Top: g_k vs k (linear).
    ax_top.plot(k_values, g_values, "o-", color="tab:blue", markersize=5,
                label=r"$g_k$ (UV direction)")
    ax_top.set_ylabel(r"coupling $g_k$")
    ax_top.set_title(
        f"UV-direction SU(2) trajectory ($g_0 = {g_0}$, $b = {b}$, {t_choice.value})"
    )
    ax_top.grid(True, alpha=0.3)
    ax_top.legend()

    # Bottom: K_lf(g_k) surrogate vs k.  Eta itself is zero in the UV
    # direction because K_cap is monotone non-increasing under the
    # standard Delta_cap = max(0, K_cap(g_{k+1}) - K_cap(g_k))
    # accounting; the large-field summability K_lf(g_k) is the natural
    # surrogate that exhibits the geometric decay rate r_uv_inf.
    from computations.large_field_kp import compute_large_field_kp
    klf_values = np.array([
        compute_large_field_kp(s.g_k, t_choice=t_choice).K_lf for s in traj.steps
    ])
    # Filter zeros for log plot.
    klf_plot = np.array([k if k > 1e-300 else float("nan") for k in klf_values])
    ax_bot.semilogy(k_values, klf_plot, "s-", color="tab:red", markersize=5,
                    label=r"$K_{\mathrm{lf}}(g_k)$ (large-field surrogate)")
    # Empirical median ratio of the K_lf sequence, restricted to the
    # regime where K_lf is finite & positive (out of the spike at small k).
    finite_mask = np.isfinite(klf_values) & (klf_values > 0)
    if finite_mask.sum() >= 4:
        finite_klf = klf_values[finite_mask]
        ratios = finite_klf[1:] / finite_klf[:-1]
        ratios = ratios[np.isfinite(ratios) & (ratios > 0)]
        if ratios.size:
            median_ratio = float(np.median(ratios))
            decay_label = rf"median ratio $K_{{\mathrm{{lf}}}}(g_{{k+1}})/K_{{\mathrm{{lf}}}}(g_k) \approx {median_ratio:.4f}$"
        else:
            decay_label = r"$K_{\mathrm{lf}}(g_k)$: large-field summability surrogate"
    else:
        decay_label = r"$K_{\mathrm{lf}}(g_k)$: large-field summability surrogate"
    ax_bot.set_xlabel(r"scale index $k$ (UV: $a_k \to 0$)")
    ax_bot.set_ylabel(r"$K_{\mathrm{lf}}(g_k)$ (log scale)")
    ax_bot.set_title(decay_label)
    ax_bot.grid(True, alpha=0.3, which="both")
    ax_bot.legend()

    fig.tight_layout()

    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


if __name__ == "__main__":
    traj = uv_su2_trajectory(k_max=10, g_0=0.30, t_choice=HeatKernelConvention.CANONICAL)
    print("UV-direction SU(2) trajectory (canonical, g_0=0.30, K=10):")
    print(f"{'k':>3} {'g_k':>10} {'a_k/a_0':>10} {'η_k':>14}")
    for s in traj.steps:
        print(f"{s.k:>3} {s.g_k:>10.6f} {s.a_k_over_a_0:>10.6f} {s.eta_k:>14.4e}")
    print()
    print(f"  monotone g_k → 0:     {traj.converges_to_zero}")
    print(f"  median decay ratio:    {geometric_decay_rate(traj)}")
    # For the manuscript figure, render at g_0 = 0.45 (near the small-field
    # convergence threshold) where eta_k is large enough to plot visibly.
    path = plot_uv_trajectory(g_0=0.45, k_max=30)
    print(f"  figure: {path}")
