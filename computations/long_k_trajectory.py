"""Long-K trajectory exploration — empirical geometric decay of η_k.

Manuscript Ch. 10–12 strengthening (2026-05-27): run the UV-direction
SU(2) trajectory at K = 10, 20, 50 (and beyond) and demonstrate
empirically that the per-step σ̂-degradation `η_k` (or its surrogate
`K_lf(g_k+1) − K_lf(g_k)`) decays **geometrically** with k at a rate
matching the one-loop β-function prediction.

# Why this matters for the manuscript

Ch. 10 (σ̂-budget closure) and Ch. 12 (UV-direction trajectory)
currently state the geometric decay of `η_k` as a **structural
claim** derived from the one-loop β-function.  This module converts
that structural claim into an **empirically observed rate**: along
the canonical UV trajectory at `g_0 ∈ [0.30, 0.40]` for K up to 50,
the `K_lf(g_k)` and `η_k` sequences decay geometrically at the rate

    r = exp(− (3 b_0 log b) / (64 π²))

with `b_0 = 22/3` (one-loop SU(2) β-function), `b = 2` (block scale).
For b = 2: r ≈ 0.976 per RG step.

# Why use `K_lf` as the surrogate observable

`compute_eta` in `sigma_hat_trajectory.py` saturates to 0 in the
deep weak-coupling regime because the small Δ_∩ underflows float64
when both K_∩(g_k) and K_∩(g_{k+1}) are essentially 0.  `K_lf(g_k)`
itself ranges from 4.6e-7 at g = 0.20 to 1.44 at g = 0.40, spanning
many orders of magnitude without underflow.  The leading
character-sum form `K_lf = q/(1−q)` with `q = μ_plaq · Z_t` gives
the cleanest geometric-decay signal on the UV trajectory; the η_k
sequence inherits the same decay rate since
`η ≈ c_polymer / A_min · ΔK_∩` and `K_∩ ≈ K_sf + K_lf` with K_sf
nearly constant in this regime.

# What the script delivers

  * `long_k_trajectory(K, g_0, b, t_choice)` — generates the UV
    trajectory at the requested K, returning per-step
    `(g_k, K_sf, K_lf, K_cap, eta_lf_surrogate)` and the empirical
    decay ratio `r_empirical`.
  * `plot_long_k_trajectories(K_values, g_0, ...)` — overlays the
    K_lf(k) and η_k trajectories at K = 10, 20, 50 on a log plot,
    with the analytical decay-rate line for comparison.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from pathlib import Path
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import compute_large_field_kp
from computations.small_field_kp import compute_small_field_kp


# --------------------------------------------------------------------------
# One-loop β-function (SU(2)) + analytical decay-rate prediction
# --------------------------------------------------------------------------


ONE_LOOP_SU2_BETA_COEFF: Final[float] = 22.0 / 3.0
"""One-loop β-function coefficient `b_0 = 11/3 · C_2(adj) = 22/3` for SU(2)."""


def analytical_decay_rate(b: float) -> float:
    """Predicted geometric decay rate `r = exp(−(3 b_0 log b) / (64 π²))`.

    Derived from the leading-asymptotic decay of `K_lf ≈ q/(1−q) ≈ q =
    μ_plaq · Z_t` with `Z_t ≈ 4 exp(−3t/4)` (canonical) for the leading
    spin-1/2 irrep, combined with the AF β-function update
    `t_{k+1} − t_k = (b_0 / (16π²)) log b`.

    For `b = 2` (block scale 2): `r ≈ 0.976` per RG step.
    """
    return math.exp(-(3.0 * ONE_LOOP_SU2_BETA_COEFF * math.log(b)) / (64.0 * math.pi * math.pi))


def uv_g_sequence(g_0: float, K: int, b: float) -> list[float]:
    """Generate the UV-direction coupling sequence: `g_0 > g_1 > ... > g_K`.

    One-loop β-function recursion:
        `1/g_{k+1}²  =  1/g_k²  +  (b_0 / (16π²)) log b`.
    """
    if g_0 <= 0:
        raise ValueError(f"g_0 must be positive; got {g_0}")
    if b <= 1.0:
        raise ValueError(f"block factor b must be > 1; got {b}")
    if K < 0:
        raise ValueError(f"K must be ≥ 0; got {K}")

    coeff = ONE_LOOP_SU2_BETA_COEFF / (16.0 * math.pi * math.pi)
    log_b = math.log(b)
    g_values = [g_0]
    for _ in range(K):
        inv_g_sq = 1.0 / (g_values[-1] ** 2) + coeff * log_b
        g_values.append(1.0 / math.sqrt(inv_g_sq))
    return g_values


# --------------------------------------------------------------------------
# Long-K trajectory dataclasses
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class LongKStep:
    """One step of the long-K trajectory."""

    k: int
    g_k: float
    K_sf: float
    K_lf: float
    K_cap_approx: float  # K_sf + K_lf (upper bound on K_∩)


@dataclass(frozen=True)
class LongKTrajectory:
    """Long-K trajectory with empirical-decay-rate diagnostics."""

    K: int
    g_0: float
    b: float
    convention: HeatKernelConvention
    steps: list[LongKStep]
    K_lf_ratio_median: float | None
    """Median `K_lf(g_{k+1}) / K_lf(g_k)` across the trajectory."""
    K_lf_ratio_mean: float | None
    """Mean `K_lf(g_{k+1}) / K_lf(g_k)` across the trajectory."""
    analytical_ratio: float
    """Predicted ratio `r = exp(−(3 b_0 log b) / (64 π²))`."""

    @property
    def sigma_hat_final(self) -> float:
        """σ̂_K = 1 − Σ η_k with the UV-direction η surrogate.

        Uses η_k = (c_polymer/A_min) · max(0, K_lf(g_k) − K_lf(g_{k+1}))
        = 0.5 · (K_lf(g_k) − K_lf(g_{k+1})) for the UV trajectory
        (where K_lf decreases monotonically).  The 0.5 coupling is the
        derived `c_polymer/A_min = 2/4` from
        `sigma_hat_trajectory.py::DERIVED_ETA_COUPLING`.

        Telescoping bound: Σ η_k ≤ 0.5 · K_lf(0), so σ̂_K ≥ 1 − 0.5·K_lf(0)
        in this surrogate.  At g_0 = 0.40 canonical: K_lf(0) ≈ 1.44,
        bound ≈ 1 − 0.72 = 0.28 (positive, demonstrating the σ̂-budget
        closure even at the long-K boundary)."""
        if len(self.steps) < 2:
            return 1.0
        eta_coupling = 0.5  # c_polymer / A_min = 2/4.
        eta_total = eta_coupling * sum(
            max(0.0, self.steps[i].K_lf - self.steps[i + 1].K_lf)
            for i in range(len(self.steps) - 1)
        )
        return 1.0 - eta_total


def long_k_trajectory(
    K: int,
    g_0: float = 0.40,
    b: float = 2.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> LongKTrajectory:
    """Generate the long-K UV trajectory + compute the empirical decay rate.

    For each k = 0, ..., K, compute `g_k` via the one-loop β-function and
    measure `K_sf(g_k)`, `K_lf(g_k)`, `K_cap(g_k) ≈ K_sf + K_lf`.  Then
    compute the per-step geometric ratio `K_lf(g_{k+1}) / K_lf(g_k)` and
    report the median and mean across the trajectory.

    Default `g_0 = 0.40`: just inside the canonical convergence window
    where K_lf is non-zero and not yet at the boundary.  Lower g_0 gives
    longer trajectory in the deep convergent regime; higher g_0 risks
    hitting the divergence at g_max_lf ≈ 0.42.
    """
    if K < 1:
        raise ValueError(f"K must be ≥ 1; got {K}")

    g_values = uv_g_sequence(g_0, K, b)

    steps: list[LongKStep] = []
    for k, g_k in enumerate(g_values):
        sf = compute_small_field_kp(g_k=g_k, t_choice=t_choice)
        lf = compute_large_field_kp(g_k=g_k, t_choice=t_choice)
        if not math.isfinite(sf.K_sf) or not math.isfinite(lf.K_lf):
            raise RuntimeError(
                f"non-convergent KP at k = {k}, g = {g_k} "
                f"(K_sf = {sf.K_sf}, K_lf = {lf.K_lf}); "
                f"lower g_0 or stay further inside convergent regime"
            )
        steps.append(LongKStep(
            k=k, g_k=g_k,
            K_sf=sf.K_sf, K_lf=lf.K_lf,
            K_cap_approx=sf.K_sf + lf.K_lf,
        ))

    # Empirical decay-rate measurement: K_lf(k+1) / K_lf(k).
    ratios: list[float] = []
    for k in range(len(steps) - 1):
        if steps[k].K_lf > 0 and math.isfinite(steps[k + 1].K_lf):
            ratios.append(steps[k + 1].K_lf / steps[k].K_lf)

    median = (
        sorted(ratios)[len(ratios) // 2] if ratios else None
    )
    mean = (sum(ratios) / len(ratios)) if ratios else None
    analytical = analytical_decay_rate(b)

    return LongKTrajectory(
        K=K, g_0=g_0, b=b, convention=t_choice,
        steps=steps,
        K_lf_ratio_median=median,
        K_lf_ratio_mean=mean,
        analytical_ratio=analytical,
    )


# --------------------------------------------------------------------------
# Plot
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/long-k-trajectory.svg"


def plot_long_k_trajectories(
    K_values: tuple[int, ...] = (10, 20, 50),
    g_0: float = 0.40,
    b: float = 2.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
) -> tuple[str, list[LongKTrajectory]]:
    """Plot K_lf(k) at K = 10, 20, 50 + analytical decay-rate prediction.

    Top panel: K_lf(g_k) vs k on log scale, overlaid for each K.  The
    analytical line `K_lf(0) · r^k` with `r = exp(-(3 b_0 log b) / (64π²))`
    is shown as a dashed reference.

    Bottom panel: σ̂_k = 1 - Σ_{j<k} (K_lf(j) - K_lf(j+1)) — the running
    σ̂ trajectory built from K_lf differences (an upper bound on the
    actual σ̂ trajectory in the regime where K_lf dominates).
    """
    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    target = Path(output_path) if output_path else (
        Path(__file__).resolve().parent.parent / DEFAULT_PLOT_PATH
    )

    trajectories = [
        long_k_trajectory(K=K, g_0=g_0, b=b, t_choice=t_choice)
        for K in K_values
    ]

    fig, (ax_top, ax_bot) = plt.subplots(2, 1, figsize=(9.0, 7.5), sharex=False)

    # ---------- Top: K_lf(k) on log scale ----------
    colors = ["tab:blue", "tab:orange", "tab:red"]
    for traj, color in zip(trajectories, colors[: len(trajectories)]):
        k_arr = np.array([s.k for s in traj.steps])
        K_lf_arr = np.array([s.K_lf for s in traj.steps])
        ax_top.semilogy(
            k_arr, K_lf_arr, "o-", color=color, markersize=4,
            label=f"K = {traj.K}: median r = {traj.K_lf_ratio_median:.4f}"
                  if traj.K_lf_ratio_median else f"K = {traj.K}",
        )

    # Analytical reference: K_lf(g_0) · r^k.
    r_an = analytical_decay_rate(b)
    K_max = max(K_values)
    k_grid = np.arange(0, K_max + 1)
    K_lf_0 = trajectories[0].steps[0].K_lf
    K_lf_analytical = K_lf_0 * (r_an ** k_grid)
    ax_top.semilogy(
        k_grid, K_lf_analytical, "k--", alpha=0.6,
        label=f"analytical: $K_{{lf}}(0) \\cdot r^k$, $r = {r_an:.4f}$",
    )

    ax_top.set_xlabel(r"RG scale index $k$ (UV direction)")
    ax_top.set_ylabel(r"$K_{lf}(g_k)$ (log scale)")
    ax_top.set_title(
        f"Long-K trajectory: $K_{{lf}}$ geometric decay at $g_0 = {g_0}$, "
        f"$b = {b}$ ({t_choice.value})"
    )
    ax_top.grid(True, alpha=0.3, which="both")
    ax_top.legend(loc="best", fontsize=9)

    # ---------- Bottom: σ̂_k running budget at K = max ----------
    longest = trajectories[-1]
    k_arr = np.array([s.k for s in longest.steps])
    eta_coupling = 0.5  # c_polymer / A_min = 2/4.
    sigma_hat = []
    running_eta = 0.0
    for i, s in enumerate(longest.steps):
        if i > 0:
            running_eta += eta_coupling * max(
                0.0, longest.steps[i - 1].K_lf - s.K_lf
            )
        sigma_hat.append(1.0 - running_eta)
    ax_bot.plot(k_arr, sigma_hat, "o-", color="tab:green", markersize=4,
                label=r"$\hat\sigma_k = 1 - 0.5 \cdot \Sigma_{j<k}\max(0, K_{lf}(j) - K_{lf}(j+1))$")
    ax_bot.axhline(y=1.0, color="gray", alpha=0.3, linestyle=":", label=r"$\hat\sigma_0 = 1$")
    ax_bot.axhline(y=0.0, color="red", alpha=0.3, linestyle=":", label=r"positivity")

    final = longest.sigma_hat_final
    ax_bot.annotate(
        f"σ̂_K = {final:.6f}",
        xy=(longest.K, final),
        xytext=(longest.K * 0.55, final + 0.08),
        fontsize=9, color="darkgreen",
        arrowprops=dict(arrowstyle="->", color="darkgreen", alpha=0.5),
    )

    ax_bot.set_xlabel(r"RG scale index $k$")
    ax_bot.set_ylabel(r"running $\hat\sigma_k$")
    ax_bot.set_ylim(min(0.0, min(sigma_hat) - 0.05), 1.05)
    ax_bot.set_title(
        f"Long-K $\\hat\\sigma$ budget closure ($K = {longest.K}$, $g_0 = {g_0}$): "
        f"convergent + stays above 0"
    )
    ax_bot.grid(True, alpha=0.3)
    ax_bot.legend(loc="lower left", fontsize=9)

    fig.tight_layout()
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target), trajectories


# --------------------------------------------------------------------------
# CLI / main
# --------------------------------------------------------------------------


def main() -> None:
    print("Long-K trajectory exploration — empirical geometric decay")
    print()
    K_values = (10, 20, 50)
    g_0 = 0.40
    b = 2.0
    t_choice = HeatKernelConvention.CANONICAL
    path, trajectories = plot_long_k_trajectories(
        K_values=K_values, g_0=g_0, b=b, t_choice=t_choice,
    )
    r_an = analytical_decay_rate(b)
    print(f"Analytical decay rate r = exp(-(3·b_0·log b)/(64π²)) = {r_an:.6f}")
    print()
    print(f"{'K':>4} {'g_K':>10} {'σ̂_K':>14} {'r median':>10} {'r mean':>10} {'r_an':>8}")
    for traj in trajectories:
        median = traj.K_lf_ratio_median if traj.K_lf_ratio_median else float("nan")
        mean = traj.K_lf_ratio_mean if traj.K_lf_ratio_mean else float("nan")
        print(
            f"{traj.K:>4} {traj.steps[-1].g_k:>10.6f} "
            f"{traj.sigma_hat_final:>14.10f} "
            f"{median:>10.6f} {mean:>10.6f} {r_an:>8.4f}"
        )
    print()
    print(f"plot written: {path}")


if __name__ == "__main__":
    main()
