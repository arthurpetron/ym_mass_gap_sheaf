"""UV-direction continuum limit of the renormalized string tension σ̂.

Milestone 7.1 of `work_plan.md`.  Builds on the UV trajectory
(`computations/uv_trajectory.py`, Milestone 6.3) to compute the
continuum-limit string tension

    σ̂_∞  :=  lim_{k → ∞} σ̂_k

where the σ̂-trajectory under the UV-direction RG flow is

    σ̂_{k+1}  =  σ̂_k - η_k,

with `η_k` the per-step σ̂-degradation from `sigma_hat_trajectory.compute_eta`.

# Why σ̂_∞ > 0 is the precursor to the mass gap

The mass-gap theorem (Phase 9) needs `σ̂_∞ > 0` to inject the area-law
bound `⟨W_R(C)⟩ ≤ C · exp(-σ̂_∞ · A(C))` into the continuum gauge
theory.  Here σ̂_∞ is the *limit* of the rational sequence σ̂_k; the
existence of the limit is what Phase 7.1 establishes (computationally
in this module, framework-level in Lean via `SigmaHatLimit.lean`).

# Convergence structure

The σ̂-trajectory satisfies

    σ̂_K  =  σ̂_0 - Σ_{k<K} η_k                 (telescoping)
    σ̂_∞  =  σ̂_0 - Σ_{k=0}^∞ η_k                (taking K → ∞)

Convergence of σ̂_K to a (finite) σ̂_∞ is equivalent to convergence of
the series `Σ_k η_k`.  In the UV direction:

  * (Trivial / empirical) η_k = 0 for all k at the project's current
    Δ_∩ floor (because K_∩ is non-increasing as g_k decreases, hence
    `Δ_∩ = max(0, K_∩(g_next) - K_∩(g)) = 0`).  Then σ̂_∞ = σ̂_0.
  * (Non-trivially-decaying) For a refined Δ_∩ derivation that
    doesn't clip to zero, η_k decays geometrically with rate
    `r ≈ (g_{k+1}/g_k)² ≈ 1 - (b_0/16π²)·log b·g_k²`.  The geometric
    series `Σ_k η_k` converges, and σ̂_∞ = σ̂_0 - Σ_k η_k > 0 iff the
    series sum is less than σ̂_0 (the σ̂-budget closure of Phase 6.4).

This module reports both cases honestly: the UV pilot's σ̂_∞ equals
σ̂_0 = 1.0 exactly, and the non-trivial case can be exercised by
passing a custom η-sequence.

# g_0 dependence (open question per Phase 7.1)

Whether σ̂_∞ is `g_0`-independent in the AF limit (suggesting a
universal continuum string tension) or carries residual `g_0`-dependence
is an open analytic question.  In the trivial UV pilot regime
(η_k ≡ 0), σ̂_∞ = σ̂_0 trivially — no g_0 dependence beyond what
σ̂_0 itself encodes.  The non-trivial case would expose g_0 dependence
through the η_k series sum; this module exposes a helper
``compare_g0_dependence`` to sweep g_0 and observe how σ̂_∞ varies.

# References

- `notes/sigma-hat-derivation.md` §4–§5 (σ̂-trajectory derivation).
- `notes/continuum-limit.md` (this milestone's prose companion).
- `work_plan.md` Milestone 7.1.
- `docs/outline.md` §9 (continuum-limit story for the mass gap).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.uv_trajectory import (
    UVTrajectory,
    geometric_decay_rate,
    uv_su2_trajectory,
)


# --------------------------------------------------------------------------
# Result dataclasses
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SigmaHatLimitStep:
    """One step of the σ̂_k trajectory toward the continuum limit."""

    k: int
    sigma_hat_k: float
    """σ̂_k = σ̂_0 - Σ_{j<k} η_j; monotone non-increasing under η_k ≥ 0."""
    eta_k: float
    """Per-step σ̂-degradation from this scale to the next."""
    distance_to_limit: float
    """|σ̂_k - σ̂_∞_estimate|; how far this partial result is from the limit."""


@dataclass(frozen=True)
class ContinuumLimit:
    """Result of `sigma_hat_uv_limit`: σ̂_∞ estimate + convergence diagnostics."""

    sigma_hat_initial: float
    """The starting σ̂_0."""
    sigma_hat_limit: float
    """The continuum-limit estimate σ̂_∞ (= σ̂_0 - Σ_{k<K} η_k at K = k_max)."""
    is_positive: bool
    """True iff σ̂_∞ > 0 — the make-or-break Phase 7.1 condition."""
    is_monotone_decreasing: bool
    """True iff σ̂_k is monotone non-increasing in k (always true for η_k ≥ 0)."""
    total_eta_consumed: float
    """Σ_{k<K} η_k; equals σ̂_0 - σ̂_∞."""
    geometric_decay_rate: float | None
    """Empirical r_uv = median η_{k+1}/η_k; ``None`` if all η_k = 0."""
    convergence_rate: float | None
    """|σ̂_{k+1} - σ̂_∞| / |σ̂_k - σ̂_∞| (median over middle window); ``None``
    if the trajectory is already at the limit throughout."""
    steps: list[SigmaHatLimitStep]
    g_0: float
    b: float
    convention: HeatKernelConvention


# --------------------------------------------------------------------------
# Computation
# --------------------------------------------------------------------------


def _partial_sigma_hat(
    eta_values: list[float], sigma_hat_initial: float
) -> list[float]:
    """The σ̂_k sequence: σ̂_0, σ̂_0 - η_0, σ̂_0 - η_0 - η_1, ...

    Returns a list of length ``len(eta_values) + 1`` (the initial σ̂_0
    plus one σ̂_{k+1} per η_k transition).
    """
    sigma_hats: list[float] = [sigma_hat_initial]
    sigma = sigma_hat_initial
    for eta in eta_values:
        sigma -= eta
        sigma_hats.append(sigma)
    return sigma_hats


def _convergence_rate(distances: list[float]) -> float | None:
    """Median |σ̂_{k+1} - σ̂_∞| / |σ̂_k - σ̂_∞| over the middle window.

    For an actual geometric convergence this is approximately the
    geometric decay rate r.  ``None`` if no finite ratios exist.
    """
    ratios: list[float] = []
    for k in range(1, len(distances) - 1):
        if distances[k] > 1e-20 and math.isfinite(distances[k + 1]):
            ratios.append(distances[k + 1] / distances[k])
    if not ratios:
        return None
    ratios.sort()
    return ratios[len(ratios) // 2]


def sigma_hat_uv_limit(
    g_0: float = 0.30,
    b: float = 2.0,
    k_max: int = 20,
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    eta_override: list[float] | None = None,
) -> ContinuumLimit:
    """Compute the UV-direction continuum limit σ̂_∞.

    Runs the UV trajectory (`uv_su2_trajectory`) for `k_max` steps,
    extracts the per-step η_k, and integrates the σ̂-recurrence

        σ̂_{k+1}  =  σ̂_k - η_k

    to obtain the σ̂_k sequence and its k → ∞ estimate σ̂_∞ at the
    truncation k = k_max.

    Returns a `ContinuumLimit` with the limit estimate, the positivity
    flag (σ̂_∞ > 0), the monotonicity flag (σ̂_k decreasing), the
    convergence rate, and the per-step trajectory.

    Parameters
    ----------
    g_0
        Initial coupling.  Must be > 0; well inside the convergent
        regime (e.g., g_0 = 0.30 for canonical convention).
    b
        Block factor (> 1).  Must match the UV trajectory convention.
    k_max
        Number of UV-direction RG steps.  Larger k_max gives a tighter
        σ̂_∞ estimate; 20 is sufficient in the AF regime for the
        truncation error to be below floating-point precision.
    sigma_hat_initial
        The starting σ̂_0.  Default 1.0 matches the SU(2) pilot.
    t_choice
        Heat-kernel convention.  Default canonical.
    eta_override
        Optional explicit η-sequence (length ≥ k_max).  When supplied,
        bypasses the UV-trajectory η computation — useful for testing
        the σ̂-recurrence against synthetic geometric sequences and
        for exercising the non-trivially-decaying case.
    """
    if k_max < 1:
        raise ValueError(f"k_max must be ≥ 1; got {k_max}")
    if sigma_hat_initial <= 0:
        raise ValueError(
            f"sigma_hat_initial must be positive; got {sigma_hat_initial}"
        )
    if eta_override is not None and len(eta_override) < k_max:
        raise ValueError(
            f"eta_override must have length ≥ k_max ({k_max}); "
            f"got {len(eta_override)}"
        )

    # Generate η_k either from the UV trajectory or the override.
    traj: UVTrajectory = uv_su2_trajectory(
        k_max=k_max, b=b, g_0=g_0, t_choice=t_choice
    )
    if eta_override is not None:
        eta_values = list(eta_override[:k_max])
    else:
        # Trajectory carries η for steps 0..k_max-1 (last one is 0 by convention).
        eta_values = [s.eta_k for s in traj.steps[:k_max]]

    sigma_hats = _partial_sigma_hat(eta_values, sigma_hat_initial)
    sigma_hat_limit = sigma_hats[-1]
    total_eta = sigma_hat_initial - sigma_hat_limit

    # Monotone-decreasing check (always true when η ≥ 0; explicit for clarity).
    is_monotone_decreasing = all(
        sigma_hats[i + 1] <= sigma_hats[i] for i in range(len(sigma_hats) - 1)
    )

    # Convergence-rate diagnostics.
    distances = [abs(s - sigma_hat_limit) for s in sigma_hats]
    convergence_rate = _convergence_rate(distances)
    decay_rate = geometric_decay_rate(traj) if eta_override is None else None

    # Build per-step records.
    steps = [
        SigmaHatLimitStep(
            k=k,
            sigma_hat_k=sigma_hats[k],
            eta_k=(eta_values[k] if k < len(eta_values) else 0.0),
            distance_to_limit=distances[k],
        )
        for k in range(len(sigma_hats))
    ]

    return ContinuumLimit(
        sigma_hat_initial=sigma_hat_initial,
        sigma_hat_limit=sigma_hat_limit,
        is_positive=sigma_hat_limit > 0.0,
        is_monotone_decreasing=is_monotone_decreasing,
        total_eta_consumed=total_eta,
        geometric_decay_rate=decay_rate,
        convergence_rate=convergence_rate,
        steps=steps,
        g_0=g_0,
        b=b,
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# g_0 dependence sweep
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class G0DependenceRow:
    """One row of `compare_g0_dependence`'s sweep."""

    g_0: float
    sigma_hat_limit: float
    total_eta_consumed: float


def compare_g0_dependence(
    g_0_values: list[float] | None = None,
    b: float = 2.0,
    k_max: int = 20,
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> list[G0DependenceRow]:
    """Sweep σ̂_∞ over a list of initial g_0 values.

    Returns one `G0DependenceRow` per g_0.  If σ̂_∞ is `g_0`-independent
    in the AF limit (suggested by some renormalization-group lore but
    not established in the constructive setting), all rows should report
    the same σ̂_∞ to within floating-point precision.

    In the project's current η_k ≡ 0 regime, σ̂_∞ = σ̂_0 for every g_0,
    so the dependence is identically trivial and the comparison gives
    a degenerate-but-correct g_0-independence answer.
    """
    if g_0_values is None:
        # Restrict to the canonical-convention sf-window (g_max ≈ 0.40);
        # the Wilson convention permits up to ~0.81 — pass an explicit
        # sweep if you want to exercise that range.
        g_0_values = [0.10, 0.20, 0.30, 0.40]
    rows: list[G0DependenceRow] = []
    for g_0 in g_0_values:
        result = sigma_hat_uv_limit(
            g_0=g_0,
            b=b,
            k_max=k_max,
            sigma_hat_initial=sigma_hat_initial,
            t_choice=t_choice,
        )
        rows.append(
            G0DependenceRow(
                g_0=g_0,
                sigma_hat_limit=result.sigma_hat_limit,
                total_eta_consumed=result.total_eta_consumed,
            )
        )
    return rows


# --------------------------------------------------------------------------
# Visualization
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/continuum-limit.svg"


def plot_continuum_limit(
    g_0: float = 0.30,
    b: float = 2.0,
    k_max: int = 20,
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
    eta_override: list[float] | None = None,
) -> str:
    """Plot σ̂_k vs k with σ̂_∞ as a horizontal asymptote.

    Two panels: (top) σ̂_k linear; (bottom) |σ̂_k - σ̂_∞| log-scale
    (exhibits the geometric convergence rate when η_k decays geometrically).
    """
    from pathlib import Path

    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    result = sigma_hat_uv_limit(
        g_0=g_0,
        b=b,
        k_max=k_max,
        sigma_hat_initial=sigma_hat_initial,
        t_choice=t_choice,
        eta_override=eta_override,
    )

    k_values = np.array([s.k for s in result.steps])
    sigma_values = np.array([s.sigma_hat_k for s in result.steps])
    distances = np.array([s.distance_to_limit for s in result.steps])

    fig, (ax_top, ax_bot) = plt.subplots(2, 1, figsize=(8.5, 7.0), sharex=True)

    ax_top.plot(k_values, sigma_values, "o-", color="tab:blue", markersize=5,
                label=r"$\widehat{\sigma}_k$")
    ax_top.axhline(result.sigma_hat_limit, linestyle="--", alpha=0.4,
                   color="tab:green",
                   label=rf"$\widehat{{\sigma}}_\infty \approx {result.sigma_hat_limit:.6g}$")
    ax_top.axhline(0.0, linestyle=":", alpha=0.3, color="gray")
    ax_top.set_ylabel(r"$\widehat{\sigma}_k$")
    ax_top.set_title(
        rf"UV continuum limit: $\widehat{{\sigma}}_\infty > 0$? "
        rf"{result.is_positive} (positive iff σ̂_∞ > 0)"
    )
    ax_top.grid(True, alpha=0.3)
    ax_top.legend()

    # Bottom: |σ̂_k - σ̂_∞| log scale.  Filter zeros for log plot.
    distance_plot = np.array(
        [d if d > 1e-300 else float("nan") for d in distances]
    )
    ax_bot.semilogy(k_values, distance_plot, "s-", color="tab:red",
                    markersize=5, label=r"$|\widehat{\sigma}_k - \widehat{\sigma}_\infty|$")
    rate_label = (
        f"convergence rate ≈ {result.convergence_rate:.4f}"
        if result.convergence_rate is not None
        else "trajectory at limit throughout (η ≡ 0)"
    )
    ax_bot.set_xlabel(r"RG step $k$ (UV direction)")
    ax_bot.set_ylabel(r"distance to limit (log)")
    ax_bot.set_title(rate_label)
    ax_bot.grid(True, alpha=0.3, which="both")
    ax_bot.legend()

    fig.suptitle(
        rf"SU(2) continuum-limit string tension "
        rf"($g_0 = {g_0}$, $b = {b}$, "
        rf"$\widehat{{\sigma}}_0 = {sigma_hat_initial}$, {t_choice.value})"
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
    print("UV-direction continuum limit (canonical, g_0=0.30, k_max=20):")
    result = sigma_hat_uv_limit(g_0=0.30, k_max=20)
    print(f"  σ̂_0               = {result.sigma_hat_initial}")
    print(f"  σ̂_∞ (estimate)   = {result.sigma_hat_limit:.10f}")
    print(f"  Σ η_k consumed    = {result.total_eta_consumed:.6e}")
    print(f"  σ̂_∞ > 0 ?         = {result.is_positive}")
    print(f"  σ̂_k decreasing ?  = {result.is_monotone_decreasing}")
    print(f"  geom decay rate r = {result.geometric_decay_rate}")
    print(f"  convergence rate  = {result.convergence_rate}")
    print()
    print("g_0 dependence (canonical, k_max=20):")
    print(f"{'g_0':>8} {'σ̂_∞':>14} {'Σ η':>14}")
    for row in compare_g0_dependence(k_max=20):
        print(f"{row.g_0:>8.2f} {row.sigma_hat_limit:>14.8f} "
              f"{row.total_eta_consumed:>14.6e}")
    path = plot_continuum_limit(g_0=0.30)
    print(f"\n  figure: {path}")
