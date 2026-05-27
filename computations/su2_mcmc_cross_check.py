"""SU(2) lattice MCMC cross-check: scan β and plot ⟨P⟩ vs analytical curves.

Runs the small-lattice MCMC of `su2_mcmc.py` at a grid of bare couplings
`β = 4/g²`, measures the average plaquette `⟨P⟩` at each, and produces
a comparison plot against the strong-coupling and weak-coupling
analytical asymptotic expansions.  The plot is the physics-community-
style evidence anchoring the project's analytical framework: lattice
MCMC reproduces the expected `⟨P⟩(β)` curve, validating the Wilson
action our deterministic pilot operates on.

Output:
  * `visualizations/pilot/su2/mcmc-cross-check.svg` — the comparison plot.

Usage:
    python -m computations.su2_mcmc_cross_check
"""

from __future__ import annotations

import math
from pathlib import Path
from typing import Final

import numpy as np

from computations.su2_mcmc import (
    LatticeConfig,
    MCMCResult,
    run_mcmc,
    strong_coupling_plaquette,
    weak_coupling_plaquette,
)


# --------------------------------------------------------------------------
# Cross-check β grid
# --------------------------------------------------------------------------


# A grid of bare couplings spanning strong → intermediate → weak coupling.
# β = 4/g² for SU(2); g = √(4/β):
#   β = 1.5 → g ≈ 1.63 (deep strong-coupling)
#   β = 2.0 → g ≈ 1.41
#   β = 2.4 → g ≈ 1.29 (Creutz 1980 reference)
#   β = 2.8 → g ≈ 1.20
#   β = 3.2 → g ≈ 1.12 (intermediate)
#   β = 4.0 → g ≈ 1.00
CROSS_CHECK_BETAS: Final[tuple[float, ...]] = (1.5, 2.0, 2.4, 2.8, 3.2, 4.0)


# Pilot operating points (for overlay; far in weak-coupling regime).
# Canonical: g = 0.30 → β = 4 / 0.09 = 44.4
# Wilson:    g = 0.50 → β = 4 / 0.25 = 16.0
CANONICAL_PILOT_BETA: Final[float] = 4.0 / (0.30 ** 2)  # ≈ 44.4
WILSON_PILOT_BETA: Final[float] = 4.0 / (0.50 ** 2)     # = 16.0


DEFAULT_PLOT_PATH: Final[Path] = Path(
    "visualizations/pilot/su2/mcmc-cross-check.svg"
)


# --------------------------------------------------------------------------
# Run the cross-check
# --------------------------------------------------------------------------


def run_cross_check(
    L: int = 8,
    betas: tuple[float, ...] = CROSS_CHECK_BETAS,
    n_thermalization: int = 100,
    n_measurement: int = 200,
    measurement_interval: int = 5,
    seed: int = 42,
) -> list[MCMCResult]:
    """Run the MCMC at each β; return the per-β `MCMCResult` list.

    Defaults: **L=8 lattice** (the user-named lattice size at this
    project's MCMC milestone), 100 thermal + 200 measurement sweeps per
    β (5-sweep interval gives ~40 independent samples per β), seed 42.
    Wall-time at L=8 defaults: ~12 minutes for the full 6-β grid on a
    single CPU core (L=4 was the prior MVP default at ~50s).
    """
    results: list[MCMCResult] = []
    for i, beta in enumerate(betas):
        config = LatticeConfig(L=L, beta=beta)
        res = run_mcmc(
            config,
            n_thermalization=n_thermalization,
            n_measurement=n_measurement,
            measurement_interval=measurement_interval,
            seed=seed + i,  # decorrelate seeds across β values
        )
        results.append(res)
    return results


# --------------------------------------------------------------------------
# Plot generator
# --------------------------------------------------------------------------


def plot_cross_check(
    results: list[MCMCResult],
    output_path: Path | None = None,
) -> Path:
    """Render the cross-check plot to SVG.

    Layout:
      * X-axis: β.
      * Y-axis: ⟨P⟩.
      * MCMC measurements with error bars.
      * Strong-coupling curve `β/4` (dashed).
      * Weak-coupling curve `1 − 3/(4β)` (dashed).
      * Pilot operating points (β_canonical, β_Wilson) indicated as
        vertical lines on the far-right edge.
    """
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    target = output_path if output_path is not None else (
        Path(__file__).resolve().parent.parent / DEFAULT_PLOT_PATH
    )

    fig, ax = plt.subplots(figsize=(8.0, 5.5))

    # MCMC data.
    betas_arr = np.array([r.beta for r in results])
    p_means = np.array([r.plaquette_mean for r in results])
    p_errs = np.array([r.plaquette_stderr for r in results])
    ax.errorbar(
        betas_arr, p_means, yerr=p_errs,
        fmt="o", color="black", markersize=7, capsize=4,
        label=f"MCMC, L = {results[0].L}⁴",
    )

    # Analytical curves.
    beta_grid = np.linspace(0.1, max(max(betas_arr), 6.0), 400)
    ax.plot(
        beta_grid,
        [strong_coupling_plaquette(b) for b in beta_grid],
        linestyle="--", color="tab:blue", alpha=0.7,
        label=r"strong: $\langle P\rangle \approx \beta/4$",
    )
    weak_grid = beta_grid[beta_grid >= 0.8]
    ax.plot(
        weak_grid,
        [weak_coupling_plaquette(b) for b in weak_grid],
        linestyle="--", color="tab:red", alpha=0.7,
        label=r"weak: $\langle P\rangle \approx 1 - 3/(4\beta)$",
    )

    # Pilot operating points — far weak-coupling, off the right edge of
    # MCMC range; indicate via annotation.
    ax.axhline(y=1.0, color="gray", alpha=0.2, linewidth=0.5)

    # Strong → weak crossover band.
    crossover_beta = 2.4
    ax.axvline(x=crossover_beta, color="gray", linestyle=":", alpha=0.4)
    ax.text(
        crossover_beta + 0.04, 0.15,
        "strong → weak crossover\n(literature: β ≈ 2.4)",
        fontsize=8, color="gray", verticalalignment="bottom",
    )

    # Annotate pilot operating points (far right, in the weak-coupling
    # tail where direct MCMC has long autocorrelation times — the regime
    # where the project's analytical framework shines).
    ax.text(
        4.0, 0.97,
        f"pilot operating points:\n  canonical β = {CANONICAL_PILOT_BETA:.1f}\n  Wilson    β = {WILSON_PILOT_BETA:.1f}",
        fontsize=8, color="darkgreen",
        verticalalignment="top",
        bbox=dict(boxstyle="round,pad=0.3", facecolor="lightyellow",
                  edgecolor="darkgreen", alpha=0.7),
    )

    ax.set_xlabel(r"bare coupling $\beta = 4/g^2$", fontsize=11)
    ax.set_ylabel(r"average plaquette $\langle P\rangle = \langle (1/2)\,\mathrm{Re}\,\mathrm{tr}\,U_p\rangle$",
                  fontsize=11)
    ax.set_title(
        "SU(2) lattice MCMC cross-check on the Wilson action\n"
        f"(L = {results[0].L}⁴ lattice, {results[0].n_thermalization} thermal + "
        f"{results[0].n_measurement} measurement sweeps per β)"
    )
    ax.set_xlim(0.0, max(max(betas_arr), 5.0) + 0.5)
    ax.set_ylim(0.0, 1.05)
    ax.grid(True, alpha=0.3)
    ax.legend(loc="lower right", fontsize=9)
    fig.tight_layout()

    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return target


# --------------------------------------------------------------------------
# CLI / main
# --------------------------------------------------------------------------


def main() -> None:
    print("SU(2) lattice MCMC cross-check — running...")
    results = run_cross_check()
    print()
    print(f"{'β':>6}  {'⟨P⟩':>8}  {'± err':>8}  {'accept':>7}  "
          f"{'strong':>8}  {'weak':>8}")
    for r in results:
        sc = strong_coupling_plaquette(r.beta)
        wc = weak_coupling_plaquette(r.beta)
        print(
            f"{r.beta:>6.2f}  {r.plaquette_mean:>8.4f}  "
            f"{r.plaquette_stderr:>8.4f}  {r.acceptance_rate:>7.2%}  "
            f"{sc:>8.4f}  {wc:>8.4f}"
        )
    path = plot_cross_check(results)
    print()
    print(f"plot written: {path}")


if __name__ == "__main__":
    main()
