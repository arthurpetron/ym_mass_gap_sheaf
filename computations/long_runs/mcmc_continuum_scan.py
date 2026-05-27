"""SU(2) Wilson-action MCMC at 8^4 and 12^4 across a wider β grid.

The fast `computations.su2_mcmc_cross_check` runs at 4^4 with 50+50
sweeps as a smoke-test of the strong-to-weak crossover.  This driver
runs the SAME observable (average plaquette ⟨P⟩) at production-grade
lattice sizes (8^4, 12^4) with longer thermalization (500 + 500
sweeps, measurement every 5) across a denser β grid, including the
crossover region (β ∈ [2.0, 3.2]) that the manuscript's deterministic
σ̂-pilot reaches indirectly via the Wilson convention.

For each (β, L), we report ⟨P⟩ ± stderr and compare to the two
analytical expansions (strong-coupling β/4, weak-coupling 1 − 3/4β).
Continuum extrapolation is performed by linear regression in 1/L at
fixed β, giving ⟨P⟩(β; L → ∞) with a fit-quality diagnostic.

Cost: each 12^4 MCMC at 1000 sweeps ≈ 5-15 minutes single-core; a
6-β × 2-L scan ≈ 1-3 hours.  Memory: bounded by lattice (∼800 KB
at 12^4).

Usage:
    python -m computations.long_runs.mcmc_continuum_scan
    python -m computations.long_runs.mcmc_continuum_scan --L 8 12 16 --betas 1.5 2.0 2.4 2.8 3.2 4.0
    python -m computations.long_runs.mcmc_continuum_scan --sweeps 2000
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Final

import numpy as np

from computations.su2_mcmc import (
    LatticeConfig,
    run_mcmc,
    strong_coupling_plaquette,
    weak_coupling_plaquette,
)


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/mcmc-continuum-scan.svg"
DEFAULT_JSON_PATH: Final[str] = "visualizations/pilot/su2/mcmc-continuum-scan.json"


@dataclass(frozen=True)
class MCMCContinuumPoint:
    beta: float
    L: int
    n_thermalization: int
    n_measurement: int
    measurement_interval: int
    plaquette_mean: float
    plaquette_stderr: float
    acceptance_rate: float
    strong_coupling_reference: float
    weak_coupling_reference: float
    elapsed_seconds: float


@dataclass(frozen=True)
class ContinuumExtrapolation:
    beta: float
    L_values: tuple[int, ...]
    plaquette_at_L: tuple[float, ...]
    plaquette_stderr_at_L: tuple[float, ...]
    plaquette_continuum: float
    plaquette_continuum_stderr: float
    fit_intercept: float
    fit_slope: float
    fit_r_squared: float


def run_one_point(
    beta: float,
    L: int,
    n_thermalization: int = 500,
    n_measurement: int = 500,
    measurement_interval: int = 5,
    seed: int = 42,
) -> MCMCContinuumPoint:
    t0 = time.time()
    cfg = LatticeConfig(L=L, beta=beta)
    res = run_mcmc(
        config=cfg,
        n_thermalization=n_thermalization,
        n_measurement=n_measurement,
        measurement_interval=measurement_interval,
        seed=seed,
    )
    return MCMCContinuumPoint(
        beta=beta, L=L,
        n_thermalization=n_thermalization,
        n_measurement=n_measurement,
        measurement_interval=measurement_interval,
        plaquette_mean=res.plaquette_mean,
        plaquette_stderr=res.plaquette_stderr,
        acceptance_rate=res.acceptance_rate,
        strong_coupling_reference=strong_coupling_plaquette(beta),
        weak_coupling_reference=weak_coupling_plaquette(beta),
        elapsed_seconds=time.time() - t0,
    )


def extrapolate_continuum(
    points: list[MCMCContinuumPoint],
) -> ContinuumExtrapolation:
    """Linear regression: ⟨P⟩(L) = a + b / L."""
    L = np.array([p.L for p in points], dtype=np.float64)
    P = np.array([p.plaquette_mean for p in points], dtype=np.float64)
    sigma = np.array([p.plaquette_stderr for p in points], dtype=np.float64)
    weights = 1.0 / np.where(sigma > 0, sigma**2, 1e-12)
    x = 1.0 / L
    # Weighted linear regression.
    W = np.diag(weights)
    X = np.column_stack([np.ones_like(x), x])
    XtWX = X.T @ W @ X
    XtWy = X.T @ W @ P
    beta_hat = np.linalg.solve(XtWX, XtWy)
    a, b = float(beta_hat[0]), float(beta_hat[1])
    residuals = P - (a + b * x)
    ss_res = float(np.sum(weights * residuals**2))
    ss_tot = float(np.sum(weights * (P - np.average(P, weights=weights))**2))
    r_sq = 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0
    cov = np.linalg.inv(XtWX)
    intercept_stderr = float(np.sqrt(cov[0, 0]))
    return ContinuumExtrapolation(
        beta=points[0].beta,
        L_values=tuple(int(L_) for L_ in L),
        plaquette_at_L=tuple(float(p) for p in P),
        plaquette_stderr_at_L=tuple(float(s) for s in sigma),
        plaquette_continuum=a,
        plaquette_continuum_stderr=intercept_stderr,
        fit_intercept=a,
        fit_slope=b,
        fit_r_squared=r_sq,
    )


def run_scan(
    betas: tuple[float, ...],
    L_values: tuple[int, ...],
    n_thermalization: int,
    n_measurement: int,
    measurement_interval: int,
    seed_base: int,
) -> tuple[list[MCMCContinuumPoint], list[ContinuumExtrapolation]]:
    all_points: list[MCMCContinuumPoint] = []
    extrapolations: list[ContinuumExtrapolation] = []
    for beta in betas:
        beta_points: list[MCMCContinuumPoint] = []
        for L in L_values:
            seed = seed_base + 1000 * int(round(beta * 10)) + L
            print(f"  β = {beta:.2f}, L = {L}  ", end="", flush=True)
            p = run_one_point(
                beta=beta, L=L,
                n_thermalization=n_thermalization,
                n_measurement=n_measurement,
                measurement_interval=measurement_interval,
                seed=seed,
            )
            print(
                f"⟨P⟩ = {p.plaquette_mean:.6f} ± {p.plaquette_stderr:.6f}   "
                f"accept = {p.acceptance_rate:.2f}   ({p.elapsed_seconds:.1f}s)"
            )
            beta_points.append(p)
        all_points.extend(beta_points)
        if len(beta_points) >= 2:
            extrap = extrapolate_continuum(beta_points)
            print(f"    L → ∞ extrapolation: ⟨P⟩∞ = "
                  f"{extrap.plaquette_continuum:.6f} ± "
                  f"{extrap.plaquette_continuum_stderr:.6f}   "
                  f"R² = {extrap.fit_r_squared:.4f}")
            extrapolations.append(extrap)
    return all_points, extrapolations


def plot_scan(
    points: list[MCMCContinuumPoint],
    extrapolations: list[ContinuumExtrapolation],
    output_path: str | None = None,
) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(9.0, 6.0))

    by_L: dict[int, list[MCMCContinuumPoint]] = {}
    for p in points:
        by_L.setdefault(p.L, []).append(p)

    markers = {4: "o", 6: "s", 8: "^", 12: "d", 16: "x"}
    for L, pts in sorted(by_L.items()):
        pts.sort(key=lambda p: p.beta)
        betas = [p.beta for p in pts]
        means = [p.plaquette_mean for p in pts]
        errs = [p.plaquette_stderr for p in pts]
        ax.errorbar(betas, means, yerr=errs, marker=markers.get(L, "o"),
                    capsize=3, label=fr"$L = {L}$", markersize=6, linewidth=1.2)

    if extrapolations:
        extrapolations_sorted = sorted(extrapolations, key=lambda e: e.beta)
        betas_inf = [e.beta for e in extrapolations_sorted]
        means_inf = [e.plaquette_continuum for e in extrapolations_sorted]
        errs_inf = [e.plaquette_continuum_stderr for e in extrapolations_sorted]
        ax.errorbar(betas_inf, means_inf, yerr=errs_inf, marker="*",
                    capsize=4, label=r"$L \to \infty$ extrapolation",
                    color="black", linewidth=2.0, markersize=12)

    # Analytical reference curves.
    beta_dense = np.linspace(
        min(p.beta for p in points), max(p.beta for p in points), 200,
    )
    ax.plot(beta_dense, [strong_coupling_plaquette(b) for b in beta_dense],
            "--", color="gray", alpha=0.7, label=r"strong-coupling $\beta/4$")
    ax.plot(beta_dense, [weak_coupling_plaquette(b) for b in beta_dense],
            "--", color="darkred", alpha=0.7, label=r"weak-coupling $1 - 3/(4\beta)$")

    ax.set_xlabel(r"$\beta = 4/g^2$")
    ax.set_ylabel(r"$\langle P \rangle$ (average plaquette)")
    ax.set_title(
        r"SU(2) Wilson-action MCMC across $L \in \{$"
        + ", ".join(str(L) for L in sorted(by_L))
        + r"$\}$ with continuum extrapolation"
    )
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=9)
    fig.tight_layout()

    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def write_json(
    points: list[MCMCContinuumPoint],
    extrapolations: list[ContinuumExtrapolation],
    output_path: str | None = None,
) -> str:
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_JSON_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "points": [asdict(p) for p in points],
        "continuum_extrapolations": [asdict(e) for e in extrapolations],
    }
    target.write_text(json.dumps(payload, indent=2, default=lambda x: list(x) if isinstance(x, tuple) else x))
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="Multi-L SU(2) MCMC continuum scan.")
    p.add_argument("--betas", type=float, nargs="+",
                   default=[1.5, 2.0, 2.4, 2.8, 3.2, 4.0])
    p.add_argument("--L", type=int, nargs="+", default=[8, 12],
                   help="lattice sizes (default 8 12; add 16 for ~4x cost)")
    p.add_argument("--sweeps", type=int, default=500,
                   help="thermalization sweeps; measurement uses the same count")
    p.add_argument("--interval", type=int, default=5,
                   help="measurement interval (auto-decorrelation, default 5)")
    p.add_argument("--seed", type=int, default=42)
    args = p.parse_args()

    print(
        f"\n=== MCMC continuum scan ===\n"
        f"  β: {args.betas}\n"
        f"  L: {args.L}\n"
        f"  sweeps: {args.sweeps} thermal + {args.sweeps} measure (every {args.interval})\n"
        f"  total runs: {len(args.betas) * len(args.L)}\n"
    )
    t_start = time.time()
    points, extrapolations = run_scan(
        betas=tuple(args.betas), L_values=tuple(args.L),
        n_thermalization=args.sweeps, n_measurement=args.sweeps,
        measurement_interval=args.interval, seed_base=args.seed,
    )
    print(f"\n  total elapsed: {time.time() - t_start:.1f}s")

    json_path = write_json(points, extrapolations)
    svg_path = plot_scan(points, extrapolations)
    print(f"\nJSON: {json_path}\nSVG:  {svg_path}")

    if extrapolations:
        print("\n=== Continuum-extrapolated ⟨P⟩∞(β) ===")
        for e in extrapolations:
            print(
                f"  β = {e.beta:.2f}:  ⟨P⟩∞ = {e.plaquette_continuum:.6f} ± "
                f"{e.plaquette_continuum_stderr:.6f}   R² = {e.fit_r_squared:.4f}"
            )


if __name__ == "__main__":
    main()
