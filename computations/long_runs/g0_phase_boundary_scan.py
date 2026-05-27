"""Map the convergent-regime boundary in g_0 at fine resolution.

The manuscript claims the canonical convergent regime is g_0 < g_0^*
with g_0^* ≈ 0.49 (from `notes/large-field-derivation.md` and the
remark in §14.4: "for canonical SU(2) this happens at g_0 ≥ 0.49").
This driver sweeps g_0 ∈ [0.05, 0.498] at fine resolution and runs
the five-criterion pilot validator at each, recording

  * which criterion fails first as g_0 → g_0^*
  * the σ̂_K retention as a function of g_0
  * the empirical g_0^* (largest g_0 where all five pass at K = 5)

across both heat-kernel conventions.  The output is a phase-boundary
chart and a JSON sidecar suitable for the manuscript's Appendix D.

Cost: each pilot is ~1-3 seconds at K = 5; 400 g_0 points × 2 convs
= 800 pilots ≈ 30-60 minutes.

Usage:
    python -m computations.long_runs.g0_phase_boundary_scan
    python -m computations.long_runs.g0_phase_boundary_scan --resolution 200 --K 10
    python -m computations.long_runs.g0_phase_boundary_scan --g0-min 0.40 --g0-max 0.50
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Final

import numpy as np

from computations.heat_kernel import HeatKernelConvention
from computations.pilot_su2 import PILOT_THRESHOLD_SIGMA_RATIO, run_pilot


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/g0-phase-boundary.svg"
DEFAULT_JSON_PATH: Final[str] = "visualizations/pilot/su2/g0-phase-boundary.json"


@dataclass(frozen=True)
class PhaseScanPoint:
    g_0: float
    K: int
    convention: str
    crit_1_small_field_KP: bool
    crit_2_large_field_KP: bool
    crit_3_overlap_KP: bool
    crit_4_delta_cap_summable: bool
    crit_5_sigma_hat_positive_and_budget: bool
    all_five_pass: bool
    threshold_success: bool
    pilot_succeeds: bool
    sigma_hat_final: float
    total_eta: float
    elapsed_seconds: float


def scan_one_convention(
    g_0_grid: np.ndarray,
    K: int,
    convention: HeatKernelConvention,
) -> list[PhaseScanPoint]:
    """Run the pilot at every g_0 in the grid for one convention."""
    points: list[PhaseScanPoint] = []
    for g_0 in g_0_grid:
        t0 = time.time()
        try:
            r = run_pilot(K=K, g_0=float(g_0), t_choice=convention)
            elapsed = time.time() - t0
            sigma_final = r.sigma_hat_final if np.isfinite(r.sigma_hat_final) else float("-inf")
            total_eta = r.total_eta if np.isfinite(r.total_eta) else float("inf")
            points.append(PhaseScanPoint(
                g_0=float(g_0), K=K, convention=convention.value,
                crit_1_small_field_KP=r.crit_1_small_field_KP,
                crit_2_large_field_KP=r.crit_2_large_field_KP,
                crit_3_overlap_KP=r.crit_3_overlap_KP,
                crit_4_delta_cap_summable=r.crit_4_delta_cap_summable,
                crit_5_sigma_hat_positive_and_budget=r.crit_5_sigma_hat_positive_and_budget,
                all_five_pass=r.all_five_pass,
                threshold_success=r.threshold_success,
                pilot_succeeds=r.pilot_succeeds,
                sigma_hat_final=sigma_final,
                total_eta=total_eta,
                elapsed_seconds=elapsed,
            ))
        except (ValueError, RuntimeError, ArithmeticError, ZeroDivisionError, OverflowError):
            elapsed = time.time() - t0
            points.append(PhaseScanPoint(
                g_0=float(g_0), K=K, convention=convention.value,
                crit_1_small_field_KP=False,
                crit_2_large_field_KP=False,
                crit_3_overlap_KP=False,
                crit_4_delta_cap_summable=False,
                crit_5_sigma_hat_positive_and_budget=False,
                all_five_pass=False,
                threshold_success=False,
                pilot_succeeds=False,
                sigma_hat_final=float("-inf"),
                total_eta=float("inf"),
                elapsed_seconds=elapsed,
            ))
    return points


def find_boundary(points: list[PhaseScanPoint]) -> float | None:
    """Largest g_0 where the pilot succeeds (single contiguous regime)."""
    passes = sorted([p.g_0 for p in points if p.pilot_succeeds])
    return passes[-1] if passes else None


def first_failure(points: list[PhaseScanPoint]) -> dict[str, float | None]:
    """For each criterion, find the smallest g_0 at which it fails."""
    out: dict[str, float | None] = {}
    for key in (
        "crit_1_small_field_KP",
        "crit_2_large_field_KP",
        "crit_3_overlap_KP",
        "crit_4_delta_cap_summable",
        "crit_5_sigma_hat_positive_and_budget",
        "threshold_success",
    ):
        fails = sorted([p.g_0 for p in points if not getattr(p, key)])
        out[key] = fails[0] if fails else None
    return out


def plot_phase_boundary(
    by_conv: dict[str, list[PhaseScanPoint]],
    output_path: str | None = None,
) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, axes = plt.subplots(2, 1, figsize=(9.0, 8.0), sharex=True)
    ax_pass, ax_sigma = axes

    colors = {"canonical": "tab:blue", "wilson": "tab:orange"}
    for conv, points in by_conv.items():
        points = sorted(points, key=lambda p: p.g_0)
        g0s = np.array([p.g_0 for p in points])
        passes = np.array([1.0 if p.pilot_succeeds else 0.0 for p in points])
        sigmas = np.array([
            p.sigma_hat_final if np.isfinite(p.sigma_hat_final) and p.sigma_hat_final > -1
            else float("nan")
            for p in points
        ])
        col = colors.get(conv, "tab:gray")
        ax_pass.plot(g0s, passes, "-", color=col, label=conv, linewidth=2.0)
        ax_sigma.plot(g0s, sigmas, "-", color=col, label=conv, linewidth=2.0)
        boundary = find_boundary(points)
        if boundary is not None:
            ax_pass.axvline(boundary, color=col, linestyle=":", alpha=0.7)
            ax_pass.text(boundary, 0.5, f"  $g_0^* = {boundary:.4f}$ ({conv})",
                         color=col, rotation=90, va="center", fontsize=9)

    ax_pass.set_ylabel("pilot succeeds")
    ax_pass.set_ylim(-0.1, 1.1)
    ax_pass.grid(True, alpha=0.3)
    ax_pass.legend(loc="lower left")
    ax_pass.set_title(
        "Convergent-regime boundary: pilot pass/fail as a function of $g_0$"
    )

    ax_sigma.axhline(PILOT_THRESHOLD_SIGMA_RATIO, color="black", linestyle="--",
                     alpha=0.5, label=f"threshold ratio = {PILOT_THRESHOLD_SIGMA_RATIO}")
    ax_sigma.set_xlabel(r"$g_0$ (initial coupling)")
    ax_sigma.set_ylabel(r"$\widehat{\sigma}_K$ retained")
    ax_sigma.grid(True, alpha=0.3)
    ax_sigma.legend(loc="lower left")
    ax_sigma.set_title(r"$\widehat{\sigma}_K$ retention vs $g_0$")

    fig.tight_layout()
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def write_json(
    by_conv: dict[str, list[PhaseScanPoint]],
    boundaries: dict[str, float | None],
    first_fail: dict[str, dict[str, float | None]],
    output_path: str | None = None,
) -> str:
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_JSON_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "boundaries": boundaries,
        "first_failure_g0_per_criterion": first_fail,
        "points": {conv: [asdict(p) for p in pts] for conv, pts in by_conv.items()},
    }
    target.write_text(json.dumps(payload, indent=2))
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="Convergent-regime boundary scan in g_0.")
    p.add_argument("--g0-min", type=float, default=0.05)
    p.add_argument("--g0-max", type=float, default=0.498)
    p.add_argument("--resolution", type=int, default=400,
                   help="number of g_0 sample points (default 400)")
    p.add_argument("--K", type=int, default=5,
                   help="pilot K per point (default 5)")
    p.add_argument("--conventions", nargs="+",
                   default=["canonical", "wilson"],
                   choices=["canonical", "wilson"])
    args = p.parse_args()

    g0_grid = np.linspace(args.g0_min, args.g0_max, args.resolution)
    by_conv: dict[str, list[PhaseScanPoint]] = {}
    for conv_name in args.conventions:
        conv = HeatKernelConvention(conv_name)
        print(f"\n=== scanning {conv.value} convention, K = {args.K}, "
              f"{len(g0_grid)} grid points ===")
        t_start = time.time()
        points = scan_one_convention(g0_grid, args.K, conv)
        elapsed = time.time() - t_start
        n_pass = sum(1 for p in points if p.pilot_succeeds)
        print(f"  done in {elapsed:.1f}s; {n_pass}/{len(points)} pass")
        by_conv[conv.value] = points

    boundaries = {conv: find_boundary(pts) for conv, pts in by_conv.items()}
    first_fail = {conv: first_failure(pts) for conv, pts in by_conv.items()}

    print("\n=== Convergent-regime boundary g_0^* ===")
    for conv, b in boundaries.items():
        print(f"  {conv:>10}:  g_0^* = {b!r}")
    print("\n=== First-failure g_0 per criterion ===")
    for conv, ff in first_fail.items():
        print(f"  {conv}:")
        for k, v in ff.items():
            print(f"    {k:>40}: {v!r}")

    json_path = write_json(by_conv, boundaries, first_fail)
    svg_path = plot_phase_boundary(by_conv)
    print(f"\nJSON: {json_path}\nSVG:  {svg_path}")


if __name__ == "__main__":
    main()
