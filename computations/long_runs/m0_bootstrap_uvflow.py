"""UV-flow robustness: bootstrap m_0 with the operating point g_0 varied.

The Appendix-D bootstrap (`computations/m_0_bootstrap.py`) samples the
four analytic fiducials at the FIXED canonical operating point
g_0 = 0.30.  This driver additionally samples the initial coupling
g_0 jointly with the fiducials, answering the reviewer question "is
the bound robust to the UV-flow operating-point choice, not just to
fiducial uncertainty?"

Two envelopes are reported:
  * a $\pm 0.05$ band around the canonical point, g_0 ~ U[0.25, 0.35],
    which stays comfortably inside the convergent regime; and
  * the full canonical convergent range g_0 ~ U[0.20, 0.40], whose
    upper edge touches the convergent boundary g_0^* ~ 0.40 (where the
    small-field/large-field cluster expansion stops converging), so a
    fraction of draws exit the regime by construction.

The block factor b = 2 and one-loop coefficient b_0 = 22/3 are exact
structural constants of the SU(2) UV flow and are not varied here.

Output:
  * visualizations/pilot/su2/m_0-bootstrap-uvflow.{json,svg}

Usage:
    python -m computations.long_runs.m0_bootstrap_uvflow
    python -m computations.long_runs.m0_bootstrap_uvflow --n-samples 2000000
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
from computations.m_0_bootstrap import run_bootstrap


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/m_0-bootstrap-uvflow.svg"
DEFAULT_JSON_PATH: Final[str] = "visualizations/pilot/su2/m_0-bootstrap-uvflow.json"

# Canonical convergent boundary from the g_0 phase-boundary scan
# (computations/long_runs/g0_phase_boundary_scan.py): the full
# five-criterion pilot exits the convergent regime at g_0^* ~ 0.40.
G0_STAR_CANONICAL: Final[float] = 0.404


@dataclass(frozen=True)
class UVFlowEnvelopeResult:
    label: str
    g_0_low: float
    g_0_high: float
    n_samples: int
    n_failed: int
    frac_failed: float
    mean: float
    median: float
    percentile_1: float
    percentile_5: float
    percentile_50: float
    robust_lower_994: bool  # does the 5th percentile clear 994/1000?


def _summary(label, lo, hi, result) -> tuple[UVFlowEnvelopeResult, np.ndarray, np.ndarray]:
    arr = np.asarray(result.m_0_samples, dtype=np.float64)
    g0 = np.asarray(result.fiducial_samples["g_0"], dtype=np.float64)
    valid = arr[(arr > 0) & np.isfinite(arr)]
    pct = np.percentile(valid, [1.0, 5.0, 50.0]) if valid.size else [np.nan] * 3
    return (
        UVFlowEnvelopeResult(
            label=label, g_0_low=lo, g_0_high=hi,
            n_samples=result.n_samples, n_failed=result.n_failed,
            frac_failed=result.n_failed / result.n_samples,
            mean=float(valid.mean()) if valid.size else float("nan"),
            median=float(pct[2]),
            percentile_1=float(pct[0]),
            percentile_5=float(pct[1]),
            percentile_50=float(pct[2]),
            robust_lower_994=bool(pct[1] >= 0.994),
        ),
        arr, g0,
    )


def run(n_samples: int, seed: int) -> tuple[list[UVFlowEnvelopeResult], dict]:
    conv = HeatKernelConvention.CANONICAL
    envelopes = {
        "band ($\\pm 0.05$): $g_0 \\sim U[0.25, 0.35]$": (0.25, 0.35),
        "full range: $g_0 \\sim U[0.20, 0.40]$": (0.20, 0.40),
    }
    summaries: list[UVFlowEnvelopeResult] = []
    plot_data: dict = {}
    for label, (lo, hi) in envelopes.items():
        print(f"\n=== {label} ===")
        t0 = time.time()
        res = run_bootstrap(
            n_samples=n_samples, seed=seed, K=3, convention=conv,
            g_0_envelope=(lo, hi),
        )
        summ, arr, g0 = _summary(label, lo, hi, res)
        summaries.append(summ)
        plot_data[label] = (arr, g0)
        print(f"  n_failed = {summ.n_failed}/{summ.n_samples} "
              f"({summ.frac_failed*100:.2f}%)   "
              f"5th% = {summ.percentile_5:.6f}   median = {summ.median:.6f}   "
              f"({time.time()-t0:.1f}s)")
    return summaries, plot_data


def plot(summaries, plot_data, output_path: str | None = None) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (ax_sc, ax_hist) = plt.subplots(1, 2, figsize=(11.0, 5.0))

    # Left: m_0 vs g_0 over the full range (subsampled), boundary marked.
    full_label = next(k for k in plot_data if "full range" in k)
    arr, g0 = plot_data[full_label]
    n_plot = min(arr.size, 8000)
    idx = np.random.default_rng(0).choice(arr.size, size=n_plot, replace=False)
    ax_sc.scatter(g0[idx], np.clip(arr[idx], 0, None), s=2, alpha=0.25,
                  color="tab:blue")
    ax_sc.axvline(G0_STAR_CANONICAL, color="red", linestyle="--",
                  label=fr"convergent boundary $g_0^* \approx {G0_STAR_CANONICAL}$")
    ax_sc.axvline(0.30, color="green", linestyle=":", label=r"canonical $g_0 = 0.30$")
    ax_sc.axhline(0.994, color="black", linestyle="-.", linewidth=0.8,
                  label=r"$994/1000$")
    ax_sc.set_xlabel(r"sampled initial coupling $g_0$")
    ax_sc.set_ylabel(r"$m_0$ (constructive lower bound)")
    ax_sc.set_title(r"$m_0$ vs $g_0$ (full convergent range)")
    ax_sc.set_ylim(-0.02, 1.02)
    ax_sc.legend(fontsize=8, loc="lower left")
    ax_sc.grid(True, alpha=0.3)

    # Right: m_0 distribution for the +/-0.05 band.
    band_label = next(k for k in plot_data if "band" in k)
    arr_b, _ = plot_data[band_label]
    valid_b = arr_b[(arr_b > 0) & np.isfinite(arr_b)]
    ax_hist.hist(valid_b, bins=200, color="tab:green", alpha=0.6, density=True)
    band_summ = next(s for s in summaries if "band" in s.label)
    ax_hist.axvline(band_summ.percentile_5, color="red", linestyle="--",
                    label=f"5th pctile = {band_summ.percentile_5:.5f}")
    ax_hist.axvline(0.994, color="black", linestyle="-.", linewidth=0.8,
                    label=r"$994/1000$")
    ax_hist.set_xlabel(r"$m_0$ (constructive lower bound)")
    ax_hist.set_ylabel("density")
    ax_hist.set_title(r"$m_0$ distribution, $g_0 \sim U[0.25, 0.35]$")
    ax_hist.legend(fontsize=8)
    ax_hist.grid(True, alpha=0.3)

    fig.tight_layout()
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def write_json(summaries, output_path: str | None = None) -> str:
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_JSON_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps([asdict(s) for s in summaries], indent=2))
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="UV-flow (g_0) robustness bootstrap.")
    p.add_argument("--n-samples", type=int, default=1_000_000)
    p.add_argument("--seed", type=int, default=0)
    args = p.parse_args()

    summaries, plot_data = run(args.n_samples, args.seed)
    json_path = write_json(summaries)
    svg_path = plot(summaries, plot_data)
    print(f"\nJSON: {json_path}\nSVG:  {svg_path}")
    print("\n=== UV-flow robustness summary ===")
    for s in summaries:
        verdict = "clears" if s.robust_lower_994 else "BELOW"
        print(f"  {s.label}")
        print(f"    failed {s.frac_failed*100:5.2f}%   5th% = {s.percentile_5:.6f} "
              f"({verdict} 994/1000)   median = {s.median:.6f}")


if __name__ == "__main__":
    main()
