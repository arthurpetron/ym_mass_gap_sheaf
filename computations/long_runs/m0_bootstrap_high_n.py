"""Appendix D bootstrap at N = 10^6 (vs. the manuscript's headline N = 5000).

The Appendix D headline statement is

    m_0 ≥ X at the 5th percentile across N = 5000 fiducial draws

(`computations.m_0_bootstrap`).  This driver re-runs the same
4-dimensional uniform-sampling experiment at N = 10^6 to tighten the
percentile estimates by ~14× (√(N_new / N_old)), and reports

  * the high-N 5th, 1st, and 0.1st percentile of m_0
  * the bootstrap confidence interval on those percentiles
  * the empirical CDF tail behaviour near the lower bound

Cost: each draw evaluates the constructive m_0 formula (a single
ratio of fiducials, ≪ 1 ms after fiducial state has been mutated).
N = 10^6 ≈ 30-90 minutes depending on the fiducial-perturbation
callback chain.  Memory: 10^6 floats = 8 MB.

Usage:
    python -m computations.long_runs.m0_bootstrap_high_n
    python -m computations.long_runs.m0_bootstrap_high_n --n-samples 10000000 --seed 1
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


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/m0-bootstrap-high-n.svg"
DEFAULT_JSON_PATH: Final[str] = "visualizations/pilot/su2/m0-bootstrap-high-n.json"


@dataclass(frozen=True)
class HighNSummary:
    n_samples: int
    seed: int
    g_0: float
    K: int
    convention: str
    n_failed: int
    mean: float
    median: float
    std: float
    percentile_0_1: float  # 0.1-th
    percentile_1: float    # 1st
    percentile_5: float    # 5th (manuscript headline)
    percentile_50: float   # median
    percentile_95: float
    percentile_99: float
    bca_5_lo: float  # bias-corrected accelerated CI on the 5th pctile
    bca_5_hi: float
    elapsed_seconds: float


def bootstrap_percentile_ci(
    samples: np.ndarray,
    percentile: float,
    n_resamples: int = 1000,
    confidence: float = 0.95,
    rng: np.random.Generator | None = None,
) -> tuple[float, float]:
    """Standard bootstrap CI on a percentile statistic.

    For N = 10^6, each resample is 10^6 draws-with-replacement +
    one np.percentile call (~50 ms), so 1000 resamples ≈ 1 min.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    n = samples.shape[0]
    estimates = np.empty(n_resamples, dtype=np.float64)
    for i in range(n_resamples):
        idx = rng.integers(0, n, size=n)
        estimates[i] = np.percentile(samples[idx], percentile)
    alpha = 1.0 - confidence
    lo = float(np.percentile(estimates, 100 * (alpha / 2)))
    hi = float(np.percentile(estimates, 100 * (1 - alpha / 2)))
    return lo, hi


def run(
    n_samples: int = 1_000_000,
    seed: int = 0,
    g_0: float = 0.30,
    K: int = 3,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    n_ci_resamples: int = 1000,
) -> tuple[HighNSummary, np.ndarray]:
    """Draw once, return the summary AND the valid-sample array.

    Returning the samples lets the caller plot without re-drawing the
    (potentially very expensive) bootstrap a second time.
    """
    print(f"=== high-N m_0 bootstrap: n_samples = {n_samples:,}, seed = {seed} ===")
    t_start = time.time()
    result = run_bootstrap(
        n_samples=n_samples, seed=seed, g_0=g_0, K=K, convention=convention,
    )
    arr = np.asarray(result.m_0_samples, dtype=np.float64)
    valid = arr[np.isfinite(arr) & (arr > 0)]
    print(f"  raw draws: {n_samples:,}   valid: {valid.size:,}   "
          f"failed: {result.n_failed:,}")

    if valid.size == 0:
        raise RuntimeError("no valid m_0 draws — check fiducial envelopes")

    percentiles = np.percentile(valid, [0.1, 1.0, 5.0, 50.0, 95.0, 99.0])
    print(f"  percentile  0.1: {percentiles[0]:.6f}")
    print(f"  percentile  1.0: {percentiles[1]:.6f}")
    print(f"  percentile  5.0: {percentiles[2]:.6f}  <-- manuscript headline")
    print(f"  percentile 50.0: {percentiles[3]:.6f}")
    print(f"  percentile 95.0: {percentiles[4]:.6f}")
    print(f"  percentile 99.0: {percentiles[5]:.6f}")

    print(f"\n  computing bootstrap CI on the 5th percentile "
          f"({n_ci_resamples} resamples)...")
    rng = np.random.default_rng(seed + 1)
    bca_5_lo, bca_5_hi = bootstrap_percentile_ci(
        valid, 5.0, n_resamples=n_ci_resamples, rng=rng,
    )
    print(f"  5th-percentile 95% CI: [{bca_5_lo:.6f}, {bca_5_hi:.6f}]   "
          f"width = {bca_5_hi - bca_5_lo:.6e}")

    return HighNSummary(
        n_samples=n_samples, seed=seed, g_0=g_0, K=K,
        convention=convention.value,
        n_failed=result.n_failed,
        mean=float(valid.mean()),
        median=float(np.median(valid)),
        std=float(valid.std(ddof=1)),
        percentile_0_1=float(percentiles[0]),
        percentile_1=float(percentiles[1]),
        percentile_5=float(percentiles[2]),
        percentile_50=float(percentiles[3]),
        percentile_95=float(percentiles[4]),
        percentile_99=float(percentiles[5]),
        bca_5_lo=bca_5_lo,
        bca_5_hi=bca_5_hi,
        elapsed_seconds=time.time() - t_start,
    ), valid


def plot_tail(
    samples: np.ndarray,
    summary: HighNSummary,
    output_path: str | None = None,
) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, axes = plt.subplots(1, 2, figsize=(11.0, 5.0))
    ax_hist, ax_cdf = axes

    # Histogram of the full m_0 distribution.
    ax_hist.hist(samples, bins=200, color="tab:blue", alpha=0.6, density=True)
    ax_hist.axvline(summary.percentile_5, color="red", linestyle="--",
                    linewidth=1.5, label=f"5th pctile = {summary.percentile_5:.6f}")
    ax_hist.axvline(summary.bca_5_lo, color="red", alpha=0.4, linestyle=":")
    ax_hist.axvline(summary.bca_5_hi, color="red", alpha=0.4, linestyle=":")
    ax_hist.axvline(summary.median, color="black", linewidth=1.0,
                    label=f"median = {summary.median:.6f}")
    ax_hist.set_xlabel(r"$m_0$ (constructive lower bound)")
    ax_hist.set_ylabel("density")
    ax_hist.set_title(rf"$m_0$ distribution, $N = {summary.n_samples:,}$")
    ax_hist.legend(fontsize=9)
    ax_hist.grid(True, alpha=0.3)

    # CDF tail near the low end.
    sorted_samples = np.sort(samples)
    cdf = np.arange(1, len(sorted_samples) + 1) / len(sorted_samples)
    tail_n = min(len(sorted_samples), 50_000)
    ax_cdf.plot(sorted_samples[:tail_n], cdf[:tail_n], color="tab:blue", linewidth=1.5)
    ax_cdf.axvline(summary.percentile_5, color="red", linestyle="--",
                   label=f"5th pctile = {summary.percentile_5:.6f}")
    ax_cdf.axvline(summary.percentile_1, color="orange", linestyle="--",
                   label=f"1st pctile = {summary.percentile_1:.6f}")
    ax_cdf.axvline(summary.percentile_0_1, color="purple", linestyle="--",
                   label=f"0.1th pctile = {summary.percentile_0_1:.6f}")
    ax_cdf.set_xlabel(r"$m_0$ (constructive lower bound)")
    ax_cdf.set_ylabel("CDF")
    ax_cdf.set_title("Empirical CDF — lower tail")
    ax_cdf.grid(True, alpha=0.3)
    ax_cdf.legend(fontsize=9, loc="lower right")

    fig.tight_layout()
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def write_json(summary: HighNSummary, output_path: str | None = None) -> str:
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_JSON_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(asdict(summary), indent=2))
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="High-N m_0 bootstrap (Appendix D extension).")
    p.add_argument("--n-samples", type=int, default=1_000_000)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--g0", type=float, default=0.30)
    p.add_argument("--K", type=int, default=3)
    p.add_argument("--convention", choices=["canonical", "wilson"], default="canonical")
    p.add_argument("--ci-resamples", type=int, default=1000,
                   help="bootstrap CI resamples on the 5th percentile (default 1000)")
    args = p.parse_args()

    conv = HeatKernelConvention(args.convention)
    # Single draw: run() returns both the summary and the valid-sample
    # array, so the empirical-CDF plot reuses the same draw.
    summary, valid = run(
        n_samples=args.n_samples, seed=args.seed, g_0=args.g0, K=args.K,
        convention=conv, n_ci_resamples=args.ci_resamples,
    )
    json_path = write_json(summary)
    svg_path = plot_tail(valid, summary)
    print(f"\nJSON: {json_path}\nSVG:  {svg_path}")
    print(
        f"\n  HEADLINE: m_0 ≥ {summary.percentile_5:.6f} at the 5th percentile, "
        f"95% CI [{summary.bca_5_lo:.6f}, {summary.bca_5_hi:.6f}] "
        f"(N = {summary.n_samples:,})"
    )


if __name__ == "__main__":
    main()
