"""Verify Theorem 15.3.1 (geometric K_lf decay rate) at K up to 10^5.

The manuscript chapter 15 currently quotes the empirical decay rate
r_uv^{emp} = 0.9762 ± 0.0005 measured at K ∈ {10, 20, 50}, and the
analytical r_uv^∞ ≈ 0.9762 from the b = 2 one-loop β-function.  This
driver pushes the empirical measurement out to K = 10^5 and records
(a) the empirical median / mean ratio, (b) the maximum departure from
the analytical rate across the trajectory, and (c) the partial sum
Σ K_lf as a proxy for the "η-tail bound" of Cor. 15.3.2.

Per-K cost is dominated by `compute_large_field_kp` (a few ms) so a
K = 10^5 run is ~5-15 minutes on a single core; the multi-(g_0, K)
sweep is hours.  Results are JSON-sidecarred to

    visualizations/pilot/su2/uv-decay-ultra-long-k.json

with a companion summary plot.

Usage:
    python -m computations.long_runs.uv_decay_ultra_long_k
    python -m computations.long_runs.uv_decay_ultra_long_k --K 1000000
    python -m computations.long_runs.uv_decay_ultra_long_k --g0 0.40 --K 10000
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import compute_large_field_kp
from computations.long_k_trajectory import analytical_decay_rate, uv_g_sequence


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/uv-decay-ultra-long-k.svg"
DEFAULT_JSON_PATH: Final[str] = "visualizations/pilot/su2/uv-decay-ultra-long-k.json"


@dataclass(frozen=True)
class UltraLongKResult:
    g_0: float
    K: int
    b: float
    convention: str
    analytical_ratio: float
    empirical_median_ratio: float | None
    empirical_mean_ratio: float | None
    empirical_min_ratio: float | None
    empirical_max_ratio: float | None
    max_abs_deviation_from_analytical: float | None
    n_finite_ratios: int
    n_zero_or_underflow: int
    K_lf_partial_sum: float
    final_g_K: float
    elapsed_seconds: float


def run_one(
    g_0: float,
    K: int,
    b: float = 2.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    log_every: int = 0,
) -> UltraLongKResult:
    """One ultra-long-K run at fixed (g_0, K, b).

    Streams through k = 0..K-1, accumulates K_lf and the per-step
    ratio K_lf(g_{k+1}) / K_lf(g_k), and returns aggregate statistics.
    Uses streaming accumulation to avoid storing K floats when K is
    huge.
    """
    t_start = time.time()
    g_values = uv_g_sequence(g_0, K, b)

    klf_prev: float | None = None
    ratio_sum = 0.0
    ratio_sum_sq = 0.0
    ratios_sorted: list[float] = []  # for median (kept compact via downsample)
    ratio_min = math.inf
    ratio_max = -math.inf
    n_finite = 0
    n_zero = 0
    klf_partial_sum = 0.0

    # To estimate the median without storing 10^5+ floats, downsample
    # uniformly to keep at most max_kept ratios.
    max_kept = 50_000
    stride = max(1, K // max_kept)

    for k, g_k in enumerate(g_values):
        klf = compute_large_field_kp(g_k, t_choice=convention).K_lf
        if not math.isfinite(klf) or klf <= 0.0:
            n_zero += 1
            klf_prev = klf if math.isfinite(klf) and klf > 0 else None
            continue
        klf_partial_sum += klf
        if klf_prev is not None and klf_prev > 0.0:
            r = klf / klf_prev
            if math.isfinite(r):
                n_finite += 1
                ratio_sum += r
                ratio_sum_sq += r * r
                if r < ratio_min:
                    ratio_min = r
                if r > ratio_max:
                    ratio_max = r
                if (k % stride) == 0:
                    ratios_sorted.append(r)
        klf_prev = klf
        if log_every and (k % log_every) == 0:
            print(f"  k = {k:>8} / {K}   g_k = {g_k:.6e}   K_lf = {klf:.3e}")

    analytical = analytical_decay_rate(b)
    if n_finite > 0:
        mean_ratio: float | None = ratio_sum / n_finite
        ratios_sorted.sort()
        median_ratio: float | None = ratios_sorted[len(ratios_sorted) // 2] if ratios_sorted else None
        max_dev: float | None = max(
            abs(ratio_min - analytical),
            abs(ratio_max - analytical),
        )
        min_r: float | None = ratio_min
        max_r: float | None = ratio_max
    else:
        mean_ratio = median_ratio = max_dev = min_r = max_r = None

    return UltraLongKResult(
        g_0=g_0,
        K=K,
        b=b,
        convention=convention.value,
        analytical_ratio=analytical,
        empirical_median_ratio=median_ratio,
        empirical_mean_ratio=mean_ratio,
        empirical_min_ratio=min_r,
        empirical_max_ratio=max_r,
        max_abs_deviation_from_analytical=max_dev,
        n_finite_ratios=n_finite,
        n_zero_or_underflow=n_zero,
        K_lf_partial_sum=klf_partial_sum,
        final_g_K=g_values[-1],
        elapsed_seconds=time.time() - t_start,
    )


def run_sweep(
    g_0_grid: tuple[float, ...] = (0.30, 0.35, 0.40, 0.45),
    K_grid: tuple[int, ...] = (1_000, 10_000, 100_000),
    b: float = 2.0,
    log_every: int = 5_000,
) -> list[UltraLongKResult]:
    """Run the (g_0, K) sweep and collect results."""
    results: list[UltraLongKResult] = []
    for g_0 in g_0_grid:
        for K in K_grid:
            print(f"\n=== g_0 = {g_0}, K = {K} ===")
            r = run_one(g_0=g_0, K=K, b=b, log_every=log_every if K >= 10_000 else 0)
            print(
                f"  median r = {r.empirical_median_ratio}  "
                f"analytical = {r.analytical_ratio:.6f}  "
                f"max |Δ| = {r.max_abs_deviation_from_analytical}  "
                f"({r.elapsed_seconds:.1f}s)"
            )
            results.append(r)
    return results


def plot_summary(results: list[UltraLongKResult], output_path: str | None = None) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(8.5, 5.0))

    # Group by g_0; plot median ratio vs K with error bars = (max - min)/2.
    by_g0: dict[float, list[UltraLongKResult]] = {}
    for r in results:
        by_g0.setdefault(r.g_0, []).append(r)

    for g_0, rows in sorted(by_g0.items()):
        rows.sort(key=lambda r: r.K)
        Ks = [r.K for r in rows]
        meds = [r.empirical_median_ratio or float("nan") for r in rows]
        ax.semilogx(Ks, meds, "o-", label=f"$g_0 = {g_0}$", markersize=6)

    if results:
        ax.axhline(results[0].analytical_ratio, color="black", linestyle="--",
                   linewidth=1.0, label=f"analytical $r_{{\\mathrm{{uv}}}}^\\infty = {results[0].analytical_ratio:.4f}$")

    ax.set_xlabel(r"trajectory length $K$")
    ax.set_ylabel(r"empirical median $K_{\mathrm{lf}}(g_{k+1})/K_{\mathrm{lf}}(g_k)$")
    ax.set_title(r"Ultra-long-$K$ verification of Theorem 15.3.1 (geometric $K_{\mathrm{lf}}$ decay)")
    ax.grid(True, alpha=0.3, which="both")
    ax.legend(fontsize=9)
    fig.tight_layout()

    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def write_json(results: list[UltraLongKResult], output_path: str | None = None) -> str:
    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent.parent / DEFAULT_JSON_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps([asdict(r) for r in results], indent=2))
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="Ultra-long-K verification of Theorem 15.3.1.")
    p.add_argument("--g0", type=float, nargs="+", default=[0.30, 0.35, 0.40, 0.45],
                   help="g_0 values to sweep (default: 0.30 0.35 0.40 0.45)")
    p.add_argument("--K", type=int, nargs="+", default=[1_000, 10_000, 100_000],
                   help="K (trajectory length) values to sweep")
    p.add_argument("--b", type=float, default=2.0, help="Block factor b (default 2)")
    args = p.parse_args()

    results = run_sweep(
        g_0_grid=tuple(args.g0), K_grid=tuple(args.K), b=args.b,
    )
    json_path = write_json(results)
    svg_path = plot_summary(results)
    print(f"\nJSON: {json_path}\nSVG:  {svg_path}")

    # Headline pass/fail at the largest K, smallest g_0 (the strictest test).
    by_g0_then_K = sorted(results, key=lambda r: (r.g_0, -r.K))
    if by_g0_then_K:
        toughest = by_g0_then_K[0]
        analytical = toughest.analytical_ratio
        dev = toughest.max_abs_deviation_from_analytical
        if dev is not None and dev < 0.01:
            print(
                f"\n  HEADLINE: at g_0 = {toughest.g_0}, K = {toughest.K}, "
                f"max |empirical − analytical| = {dev:.4f} "
                f"({dev / analytical * 100:.2f}% of {analytical:.4f}) — "
                f"PASSES the 1% deviation criterion."
            )
        else:
            print(
                f"\n  HEADLINE: at g_0 = {toughest.g_0}, K = {toughest.K}, "
                f"max |empirical − analytical| = {dev} — exceeds 1% criterion."
            )


if __name__ == "__main__":
    main()
