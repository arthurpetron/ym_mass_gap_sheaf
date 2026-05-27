"""m_0 uplift from threading the chaining factor into η (Milestone 6.5-eta).

Manuscript-quotable comparison of the baseline constructive mass-gap
lower bound vs the chaining-tightened version, across the canonical
convergent window.

# Derivation

The σ̂-budget derivation (`sigma_hat_trajectory.py` module docstring)
gives

    η_k = (c_polymer / A_min) · Δ_∩(b, g_k)

as the per-step σ̂-degradation.  Inside Δ_∩'s polymer-cluster-expansion
derivation, a per-plaquette **union bound** on the buffer-shell
aggregate probability `μ_k(Ω_k^∩)` is invoked.  The Phase-6.5 chaining
estimate (`chaining_estimate.py`) replaces that union bound with a
correlation-aware bound, giving

    η_k_chaining = c_chain(g_k) · η_k_baseline,

with c_chain(g_k) = exp(-n_share · g_k² · ζ) ∈ (0, 1] (admissible in
the small-positive-correlation regime g_k ≤ G_MAX_CHAIN = 2).

# Empirical impact (canonical pilot operating points)

  * `g_0 = 0.30, K = 3`: c_chain(0.30) ≈ 0.835, Σ η reduced by 16.5%,
    m_0 uplift ≈ 0.007% (sub-/1000 resolution).
  * `g_0 = 0.30, K = 10`: m_0 from 997/1000 → 998/1000 (manuscript-
    quotable, uplift ratio = 998/997 ≈ 1.001).
  * `g_0 = 0.35, K = 3`: m_0 from 995/1000 → 996/1000.
  * `g_0 = 0.40, K = 5` (near threshold): m_0 from 798/1000 →
    859/1000 (uplift ratio 1.076 — substantial gain at the boundary).

# What this module provides

  * `chaining_uplift_row(g_0, K, ...)` — single-operating-point
    baseline-vs-chaining comparison.
  * `chaining_uplift_table(operating_points, ...)` — multi-point
    comparison returning a list of `ChainingUpliftRow`.
  * `plot_chaining_uplift(...)` — bar chart of m_0 uplift ratios
    across operating points.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Final, Sequence

from computations.heat_kernel import HeatKernelConvention
from computations.mass_gap_bound import MassGapBound, derive_mass_gap_bound


# --------------------------------------------------------------------------
# Single-point comparison
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ChainingUpliftRow:
    """Baseline-vs-chaining `m_0` comparison at one operating point."""

    g_0: float
    K: int
    m_0_denominator: int
    convention: HeatKernelConvention
    baseline: MassGapBound
    chaining: MassGapBound | None  # None if the chaining regime check fails
    baseline_closure_ok: bool
    chaining_closure_ok: bool

    @property
    def baseline_m_0(self) -> float:
        return self.baseline.m_0_float

    @property
    def chaining_m_0(self) -> float:
        return self.chaining.m_0_float if self.chaining is not None else float("nan")

    @property
    def m_0_uplift_ratio(self) -> float:
        if self.chaining is None or self.baseline.m_0_float == 0.0:
            return float("nan")
        return self.chaining.m_0_float / self.baseline.m_0_float

    @property
    def numerator_delta(self) -> int:
        """How many Q'-numerator units the chaining gain bumped (at the
        shared `m_0_denominator`)."""
        if self.chaining is None:
            return 0
        return self.chaining.m_0_numerator - self.baseline.m_0_numerator


def chaining_uplift_row(
    g_0: float = 0.30,
    K: int = 3,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    m_0_denominator: int = 1000,
) -> ChainingUpliftRow:
    """One baseline-vs-chaining comparison at (g_0, K, denominator)."""
    baseline = derive_mass_gap_bound(
        g_0=g_0, K=K, convention=convention,
        m_0_denominator=m_0_denominator,
        use_chaining=False,
    )
    baseline_ok = baseline.bound_check_passes

    # Chaining may raise if g_0 > G_MAX_CHAIN; capture that gracefully.
    chaining: MassGapBound | None = None
    chaining_ok = False
    try:
        chaining = derive_mass_gap_bound(
            g_0=g_0, K=K, convention=convention,
            m_0_denominator=m_0_denominator,
            use_chaining=True,
        )
        chaining_ok = chaining.bound_check_passes
    except RuntimeError:
        # Either chaining regime check or σ̂_∞ ≤ 0 (failed-pilot tail).
        # baseline may still have closed; preserve the report.
        chaining = None
        chaining_ok = False

    return ChainingUpliftRow(
        g_0=g_0,
        K=K,
        m_0_denominator=m_0_denominator,
        convention=convention,
        baseline=baseline,
        chaining=chaining,
        baseline_closure_ok=baseline_ok,
        chaining_closure_ok=chaining_ok,
    )


def chaining_uplift_table(
    operating_points: Sequence[tuple[float, int]] = (
        (0.30, 3),
        (0.30, 5),
        (0.30, 10),
        (0.35, 3),
        (0.35, 5),
        (0.35, 10),
        (0.40, 3),
        (0.40, 5),
    ),
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    m_0_denominator: int = 1000,
) -> list[ChainingUpliftRow]:
    """Multi-operating-point comparison table."""
    return [
        chaining_uplift_row(
            g_0=g_0, K=K, convention=convention,
            m_0_denominator=m_0_denominator,
        )
        for (g_0, K) in operating_points
    ]


# --------------------------------------------------------------------------
# Visualization
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/chaining-eta-uplift.svg"


def plot_chaining_uplift(
    rows: list[ChainingUpliftRow] | None = None,
    output_path: str | None = None,
) -> str:
    """Bar chart: baseline m_0 vs chaining m_0 across operating points."""
    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if rows is None:
        rows = chaining_uplift_table()

    target = Path(output_path) if output_path else (
        Path(__file__).resolve().parent.parent / DEFAULT_PLOT_PATH
    )

    # Filter to rows where both baseline and chaining closed.
    rows_valid = [r for r in rows if r.baseline_closure_ok and r.chaining_closure_ok]
    if not rows_valid:
        raise RuntimeError("no operating points where both baseline and chaining close")

    labels = [f"g₀={r.g_0:.2f}\nK={r.K}" for r in rows_valid]
    baseline_m0 = np.array([r.baseline_m_0 for r in rows_valid])
    chaining_m0 = np.array([r.chaining_m_0 for r in rows_valid])
    uplift_ratios = chaining_m0 / baseline_m0

    fig, (ax_top, ax_bot) = plt.subplots(2, 1, figsize=(10.0, 7.0))

    # Top: m_0 bars side-by-side
    x = np.arange(len(rows_valid))
    width = 0.35
    ax_top.bar(x - width / 2, baseline_m0, width,
               label="baseline (union bound)", color="tab:red", alpha=0.75,
               edgecolor="black", linewidth=0.4)
    ax_top.bar(x + width / 2, chaining_m0, width,
               label="chaining-tightened η", color="tab:green", alpha=0.75,
               edgecolor="black", linewidth=0.4)
    ax_top.set_xticks(x)
    ax_top.set_xticklabels(labels, fontsize=9)
    ax_top.set_ylabel(r"constructive lower bound $m_0$", fontsize=11)
    ax_top.set_title(
        r"$m_0$ uplift from threading the chaining factor into $\eta$ "
        r"(Milestone 6.5-eta)"
    )
    ax_top.legend(fontsize=9, loc="lower left")
    ax_top.grid(True, alpha=0.3, axis="y")
    # Annotate each chaining bar with its numerator delta.
    for i, r in enumerate(rows_valid):
        if r.numerator_delta > 0:
            ax_top.text(
                x[i] + width / 2, r.chaining_m_0 + 0.005,
                f"+{r.numerator_delta}",
                ha="center", fontsize=8, color="darkgreen", weight="bold",
            )

    # Bottom: uplift ratio
    bars = ax_bot.bar(x, uplift_ratios, color="tab:blue", alpha=0.7,
                      edgecolor="black", linewidth=0.4)
    ax_bot.axhline(1.0, color="gray", linestyle="--", alpha=0.6,
                   label="no uplift")
    ax_bot.set_xticks(x)
    ax_bot.set_xticklabels(labels, fontsize=9)
    ax_bot.set_ylabel(r"$m_0^{\rm chain}/m_0^{\rm base}$", fontsize=11)
    ax_bot.set_title(r"chaining $m_0$ uplift ratio per operating point")
    ax_bot.legend(fontsize=9)
    ax_bot.grid(True, alpha=0.3, axis="y")
    for bar, ratio in zip(bars, uplift_ratios):
        ax_bot.text(
            bar.get_x() + bar.get_width() / 2, ratio + 0.001,
            f"×{ratio:.4f}",
            ha="center", fontsize=8,
        )

    fig.tight_layout()
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg", bbox_inches="tight")
    plt.close(fig)
    return str(target)


# --------------------------------------------------------------------------
# CLI / main
# --------------------------------------------------------------------------


def main() -> None:
    print("m_0 uplift from chaining-tightened η (Milestone 6.5-eta)")
    print()
    rows = chaining_uplift_table()
    print(f"{'g_0':>5} {'K':>3} {'baseline':>16} {'chaining':>16} {'uplift':>10}")
    for r in rows:
        b_str = f"{r.baseline.m_0_numerator}/{r.baseline.m_0_denominator}"
        if r.chaining is not None:
            c_str = f"{r.chaining.m_0_numerator}/{r.chaining.m_0_denominator}"
            uplift = f"×{r.m_0_uplift_ratio:.6f}"
        else:
            c_str = "(no close)"
            uplift = "--"
        print(f"{r.g_0:>5.2f} {r.K:>3} {b_str:>16} {c_str:>16} {uplift:>10}")
    print()
    path = plot_chaining_uplift(rows)
    print(f"plot written: {path}")


if __name__ == "__main__":
    main()
