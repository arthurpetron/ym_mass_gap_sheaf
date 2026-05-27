"""m_0 fiducial-sensitivity tornado plot — manuscript Appendix D visual.

Manuscript Appendix D upgrade (2026-05-27): replace one of the
planned fiducial-sensitivity tables with a **tornado chart** showing
m_0's sensitivity to ±20% perturbation of each fiducial, sorted by
magnitude.

# Why a tornado plot

A tornado chart is the most visually compelling robustness statement
the manuscript can produce: at a glance, the reader sees which
fiducials dominate the m_0 lower bound and which are essentially
irrelevant.  The chart anchors the project's claim that "m_0 is
robust against ±20% perturbation of every named fiducial" with a
single figure.

# Fiducials swept

Per `notes/fiducials_notes.md` §§1–4, the project's named fiducials
are:

  * `BAŁABAN_SPECTRAL_GAP_COEFF` (c_λ): post-2026-05-26 derived from
    the SU(2) Casimir gap (3/4); previously fiducial at 1/2.
  * `MU_PLAQUETTE_4D` (μ_plaq): literature-shape (Seiler 1982); 16.
  * `BALABAN_POLYMER_RESIDUAL` (c_polymer): derived as 2 (from
    boundary-channel counting).
  * `WILSON_LOOP_MIN_AREA_DIMENSIONLESS` (A_min): derived as 4
    (outline §7.1 minimum loop area).

Each is swept at ±20% from baseline; m_0 is computed at each
perturbation and the tornado bars are sorted by sensitivity
magnitude (most sensitive at top).

# What m_0 represents in this plot

m_0 (dimensionless) is the constructive mass-gap lower bound
`m_0 = sqrt(σ̂_∞) = sqrt(σ̂_0 - Σ η_k)` derived from the σ̂-budget
closure.  Under the project's normalization σ̂_0 = 1, m_0 ranges
in [0, 1].  Baseline value (canonical pilot, g_0 = 0.30, K = 3,
post-c_λ Casimir-gap upgrade): m_0 ≈ 0.9996 (= sqrt(0.9991)).

A fiducial perturbation that pushes m_0 close to 0 indicates HIGH
sensitivity; a perturbation that leaves m_0 essentially unchanged
indicates LOW sensitivity.

# Output

`visualizations/pilot/su2/m_0-tornado.svg` — the tornado chart.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Final

from computations.heat_kernel import HeatKernelConvention
from computations.overlap_measure import standard_su2_trajectory
from computations.sigma_hat_trajectory import sigma_hat_trajectory
from computations.small_field_kp import BAŁABAN_SPECTRAL_GAP_COEFF
from computations.large_field_kp import MU_PLAQUETTE_4D


# --------------------------------------------------------------------------
# m_0 from fiducial values
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class FiducialEntry:
    """One named fiducial + its baseline + override key."""

    display_name: str
    baseline: float
    perturbation_callback: Callable[[float, dict[str, float | None]], dict[str, float | None]]
    """Updates the kwargs dict to set this fiducial to a perturbed value."""


def _m_0_from_kwargs(
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 1.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    *,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float | None = None,
    polymer_residual: float | None = None,
    wilson_loop_min_area: int | None = None,
) -> float:
    """Compute m_0 (dimensionless) under the given fiducial overrides.

    Pipeline:
      1. Run sigma_hat_trajectory at the perturbed fiducials.
      2. Extract σ̂_∞ = σ̂_0 - total_eta.
      3. Return m_0 = sqrt(σ̂_∞) clamped at 0 (negative σ̂_∞ → bound vacuous).

    Returns 0.0 if the pilot fails (non-convergent regime).
    """
    g_traj = standard_su2_trajectory(k_max=K, g_0=g_0)[0]
    kwargs: dict[str, float | None] = {
        "sigma_hat_initial": sigma_hat_initial,
        "t_choice": convention,
        "spectral_gap_coeff": spectral_gap_coeff,
        "polymer_residual": polymer_residual,
        "wilson_loop_min_area": wilson_loop_min_area,
    }
    if mu_plaq is not None:
        kwargs["mu_plaq"] = mu_plaq
    try:
        res = sigma_hat_trajectory(g_traj, **{k: v for k, v in kwargs.items() if v is not None})
    except Exception:
        return 0.0
    if not math.isfinite(res.total_eta):
        return 0.0
    sigma_hat_inf = sigma_hat_initial - res.total_eta
    if sigma_hat_inf <= 0:
        return 0.0
    return math.sqrt(sigma_hat_inf)


# --------------------------------------------------------------------------
# Fiducial registry
# --------------------------------------------------------------------------


def _set_c_lambda(value: float, kw: dict[str, float | None]) -> dict[str, float | None]:
    kw = dict(kw)
    kw["spectral_gap_coeff"] = value
    return kw


def _set_mu_plaq(value: float, kw: dict[str, float | None]) -> dict[str, float | None]:
    kw = dict(kw)
    kw["mu_plaq"] = value
    return kw


def _set_polymer_residual(value: float, kw: dict[str, float | None]) -> dict[str, float | None]:
    kw = dict(kw)
    kw["polymer_residual"] = value
    return kw


def _set_wilson_loop_min_area(value: float, kw: dict[str, float | None]) -> dict[str, float | None]:
    kw = dict(kw)
    kw["wilson_loop_min_area"] = int(round(value))
    return kw


# Note: post-2026-05-26, c_λ baseline is 3/4 (Casimir-gap derivation);
# c_polymer baseline is 2 (BALABAN_POLYMER_RESIDUAL); A_min baseline
# is 4 (WILSON_LOOP_MIN_AREA_DIMENSIONLESS); μ_plaq baseline is 16.
FIDUCIAL_REGISTRY: Final[tuple[FiducialEntry, ...]] = (
    FiducialEntry(
        display_name=r"$c_\lambda$ (small-field spectral gap)",
        baseline=float(BAŁABAN_SPECTRAL_GAP_COEFF),  # 3/4
        perturbation_callback=_set_c_lambda,
    ),
    FiducialEntry(
        display_name=r"$\mu_{\mathrm{plaq}}$ (plaquette connectivity)",
        baseline=MU_PLAQUETTE_4D,  # 16
        perturbation_callback=_set_mu_plaq,
    ),
    FiducialEntry(
        display_name=r"$c_{\mathrm{polymer}}$ (Bałaban polymer residual)",
        baseline=2.0,
        perturbation_callback=_set_polymer_residual,
    ),
    FiducialEntry(
        display_name=r"$A_{\min}$ (Wilson loop min area)",
        baseline=4.0,
        perturbation_callback=_set_wilson_loop_min_area,
    ),
)


# --------------------------------------------------------------------------
# Tornado computation
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class TornadoBar:
    """One fiducial's tornado bar: [m_0_low, m_0_high] vs baseline m_0."""

    display_name: str
    baseline_value: float
    baseline_m_0: float
    low_value: float
    low_m_0: float
    high_value: float
    high_m_0: float

    @property
    def sensitivity(self) -> float:
        """The absolute range of m_0 across the [-20%, +20%] sweep."""
        return abs(self.high_m_0 - self.low_m_0)


def compute_tornado_bars(
    perturbation_fraction: float = 0.20,
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 1.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> list[TornadoBar]:
    """Compute m_0 at ±perturbation_fraction for each fiducial.

    Returns the list of `TornadoBar`s sorted by sensitivity (most
    sensitive first).
    """
    if not (0.0 < perturbation_fraction < 1.0):
        raise ValueError(
            f"perturbation_fraction must be in (0, 1); got {perturbation_fraction}"
        )

    baseline_kw: dict[str, float | None] = {
        "spectral_gap_coeff": None,
        "mu_plaq": None,
        "polymer_residual": None,
        "wilson_loop_min_area": None,
    }
    baseline_m_0 = _m_0_from_kwargs(
        g_0=g_0, K=K,
        sigma_hat_initial=sigma_hat_initial,
        convention=convention,
        **{k: v for k, v in baseline_kw.items() if v is not None},
    )

    bars: list[TornadoBar] = []
    for entry in FIDUCIAL_REGISTRY:
        low_value = entry.baseline * (1.0 - perturbation_fraction)
        high_value = entry.baseline * (1.0 + perturbation_fraction)

        low_kw = entry.perturbation_callback(low_value, baseline_kw)
        high_kw = entry.perturbation_callback(high_value, baseline_kw)

        low_m_0 = _m_0_from_kwargs(
            g_0=g_0, K=K,
            sigma_hat_initial=sigma_hat_initial,
            convention=convention,
            **{k: v for k, v in low_kw.items() if v is not None},
        )
        high_m_0 = _m_0_from_kwargs(
            g_0=g_0, K=K,
            sigma_hat_initial=sigma_hat_initial,
            convention=convention,
            **{k: v for k, v in high_kw.items() if v is not None},
        )

        bars.append(TornadoBar(
            display_name=entry.display_name,
            baseline_value=entry.baseline,
            baseline_m_0=baseline_m_0,
            low_value=low_value,
            low_m_0=low_m_0,
            high_value=high_value,
            high_m_0=high_m_0,
        ))

    # Sort by sensitivity (largest first → topmost in tornado).
    bars.sort(key=lambda b: b.sensitivity, reverse=True)
    return bars


# --------------------------------------------------------------------------
# Plot
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/m_0-tornado.svg"


def plot_tornado(
    bars: list[TornadoBar] | None = None,
    perturbation_fraction: float = 0.20,
    output_path: str | None = None,
) -> str:
    """Render the tornado chart to SVG.

    Layout:
      * Y-axis: fiducials sorted by sensitivity (most sensitive at top).
      * X-axis: m_0 (dimensionless).
      * Each fiducial: horizontal bar from m_0_low to m_0_high.
      * Vertical line at baseline m_0.
      * Left side of bar (m_0_low) = perturbation that LOWERS m_0
        from baseline; right side = perturbation that RAISES m_0.
    """
    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if bars is None:
        bars = compute_tornado_bars(perturbation_fraction=perturbation_fraction)

    target = Path(output_path) if output_path else (
        Path(__file__).resolve().parent.parent / DEFAULT_PLOT_PATH
    )

    baseline_m_0 = bars[0].baseline_m_0
    n = len(bars)

    fig, ax = plt.subplots(figsize=(10.5, 1.0 + 0.7 * n))

    # Reverse so most sensitive ends up at top.
    bars_display = list(reversed(bars))
    y_pos = np.arange(n)

    for i, bar in enumerate(bars_display):
        lo = min(bar.low_m_0, bar.high_m_0)
        hi = max(bar.low_m_0, bar.high_m_0)
        # Two side bars: one to the left of baseline (downward shift)
        # and one to the right (upward shift).
        left_extent = baseline_m_0 - lo if lo < baseline_m_0 else 0
        right_extent = hi - baseline_m_0 if hi > baseline_m_0 else 0
        if left_extent > 0:
            ax.barh(
                y_pos[i], width=left_extent, left=baseline_m_0 - left_extent,
                height=0.6, color="tab:red", alpha=0.7, edgecolor="black", linewidth=0.5,
            )
        if right_extent > 0:
            ax.barh(
                y_pos[i], width=right_extent, left=baseline_m_0,
                height=0.6, color="tab:green", alpha=0.7, edgecolor="black", linewidth=0.5,
            )
        # Annotate the perturbed m_0 values at each end.
        # Use bar.low_m_0 (the fiducial decreased) and bar.high_m_0
        # (the fiducial increased), not min/max — preserves the ±
        # association.
        ax.text(
            lo - 0.005, y_pos[i],
            f"  {lo:.4f}", va="center", ha="right", fontsize=8, color="tab:red",
        )
        ax.text(
            hi + 0.005, y_pos[i],
            f"{hi:.4f}", va="center", ha="left", fontsize=8, color="tab:green",
        )

    # Vertical baseline line at m_0 default.
    ax.axvline(x=baseline_m_0, color="black", linewidth=1.5, linestyle="-",
               label=f"baseline m_0 = {baseline_m_0:.4f}")

    ax.set_yticks(y_pos)
    ax.set_yticklabels([b.display_name for b in bars_display], fontsize=10)
    ax.set_xlabel(r"constructive mass-gap lower bound $m_0$ (dimensionless, $\hat\sigma_0 = 1$)",
                  fontsize=11)
    ax.set_title(
        f"$m_0$ sensitivity to ±{int(perturbation_fraction*100)}% fiducial perturbation\n"
        f"(canonical pilot, $g_0 = 0.30$, $K = 3$; sorted by sensitivity)"
    )
    ax.grid(True, alpha=0.3, axis="x")
    ax.legend(loc="lower right", fontsize=9)

    # Color-coded legend on the right.
    ax.text(
        1.02, 1.0,
        "Red: m_0 at −20% fiducial\n"
        "Green: m_0 at +20% fiducial\n"
        "Sorted: most-sensitive at top",
        transform=ax.transAxes, fontsize=9, verticalalignment="top",
        bbox=dict(boxstyle="round,pad=0.3", facecolor="lightyellow",
                  edgecolor="gray", alpha=0.8),
    )

    # Snap x-axis to a reasonable range.
    all_m_0s = [b.low_m_0 for b in bars] + [b.high_m_0 for b in bars] + [baseline_m_0]
    x_min = max(0.0, min(all_m_0s) - 0.02)
    x_max = min(1.05, max(all_m_0s) + 0.02)
    ax.set_xlim(x_min, x_max)

    fig.tight_layout()
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg", bbox_inches="tight")
    plt.close(fig)
    return str(target)


# --------------------------------------------------------------------------
# CLI / main
# --------------------------------------------------------------------------


def main() -> None:
    print("m_0 fiducial-sensitivity tornado")
    print("Canonical pilot: g_0 = 0.30, K = 3, σ̂_0 = 1")
    print(f"Perturbation: ±20% from each fiducial's baseline")
    print()
    bars = compute_tornado_bars(perturbation_fraction=0.20)
    baseline_m_0 = bars[0].baseline_m_0
    print(f"Baseline m_0 = {baseline_m_0:.6f}")
    print()
    print(f"{'Fiducial':<48} {'baseline':>10} {'m_0(-20%)':>12} {'m_0(+20%)':>12} {'range':>10}")
    for bar in bars:
        # Strip LaTeX for terminal display.
        display = bar.display_name.replace("$", "").replace("\\", "")
        print(
            f"{display:<48} {bar.baseline_value:>10.4f} "
            f"{bar.low_m_0:>12.6f} {bar.high_m_0:>12.6f} "
            f"{bar.sensitivity:>10.6f}"
        )
    print()
    path = plot_tornado(bars=bars)
    print(f"plot written: {path}")


if __name__ == "__main__":
    main()
