"""m_0 bootstrap-uncertainty distribution across defensible fiducial envelopes.

Manuscript Appendix D upgrade (2026-05-27): convert the per-fiducial
±20% tornado statement (Fig. D.1) into a JOINT robustness statement:
sample all four named fiducials uniformly from their *defensible
envelopes*, evaluate `m_0` for each draw, and quote a robust lower
bound across the empirical distribution.

# Why bootstrap

The tornado plot (`m_0_tornado.py`) varies one fiducial at a time.
Bootstrap sampling lets all fiducials drift jointly, capturing
worst-case combinations that may shift `m_0` more than any single
±20% sweep does.  The output is a single sentence:

> "Across uniformly-sampled fiducials within their defensible
>  envelopes, `m_0 ≥ X/1000` at the 5th percentile."

This converts the deterministic "`m_0 = 999/1000` under these
fiducials" into the uncertainty-quantified "`m_0 ≥ X/1000` across
fiducial uncertainty."

# Defensible envelopes (from `notes/fiducials_notes.md`)

| Fiducial    | Baseline | Envelope    | Justification                              |
|-------------|----------|-------------|--------------------------------------------|
| `c_λ`       | 0.75     | [0.30, 1.50]| 0.30 = pilot-tolerance lower at g_0 = 0.30;|
|             |          |             |  1.50 ≈ 2× SU(2) Casimir gap (high-end     |
|             |          |             |  Bałaban-compatible value)                 |
| `μ_plaq`    | 16.0     | [10, 55]    | 10 = hypothetical tighter polymer count;   |
|             |          |             |  55 ≈ 20e (genuinely-BF-conservative bound)|
| `c_polymer` | 2.0      | [1.0, 2.0]  | 1.0 = sign-preservation-lemma tightening   |
|             |          |             |  (open analytic target);                   |
|             |          |             |  2.0 = derived worst-case (triangle ineq.) |
| `A_min`     | 4.0      | [4, 9]      | 4 = 2×2 minimum Wilson loop (spec);        |
|             |          |             |  9 = 3×3 (more conservative)               |

Each envelope brackets the values the project considers defensible
(literature-shape, derived, or pilot-tolerance bounded).  Sampling
within the envelope therefore explores the project's epistemic
uncertainty, not arbitrary perturbations.

# Output

  * `BootstrapResult` dataclass with the empirical distribution.
  * Robust lower bound = empirical 5th percentile.
  * `quote_rational_lower_bound(denom)` rounds *down* to a clean
    rational `m / denom` (manuscript-quotable).
  * `visualizations/pilot/su2/m_0-bootstrap.svg` — histogram of `m_0`
    with percentile annotations.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Callable, Final, Sequence

from computations.heat_kernel import HeatKernelConvention
from computations.m_0_tornado import (
    _m_0_from_kwargs,
    _set_c_lambda,
    _set_mu_plaq,
    _set_polymer_residual,
    _set_wilson_loop_min_area,
)
from computations.small_field_kp import BAŁABAN_SPECTRAL_GAP_COEFF
from computations.large_field_kp import MU_PLAQUETTE_4D


# --------------------------------------------------------------------------
# Defensible envelopes
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class FiducialEnvelope:
    """One fiducial's uniform-sampling envelope."""

    display_name: str
    short_name: str
    baseline: float
    low: float
    high: float
    perturbation_callback: Callable[[float, dict[str, float | None]], dict[str, float | None]]
    rationale: str

    def __post_init__(self) -> None:
        if self.low >= self.high:
            raise ValueError(
                f"envelope [{self.low}, {self.high}] must have low < high "
                f"for {self.short_name}"
            )
        if not (self.low <= self.baseline <= self.high):
            raise ValueError(
                f"baseline {self.baseline} must lie in envelope [{self.low}, {self.high}] "
                f"for {self.short_name}"
            )


# Envelopes per fiducials_notes.md §§1–6 (audit-driven defensibility).
ENVELOPES: Final[tuple[FiducialEnvelope, ...]] = (
    FiducialEnvelope(
        display_name=r"$c_\lambda$ (small-field spectral gap)",
        short_name="c_lambda",
        baseline=float(BAŁABAN_SPECTRAL_GAP_COEFF),  # 3/4
        low=0.30,
        high=1.50,
        perturbation_callback=_set_c_lambda,
        rationale=(
            "low=0.30 ≈ pilot-tolerance threshold at g_0=0.30 "
            "(c_lambda_pilot_tolerance_threshold); high=1.50 ≈ 2× SU(2) "
            "Casimir gap C_2(1/2)=3/4, covering Bałaban-compatible higher values."
        ),
    ),
    FiducialEnvelope(
        display_name=r"$\mu_{\mathrm{plaq}}$ (plaquette connectivity)",
        short_name="mu_plaq",
        baseline=float(MU_PLAQUETTE_4D),  # 16
        low=10.0,
        high=55.0,
        perturbation_callback=_set_mu_plaq,
        rationale=(
            "low=10 ≈ hypothetical tighter polymer count below Seiler 5d-4=16; "
            "high=55 ≈ 20e (genuinely-BF-conservative upper bound from "
            "plaquette_edge_neighbor_count(4)=20)."
        ),
    ),
    FiducialEnvelope(
        display_name=r"$c_{\mathrm{polymer}}$ (Bałaban polymer residual)",
        short_name="c_polymer",
        baseline=2.0,
        low=1.0,
        high=2.0,
        perturbation_callback=_set_polymer_residual,
        rationale=(
            "low=1.0 = sign-preservation-lemma tightening (open analytic target); "
            "high=2.0 = derived worst-case channel-multiplicity from "
            "triangle-inequality argument."
        ),
    ),
    FiducialEnvelope(
        display_name=r"$A_{\min}$ (Wilson loop min area)",
        short_name="A_min",
        baseline=4.0,
        low=4.0,
        high=9.0,
        perturbation_callback=_set_wilson_loop_min_area,
        rationale=(
            "low=4 = 2×2 minimum Wilson loop per outline §7.1; "
            "high=9 = 3×3 (more conservative area-law convention)."
        ),
    ),
)


# --------------------------------------------------------------------------
# Bootstrap result
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class BootstrapResult:
    """Empirical distribution of m_0 from joint uniform sampling.

    `m_0_samples` is a 1-D ndarray of length `n_samples`.  Samples that
    landed outside the convergent regime are stored as 0.0 (and counted
    in `n_failed`); the percentile / mean statistics are computed over
    the FULL sample set (failures count toward the lower tail), so the
    robust lower bound is honestly conservative.
    """

    n_samples: int
    n_failed: int
    seed: int
    m_0_samples: tuple[float, ...]  # all samples (incl. 0.0 for failures)
    fiducial_samples: dict[str, tuple[float, ...]]  # short_name → samples
    mean: float
    std: float
    percentiles: dict[float, float]  # {1, 5, 50, 95, 99} → m_0 percentile
    robust_lower_bound: float
    envelopes: tuple[FiducialEnvelope, ...] = field(repr=False)

    def quote_rational_lower_bound(self, denom: int = 1000) -> Fraction:
        """Round the robust lower bound DOWN to `m / denom` (conservative).

        The manuscript quotes the lower bound as a clean rational so it
        can be Q'-typed in the Lean layer.  Rounding down keeps the
        statement a lower bound.

        Note: the returned `Fraction` is auto-reduced by Python; use
        `numerator_at_denom(denom)` for the literal numerator at the
        requested denominator (preserves /1000 manuscript convention).
        """
        m = math.floor(self.robust_lower_bound * denom)
        return Fraction(int(m), int(denom))

    def numerator_at_denom(self, denom: int = 1000) -> int:
        """Literal numerator: `floor(robust_lower_bound * denom)`.

        Preserves the requested denominator without auto-reduction.
        Manuscript-quotable as "m_0 ≥ {numerator}/{denom}".
        """
        return int(math.floor(self.robust_lower_bound * denom))


# --------------------------------------------------------------------------
# Bootstrap sampler
# --------------------------------------------------------------------------


def _evaluate_m_0(
    fiducial_values: dict[str, float],
    *,
    g_0: float,
    K: int,
    sigma_hat_initial: float,
    convention: HeatKernelConvention,
) -> float:
    """Run m_0 evaluation at a specific fiducial draw."""
    return _m_0_from_kwargs(
        g_0=g_0,
        K=K,
        sigma_hat_initial=sigma_hat_initial,
        convention=convention,
        spectral_gap_coeff=fiducial_values.get("c_lambda"),
        mu_plaq=fiducial_values.get("mu_plaq"),
        polymer_residual=fiducial_values.get("c_polymer"),
        wilson_loop_min_area=(
            int(round(fiducial_values["A_min"]))
            if "A_min" in fiducial_values else None
        ),
    )


def run_bootstrap(
    n_samples: int = 5000,
    seed: int = 0,
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 1.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    envelopes: Sequence[FiducialEnvelope] = ENVELOPES,
    robust_percentile: float = 5.0,
) -> BootstrapResult:
    """Sample fiducials uniformly from their envelopes and collect m_0.

    Parameters
    ----------
    n_samples
        Number of joint draws.  Each draw samples one value per
        fiducial uniformly from its envelope.
    seed
        Numpy RNG seed (determinism for tests).
    robust_percentile
        Percentile to use as the robust lower bound (default 5%; the
        manuscript's headline statement is "m_0 ≥ X at the 5th
        percentile across fiducial uncertainty").

    Returns
    -------
    BootstrapResult with the full empirical distribution.
    """
    if n_samples < 1:
        raise ValueError(f"n_samples must be >= 1; got {n_samples}")
    if not (0.0 < robust_percentile < 100.0):
        raise ValueError(
            f"robust_percentile must be in (0, 100); got {robust_percentile}"
        )

    import numpy as np

    rng = np.random.default_rng(seed)
    envelopes_tuple = tuple(envelopes)

    fiducial_draws: dict[str, list[float]] = {
        env.short_name: rng.uniform(env.low, env.high, size=n_samples).tolist()
        for env in envelopes_tuple
    }

    m_0_samples: list[float] = []
    n_failed = 0
    for i in range(n_samples):
        draw = {short: fiducial_draws[short][i] for short in fiducial_draws}
        m_0 = _evaluate_m_0(
            draw,
            g_0=g_0, K=K,
            sigma_hat_initial=sigma_hat_initial,
            convention=convention,
        )
        if m_0 <= 0.0:
            n_failed += 1
        m_0_samples.append(m_0)

    arr = np.asarray(m_0_samples)
    percentiles = {
        p: float(np.percentile(arr, p))
        for p in (1.0, 5.0, 50.0, 95.0, 99.0)
    }
    robust_lower = float(np.percentile(arr, robust_percentile))

    return BootstrapResult(
        n_samples=n_samples,
        n_failed=n_failed,
        seed=seed,
        m_0_samples=tuple(m_0_samples),
        fiducial_samples={k: tuple(v) for k, v in fiducial_draws.items()},
        mean=float(arr.mean()),
        std=float(arr.std()),
        percentiles=percentiles,
        robust_lower_bound=robust_lower,
        envelopes=envelopes_tuple,
    )


# --------------------------------------------------------------------------
# Plot
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/m_0-bootstrap.svg"


def plot_bootstrap(
    result: BootstrapResult | None = None,
    output_path: str | None = None,
    n_bins: int = 40,
    n_samples: int = 5000,
    seed: int = 0,
) -> str:
    """Histogram of m_0 with percentile + robust-lower-bound annotations."""
    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if result is None:
        result = run_bootstrap(n_samples=n_samples, seed=seed)

    target = Path(output_path) if output_path else (
        Path(__file__).resolve().parent.parent / DEFAULT_PLOT_PATH
    )

    arr = np.asarray(result.m_0_samples)
    # For the histogram, drop the failed-pilot zeros (they would
    # dominate the leftmost bin and obscure the in-regime distribution).
    arr_in_regime = arr[arr > 0.0]
    n_in_regime = len(arr_in_regime)

    fig, ax = plt.subplots(figsize=(10.0, 5.5))

    ax.hist(
        arr_in_regime, bins=n_bins, color="tab:blue", alpha=0.7,
        edgecolor="black", linewidth=0.4,
    )

    # Vertical lines for percentiles.
    pct_styles = [
        (result.percentiles[5.0], "tab:red", "5th percentile (robust lower bound)"),
        (result.percentiles[50.0], "tab:purple", "median"),
        (result.percentiles[95.0], "tab:green", "95th percentile"),
    ]
    for x, color, label in pct_styles:
        ax.axvline(x=x, color=color, linewidth=2.0, linestyle="--",
                   label=f"{label}: m_0 = {x:.4f}")

    # Robust rational lower bound annotation (literal /1000 form).
    num_1000 = result.numerator_at_denom(1000)
    annotation = (
        f"$n = {result.n_samples}$ draws "
        f"({result.n_failed} failed, {n_in_regime} converged)\n"
        f"mean = {result.mean:.4f}, std = {result.std:.4f}\n"
        f"5th percentile: $m_0 = {result.percentiles[5.0]:.4f}$\n"
        f"Robust lower bound: $m_0 \\geq {num_1000}/1000 = {num_1000/1000:.3f}$"
    )
    ax.text(
        0.02, 0.97, annotation,
        transform=ax.transAxes, fontsize=10, verticalalignment="top",
        bbox=dict(boxstyle="round,pad=0.4", facecolor="lightyellow",
                  edgecolor="gray", alpha=0.9),
    )

    ax.set_xlabel(
        r"constructive mass-gap lower bound $m_0$ (dimensionless, $\hat\sigma_0 = 1$)",
        fontsize=11,
    )
    ax.set_ylabel("count", fontsize=11)
    ax.set_title(
        f"$m_0$ bootstrap distribution across defensible fiducial envelopes\n"
        f"(canonical pilot, $g_0 = 0.30$, $K = 3$; uniform sampling per fiducial)",
        fontsize=12,
    )
    ax.legend(loc="upper right", fontsize=9)
    ax.grid(True, alpha=0.3, axis="y")

    fig.tight_layout()
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg", bbox_inches="tight")
    plt.close(fig)
    return str(target)


# --------------------------------------------------------------------------
# CLI / main
# --------------------------------------------------------------------------


def main() -> None:
    print("m_0 bootstrap uncertainty across defensible fiducial envelopes")
    print("Canonical pilot: g_0 = 0.30, K = 3, σ̂_0 = 1")
    print()
    print("Envelopes:")
    for env in ENVELOPES:
        print(f"  {env.short_name:<12} baseline={env.baseline:>6.2f}  "
              f"envelope=[{env.low:>5.2f}, {env.high:>5.2f}]")
    print()
    print("Running 5000 draws (seed=0)...")
    result = run_bootstrap(n_samples=5000, seed=0)
    print()
    print(f"  n_samples = {result.n_samples}, n_failed = {result.n_failed}")
    print(f"  mean      = {result.mean:.6f}")
    print(f"  std       = {result.std:.6f}")
    print(f"  1st %ile  = {result.percentiles[1.0]:.6f}")
    print(f"  5th %ile  = {result.percentiles[5.0]:.6f}  (ROBUST LOWER BOUND)")
    print(f"  50th %ile = {result.percentiles[50.0]:.6f}")
    print(f"  95th %ile = {result.percentiles[95.0]:.6f}")
    print(f"  99th %ile = {result.percentiles[99.0]:.6f}")
    print()
    num_1000 = result.numerator_at_denom(1000)
    print(f"Robust rational lower bound (m_0 ≥ k/1000):")
    print(f"  m_0 ≥ {num_1000}/1000 = {num_1000/1000:.3f}")
    print(f"  (rounded DOWN from 5th-percentile {result.percentiles[5.0]:.6f})")
    print()
    path = plot_bootstrap(result=result)
    print(f"plot written: {path}")


if __name__ == "__main__":
    main()
