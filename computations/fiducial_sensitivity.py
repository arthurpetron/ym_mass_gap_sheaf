"""Fiducial sensitivity sweeps for the SU(2) pilot.

Sweeps each of the three flagged fiducials from
``notes/fiducials_notes.md`` and reports how the pilot's convergence
thresholds and budget margin respond.

# What is fiducial in this project

Per `notes/fiducials_notes.md`, three constants are flagged as
HEURISTIC or LITERATURE-SHAPE-PENDING-VERIFICATION:

  1. ``BAŁABAN_SPECTRAL_GAP_COEFF = 1/2`` (small-field activity rate
     coefficient) — literature-shape, value not directly extracted.
  2. ``MU_PLAQUETTE_4D = 16`` (large-field plaquette connectivity) —
     widely cited as ``5d - 4`` but not verified verbatim; a
     conservative rigorous fallback ``MU_PLAQUETTE_CONSERVATIVE_4D
     = 8e`` is available.
  3. ``BALABAN_POLYMER_RESIDUAL = 2.0`` (σ̂-transport coupling) —
     heuristic, chosen to match the previous placeholder value.

# What this module does

For each fiducial, sweep across a plausible range and report:

  * the resulting ``g_max`` for the affected KP family (sf / lf);
  * the pilot's ``Σ_k η_k`` and budget margin at a chosen ``g_0`` /
    ``σ̂_0``;
  * whether the pilot closes.

The sweep helps decide which refinement directions are load-bearing for
the SU(2) pilot at a given target ``g_0`` — and which are not.

# Use cases

  * Quick refinement priority: which fiducial moves ``g_max`` the most?
  * Stress test: at what value of each fiducial does the pilot break?
  * Audit transparency: explicit dependence on the numerical choices.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import (
    MU_PLAQUETTE_4D,
    MU_PLAQUETTE_CONSERVATIVE_4D,
    convergence_threshold_g_lf,
)
from computations.overlap_measure import standard_su2_trajectory
from computations.sigma_hat_trajectory import (
    BALABAN_POLYMER_RESIDUAL,
    WILSON_LOOP_MIN_AREA_DIMENSIONLESS,
    sigma_hat_trajectory,
)
from computations.small_field_kp import (
    BAŁABAN_SPECTRAL_GAP_COEFF,
    convergence_threshold_g,
)


# --------------------------------------------------------------------------
# Result dataclasses
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class FiducialSweepPoint:
    """One sample of a sensitivity sweep."""

    fiducial_name: str
    fiducial_value: float
    g_max_sf: float | None
    g_max_lf: float | None
    sigma_hat_trajectory_total_eta: float | None
    sigma_hat_trajectory_budget_closes: bool | None
    convention: HeatKernelConvention


@dataclass(frozen=True)
class FiducialSweepResult:
    """Full sweep of one fiducial across a value range."""

    fiducial_name: str
    fiducial_default: float
    convention: HeatKernelConvention
    points: list[FiducialSweepPoint] = field(default_factory=list)


# --------------------------------------------------------------------------
# Sweeps
# --------------------------------------------------------------------------


def sweep_spectral_gap_coeff(
    values: list[float] | None = None,
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 10.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> FiducialSweepResult:
    """Sweep ``BAŁABAN_SPECTRAL_GAP_COEFF`` and report g_max_sf + pilot closure.

    Default values span [0.25, 2.0] around the fiducial 1/2.  At smaller
    c_λ the small-field convergent regime shrinks (``g_max_sf =
    √(c_λ · conv_factor / μ_sf)`` falls) AND K_sf grows in the
    convergent window — both effects flow into Δ_∩ and η_k via the
    ``spectral_gap_coeff`` override threaded through
    ``sigma_hat_trajectory`` since 2026-05-24.
    """
    if values is None:
        values = [0.25, 0.375, 0.5, 0.625, 0.75, 1.0, 1.5, 2.0]

    points = []
    g_traj = standard_su2_trajectory(k_max=K, g_0=g_0)[0]

    for c_lambda in values:
        g_max_sf = convergence_threshold_g(
            t_choice=convention, spectral_gap_coeff=c_lambda
        )
        try:
            res = sigma_hat_trajectory(
                g_traj,
                sigma_hat_initial=sigma_hat_initial,
                t_choice=convention,
                spectral_gap_coeff=c_lambda,
            )
            total = res.total_eta
            closes = res.budget_closure
        except Exception:
            total = None
            closes = None
        points.append(
            FiducialSweepPoint(
                fiducial_name="BAŁABAN_SPECTRAL_GAP_COEFF",
                fiducial_value=c_lambda,
                g_max_sf=g_max_sf,
                g_max_lf=None,
                sigma_hat_trajectory_total_eta=total,
                sigma_hat_trajectory_budget_closes=closes,
                convention=convention,
            )
        )

    return FiducialSweepResult(
        fiducial_name="BAŁABAN_SPECTRAL_GAP_COEFF",
        fiducial_default=float(BAŁABAN_SPECTRAL_GAP_COEFF),
        convention=convention,
        points=points,
    )


def sweep_mu_plaq(
    values: list[float] | None = None,
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 10.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> FiducialSweepResult:
    """Sweep ``MU_PLAQUETTE_4D`` and report g_max_lf + pilot closure.

    Default values include the literature-shape ``16``, the conservative
    rigorous fallback ``8e ≈ 21.75``, and intermediates plus tighter
    speculative bounds.  The ``mu_plaq`` override is threaded into
    ``sigma_hat_trajectory`` (since 2026-05-24), so the swept ``Σ η_k``
    column reflects the actual large-field-induced movement in Δ_∩.
    """
    if values is None:
        values = [
            8.0,
            12.0,
            MU_PLAQUETTE_4D,                # 16, default literature-shape
            MU_PLAQUETTE_CONSERVATIVE_4D,   # 8e ≈ 21.75, rigorous fallback
            32.0,
            64.0,
        ]

    points = []
    g_traj = standard_su2_trajectory(k_max=K, g_0=g_0)[0]

    for mu in values:
        g_max_lf = convergence_threshold_g_lf(t_choice=convention, mu_plaq=mu)
        try:
            res = sigma_hat_trajectory(
                g_traj,
                sigma_hat_initial=sigma_hat_initial,
                t_choice=convention,
                mu_plaq=mu,
            )
            total = res.total_eta
            closes = res.budget_closure
        except Exception:
            total = None
            closes = None
        points.append(
            FiducialSweepPoint(
                fiducial_name="MU_PLAQUETTE_4D",
                fiducial_value=mu,
                g_max_sf=None,
                g_max_lf=g_max_lf,
                sigma_hat_trajectory_total_eta=total,
                sigma_hat_trajectory_budget_closes=closes,
                convention=convention,
            )
        )

    return FiducialSweepResult(
        fiducial_name="MU_PLAQUETTE_4D",
        fiducial_default=MU_PLAQUETTE_4D,
        convention=convention,
        points=points,
    )


def sweep_polymer_residual(
    values: list[float] | None = None,
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 1.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> FiducialSweepResult:
    """Sweep ``BALABAN_POLYMER_RESIDUAL`` (η-coupling numerator).

    Larger c_polymer ↔ larger η-coupling ↔ tighter budget closure
    (harder to satisfy ``Σ_k η_k < σ̂_0``).  At each sample we report the
    pilot's total Σ η_k and whether the budget closes; the choice of
    ``g_0`` and ``sigma_hat_initial`` determines the working point.
    """
    if values is None:
        values = [0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 8.0]

    points = []
    g_traj = standard_su2_trajectory(k_max=K, g_0=g_0)[0]

    for c_polymer in values:
        res = sigma_hat_trajectory(
            g_traj,
            sigma_hat_initial=sigma_hat_initial,
            t_choice=convention,
            polymer_residual=c_polymer,
            wilson_loop_min_area=WILSON_LOOP_MIN_AREA_DIMENSIONLESS,
        )
        points.append(
            FiducialSweepPoint(
                fiducial_name="BALABAN_POLYMER_RESIDUAL",
                fiducial_value=c_polymer,
                g_max_sf=None,
                g_max_lf=None,
                sigma_hat_trajectory_total_eta=res.total_eta,
                sigma_hat_trajectory_budget_closes=res.budget_closure,
                convention=convention,
            )
        )

    return FiducialSweepResult(
        fiducial_name="BALABAN_POLYMER_RESIDUAL",
        fiducial_default=BALABAN_POLYMER_RESIDUAL,
        convention=convention,
        points=points,
    )


# --------------------------------------------------------------------------
# Max-g₀ closure window
# --------------------------------------------------------------------------


def max_g0_closure(
    K: int = 3,
    sigma_hat_initial: float = 1.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
    polymer_residual: float | None = None,
    wilson_loop_min_area: int | None = None,
    g_search_range: tuple[float, float] = (1e-3, 2.0),
    tolerance: float = 1e-4,
    max_iter: int = 80,
) -> float:
    """Largest ``g_0`` for which the SU(2) pilot still closes the σ̂ budget.

    Bisects ``g_0`` in ``g_search_range``.  The pilot closes when:
      * the small-field cluster expansion converges throughout the
        trajectory (``K_sf`` finite at every ``g_k``),
      * the large-field cluster expansion converges throughout, AND
      * ``Σ_k η_k < sigma_hat_initial``.

    All fiducial overrides flow through to the same code path as
    ``sigma_hat_trajectory``.  Returns the lower edge if the pilot
    fails everywhere, or the upper edge if it closes everywhere.

    Use cases:
      * "What does adopting ``MU_PLAQUETTE_CONSERVATIVE_4D = 8e`` cost
        in pilot window vs the default 16?"
      * "If I refine ``BALABAN_POLYMER_RESIDUAL`` upward by factor 2,
        does the pilot window shrink past the canonical wire-in
        g_0 = 0.30?"
    """
    def closes_at(g0: float) -> bool:
        g_traj = standard_su2_trajectory(k_max=K, g_0=g0)[0]
        kwargs: dict = {
            "sigma_hat_initial": sigma_hat_initial,
            "t_choice": convention,
            "spectral_gap_coeff": spectral_gap_coeff,
            "mu_plaq": mu_plaq,
        }
        if polymer_residual is not None:
            kwargs["polymer_residual"] = polymer_residual
        if wilson_loop_min_area is not None:
            kwargs["wilson_loop_min_area"] = wilson_loop_min_area
        try:
            res = sigma_hat_trajectory(g_traj, **kwargs)
        except Exception:
            return False
        return res.budget_closure

    g_low, g_high = g_search_range
    if not closes_at(g_low):
        return g_low
    if closes_at(g_high):
        return g_high
    for _ in range(max_iter):
        g_mid = 0.5 * (g_low + g_high)
        if closes_at(g_mid):
            g_low = g_mid
        else:
            g_high = g_mid
        if g_high - g_low < tolerance:
            break
    return g_low


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------


def format_sweep_result(result: FiducialSweepResult) -> str:
    """Format a sweep as a human-readable table."""
    lines = []
    lines.append(f"Fiducial sweep: {result.fiducial_name}")
    lines.append(f"  default value      = {result.fiducial_default}")
    lines.append(f"  convention         = {result.convention.value}")
    lines.append("")
    has_sf = any(p.g_max_sf is not None for p in result.points)
    has_lf = any(p.g_max_lf is not None for p in result.points)
    has_eta = any(
        p.sigma_hat_trajectory_total_eta is not None for p in result.points
    )
    headers = ["value"]
    if has_sf:
        headers.append("g_max_sf")
    if has_lf:
        headers.append("g_max_lf")
    if has_eta:
        headers.append("Σ η_k")
        headers.append("closes?")
    lines.append("  " + " | ".join(f"{h:>14}" for h in headers))
    lines.append("  " + "-+-".join("-" * 14 for _ in headers))
    for p in result.points:
        row = [f"{p.fiducial_value:>14.4f}"]
        if has_sf:
            row.append(
                f"{p.g_max_sf:>14.4f}" if p.g_max_sf is not None else f"{'-':>14}"
            )
        if has_lf:
            row.append(
                f"{p.g_max_lf:>14.4f}" if p.g_max_lf is not None else f"{'-':>14}"
            )
        if has_eta:
            if p.sigma_hat_trajectory_total_eta is None:
                row.append(f"{'-':>14}")
            else:
                row.append(f"{p.sigma_hat_trajectory_total_eta:>14.4e}")
            if p.sigma_hat_trajectory_budget_closes is None:
                row.append(f"{'-':>14}")
            else:
                row.append(
                    f"{str(p.sigma_hat_trajectory_budget_closes):>14}"
                )
        lines.append("  " + " | ".join(row))
    return "\n".join(lines)


def run_all_sweeps(
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    g_0: float = 0.30,
    K: int = 3,
    sigma_hat_initial: float = 1.0,
) -> dict[str, FiducialSweepResult]:
    """Run every fiducial sweep and return them keyed by fiducial name."""
    return {
        "BAŁABAN_SPECTRAL_GAP_COEFF": sweep_spectral_gap_coeff(
            g_0=g_0,
            K=K,
            sigma_hat_initial=sigma_hat_initial,
            convention=convention,
        ),
        "MU_PLAQUETTE_4D": sweep_mu_plaq(
            g_0=g_0,
            K=K,
            sigma_hat_initial=sigma_hat_initial,
            convention=convention,
        ),
        "BALABAN_POLYMER_RESIDUAL": sweep_polymer_residual(
            g_0=g_0,
            K=K,
            sigma_hat_initial=sigma_hat_initial,
            convention=convention,
        ),
    }


if __name__ == "__main__":
    print("Fiducial sensitivity sweeps — SU(2) pilot")
    print("=" * 65)
    sweeps = run_all_sweeps()
    for name in ("BAŁABAN_SPECTRAL_GAP_COEFF", "MU_PLAQUETTE_4D",
                 "BALABAN_POLYMER_RESIDUAL"):
        print()
        print(format_sweep_result(sweeps[name]))
    print()
    print("=" * 65)
    print("All three fiducials are threaded through to Σ η_k via "
          "sigma_hat_trajectory's spectral_gap_coeff / mu_plaq / "
          "polymer_residual parameters (as of 2026-05-24).  "
          "The ``closes?`` column reflects the actual σ̂-budget check at the "
          "swept fiducial value.")
    print()
    print("=" * 65)
    print("Pilot-window analysis: max g_0 for closure")
    print("=" * 65)
    g_default = max_g0_closure(K=3, sigma_hat_initial=1.0)
    g_conserv = max_g0_closure(
        K=3, sigma_hat_initial=1.0, mu_plaq=MU_PLAQUETTE_CONSERVATIVE_4D,
    )
    g_tight_sf = max_g0_closure(
        K=3, sigma_hat_initial=1.0, spectral_gap_coeff=1.0,
    )
    g_loose_sf = max_g0_closure(
        K=3, sigma_hat_initial=1.0, spectral_gap_coeff=0.3,
    )
    print(f"  default fiducials                          g_0_max ≈ {g_default:.4f}")
    print(f"  conservative μ_plaq = 8e                  g_0_max ≈ {g_conserv:.4f}")
    print(f"  tighter sf (c_λ = 1.0)                    g_0_max ≈ {g_tight_sf:.4f}")
    print(f"  looser  sf (c_λ = 0.3)                    g_0_max ≈ {g_loose_sf:.4f}")
