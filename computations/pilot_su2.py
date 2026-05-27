"""SU(2) inductive-step pilot success-criterion validator.

Milestone 3.5 of `work_plan.md`.  Runs the full inductive-step
validator over `k = 0, 1, …, K` for `K ≥ 3` and reports the five
success criteria from `docs/context.md` §7:

  1. Small-field KP condition (ρ_sf > 0, finite K_sf, convergent flag set).
  2. Large-field KP condition.
  3. Overlap KP condition (finite buffer KP witness via Proposition 7.1).
  4. Summable degradation of K_∩: Σ_k Δ_∩ < ∞ (bounded for the
     trajectory tested).
  5. Positive retained renormalized string tension: σ̂_k > 0 for
     all k, and Σ_k η_k < σ̂_0.

Status: pilot validator runs over the standard SU(2) trajectory
with the post-3.1 small-field upgrade.  The default g_0 = 1.0 lies
outside the current Bałaban/Brydges-Federbush convergence threshold,
so K_sf = ∞, Δ_∩ = ∞, η = ∞, and the pilot fails honestly.  The same
validator passes only in the asymptotic-freedom window where K_sf is
finite.

The validator's job here is to:
  (a) Lock in the FIVE-CRITERIA INTERFACE so a future genuine
      pilot can be measured against the same five flags.
  (b) Run the validator against the current upstream and emit
      a structured report.
  (c) Generate the inductive-closure summary figure.

Per work_plan 3.5's open question ("what 'succeeds' looks like
quantitatively"), our recommendation: a pilot succeeds when σ̂_K ≥
σ̂_0 / 2 for K = 3, i.e., the string tension is retained at >50% of
its initial value over three RG steps.  This is the
``threshold_success_quantitative`` flag below — independent of, but
implied by, the five-criteria pass.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import compute_large_field_kp
from computations.overlap_kp import compute_overlap_kp, delta_cap_budget
from computations.overlap_measure import standard_su2_trajectory
from computations.sigma_hat_trajectory import sigma_hat_trajectory
from computations.small_field_kp import compute_small_field_kp

# --------------------------------------------------------------------------
# Recommended pilot success threshold (work_plan 3.5 open question)
# --------------------------------------------------------------------------

PILOT_THRESHOLD_K: Final[int] = 3
"""Pick K = 3 RG steps for the pilot."""

PILOT_THRESHOLD_SIGMA_RATIO: Final[float] = 0.5
"""Pilot succeeds quantitatively iff σ̂_K ≥ ratio · σ̂_0.

Recommendation: 50% retention over 3 RG steps is a non-trivial
test of the inductive step.  Conservative; can be tightened to
70-80% once real upstream lands.
"""


# --------------------------------------------------------------------------
# Result dataclass: the five criteria + the quantitative threshold
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class PilotResult:
    """Per-criterion bool flags + threshold + supporting data."""

    # The five context.md §7 criteria.
    crit_1_small_field_KP: bool
    crit_2_large_field_KP: bool
    crit_3_overlap_KP: bool
    crit_4_delta_cap_summable: bool
    crit_5_sigma_hat_positive_and_budget: bool
    # The recommended quantitative threshold.
    threshold_success: bool
    """σ̂_K ≥ ratio · σ̂_0, with K and ratio from the module constants."""
    # Supporting data.
    K: int
    sigma_hat_initial: float
    sigma_hat_final: float
    total_delta_cap: float
    total_eta: float
    convention: HeatKernelConvention

    @property
    def all_five_pass(self) -> bool:
        """All five context.md §7 criteria pass."""
        return all(
            [
                self.crit_1_small_field_KP,
                self.crit_2_large_field_KP,
                self.crit_3_overlap_KP,
                self.crit_4_delta_cap_summable,
                self.crit_5_sigma_hat_positive_and_budget,
            ]
        )

    @property
    def pilot_succeeds(self) -> bool:
        """The full pilot success: five criteria + quantitative threshold."""
        return self.all_five_pass and self.threshold_success


# --------------------------------------------------------------------------
# Run the validator
# --------------------------------------------------------------------------


def run_pilot(
    K: int = PILOT_THRESHOLD_K,
    g_0: float = 1.0,
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    threshold_ratio: float = PILOT_THRESHOLD_SIGMA_RATIO,
) -> PilotResult:
    """Run the inductive-step validator over k = 0..K and report.

    Per work_plan 3.5, verifies the five context.md §7 criteria
    over `K + 1` RG steps, plus the quantitative σ̂ retention
    threshold.
    """
    if K < 3:
        raise ValueError(f"K must be ≥ 3 (work_plan 3.5); got {K}")

    # Build the trajectory (use the standard RG flow from 1.4).
    traj = standard_su2_trajectory(k_max=K, g_0=g_0)
    g_traj = traj[0]
    if len(g_traj) < K + 1:
        raise ValueError(
            f"trajectory truncated at Landau pole (length {len(g_traj)}); "
            f"choose smaller K or smaller g_0"
        )

    # Compute each per-scale certificate.
    sf_certs = [compute_small_field_kp(g, k, t_choice) for k, g in enumerate(g_traj)]
    lf_certs = [compute_large_field_kp(g, k, t_choice) for k, g in enumerate(g_traj)]
    cap_certs = [compute_overlap_kp(g, k, t_choice) for k, g in enumerate(g_traj)]

    # Criterion 1: every sf cert is a finite, convergent KP certificate.
    # K_sf = ∞ is a diagnostic of cluster-expansion non-convergence, not a
    # valid KP witness for the pilot.
    import math

    crit_1 = all(
        c.rho_sf > 0 and c.K_sf >= 0 and math.isfinite(c.K_sf) and c.convergent
        for c in sf_certs
    )
    # Criterion 2: every lf cert is a finite, convergent KP certificate.
    # Post-3.2-upgrade: ρ_lf and K_lf both encode the heat-kernel character-tail
    # cluster-expansion regime; a non-convergent regime gives K_lf = ∞ and is
    # not a valid KP witness, parallel to criterion 1.
    crit_2 = all(
        c.rho_lf > 0 and c.K_lf >= 0 and math.isfinite(c.K_lf) and c.convergent
        for c in lf_certs
    )
    # Criterion 3: every overlap cert is a finite KP witness satisfying
    # Proposition 7.1. The structural min/sum relationship can hold with
    # K_cap = ∞, but that is not a useful KP certificate for the pilot.
    crit_3 = all(
        c.proposition_7_1_satisfied
        and c.rho_cap > 0
        and c.K_cap >= 0
        and math.isfinite(c.K_cap)
        for c in cap_certs
    )
    # Criterion 4: Σ_k Δ_∩ is bounded for the tested K.
    budget = delta_cap_budget(g_traj, t_choice)
    crit_4 = budget.total < float("inf")  # always True structurally
    # Criterion 5: σ̂_k > 0 for all k AND Σ η < σ̂_0.
    sigma_traj = sigma_hat_trajectory(g_traj, sigma_hat_initial, t_choice)
    crit_5 = (
        all(s.sigma_hat > 0 for s in sigma_traj.steps)
        and sigma_traj.budget_closure
    )

    sigma_final = sigma_traj.steps[-1].sigma_hat
    threshold_success = sigma_final >= threshold_ratio * sigma_hat_initial

    return PilotResult(
        crit_1_small_field_KP=crit_1,
        crit_2_large_field_KP=crit_2,
        crit_3_overlap_KP=crit_3,
        crit_4_delta_cap_summable=crit_4,
        crit_5_sigma_hat_positive_and_budget=crit_5,
        threshold_success=threshold_success,
        K=K,
        sigma_hat_initial=sigma_hat_initial,
        sigma_hat_final=sigma_final,
        total_delta_cap=budget.total,
        total_eta=sigma_traj.total_eta,
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# Figure: inductive-closure summary
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/inductive-closure.svg"


def plot_inductive_closure(
    result: PilotResult | None = None,
    output_path: str | None = None,
) -> str:
    """Plot the five criteria + threshold as a status grid."""
    from pathlib import Path

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if result is None:
        result = run_pilot()

    labels = [
        "(1) Small-field KP",
        "(2) Large-field KP",
        "(3) Overlap KP (P 7.1)",
        "(4) Σ Δ_∩ bounded",
        "(5) σ̂ > 0 AND Σ η < σ̂_0",
        f"Threshold: σ̂_K ≥ {PILOT_THRESHOLD_SIGMA_RATIO} · σ̂_0",
    ]
    statuses = [
        result.crit_1_small_field_KP,
        result.crit_2_large_field_KP,
        result.crit_3_overlap_KP,
        result.crit_4_delta_cap_summable,
        result.crit_5_sigma_hat_positive_and_budget,
        result.threshold_success,
    ]
    colors = ["tab:green" if s else "tab:red" for s in statuses]
    marks = ["✓" if s else "✗" for s in statuses]

    fig, ax = plt.subplots(figsize=(8.0, 4.5))
    y = list(range(len(labels)))
    ax.barh(y, [1.0] * len(labels), color=colors, alpha=0.45)
    for i, (lab, m) in enumerate(zip(labels, marks, strict=True)):
        ax.text(0.02, i, m + "  " + lab, va="center", fontsize=11)
    ax.set_yticks([])
    ax.set_xticks([])
    ax.set_xlim(0, 1)
    ax.set_title(
        f"SU(2) inductive-step pilot ({result.convention.value} convention, "
        f"K = {result.K}; final σ̂_K = {result.sigma_hat_final:.4f}, "
        f"Σ η = {result.total_eta:.3e})"
    )
    overall = "SUCCEEDS" if result.pilot_succeeds else "FAILS"
    fig.suptitle(f"Pilot {overall} (current analytic regime — see notes/pilot-su2-results.md)",
                 fontsize=12)
    fig.tight_layout()

    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


if __name__ == "__main__":
    # Canonical convergent operating point used in the manuscript caption.
    result = run_pilot(K=3, g_0=0.30)
    print("=" * 65)
    print("SU(2) inductive-step pilot — work_plan 3.5")
    print("=" * 65)
    print(f"K (RG steps)       : {result.K}")
    print(f"Convention         : {result.convention.value}")
    print(f"σ̂_0               : {result.sigma_hat_initial}")
    print(f"σ̂_K (final)        : {result.sigma_hat_final}")
    print(f"Σ_k Δ_∩            : {result.total_delta_cap:.6e}")
    print(f"Σ_k η_k            : {result.total_eta:.6e}")
    print()
    print("The five context.md §7 criteria:")
    print(f"  (1) Small-field KP            : {result.crit_1_small_field_KP}")
    print(f"  (2) Large-field KP            : {result.crit_2_large_field_KP}")
    print(f"  (3) Overlap KP (P 7.1)        : {result.crit_3_overlap_KP}")
    print(f"  (4) Σ Δ_∩ summable            : {result.crit_4_delta_cap_summable}")
    print(f"  (5) σ̂ positive + budget       : {result.crit_5_sigma_hat_positive_and_budget}")
    print(f"All five pass?                   : {result.all_five_pass}")
    print()
    print(
        f"Quantitative threshold (σ̂_K ≥ "
        f"{PILOT_THRESHOLD_SIGMA_RATIO} · σ̂_0): {result.threshold_success}"
    )
    print()
    print("=" * 65)
    print(f"PILOT {'SUCCEEDS' if result.pilot_succeeds else 'FAILS'}")
    print("=" * 65)
    print("(Note: current analytic regime — see notes/pilot-su2-results.md)")
    path = plot_inductive_closure(result)
    print(f"\nFigure: {path}")
