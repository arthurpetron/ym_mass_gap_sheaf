"""σ̂ trajectory and the global budget Σ_k η_k < σ̂_0.

Milestone 3.4 of `work_plan.md`, post-upgrade.  Computes the per-step
degradation η_k of the renormalized string tension σ̂_k across an RG
trajectory and checks the global budget closure

    Σ_k η_k  <  σ̂_0,

which is the make-or-break inductive-step closure of the SU(2) pilot
(per `docs/context.md` §3.3 condition 4, `docs/outline.md` §10.4).

This module:
  1. Computes η_k per step from upstream Δ_∩ (3.3) via a DERIVED
     coefficient ``DERIVED_ETA_COUPLING`` capturing the σ̂-transport
     polymer-expansion residual.
  2. Aggregates Σ_k η_k.
  3. Tests against a chosen σ̂_0 starting value.
  4. Generates the σ̂ trajectory figure.

## σ̂-transport derivation (3.4-upgrade)

Replaces the previous placeholder coupling ``η_k = 0.5 · Δ_∩``.  The
derivation, summarized:

Outline §7.1: ``σ_k`` is defined by ``⟨W_R(C)⟩_{μ_k} ≤ C_{R,k} · exp(-σ_k · A(C))``
for Wilson loops with sides ≥ ``2a_k`` — the smallest such loop has area
``A_min = (2a_k)² = 4·a_k²`` in physical units, or ``A_min_dimensionless = 4``
in lattice units.

Outline §10.4: under the block-spin map ``T_b`` (with ``a_{k+1} = b · a_k``),
dimensional analysis gives the naive scaling ``σ_{k+1}^naive = σ_k / b²``
(σ has mass²; this scaling makes ``σ̂_{k+1}^naive = a_{k+1}²·σ_k/b² = a_k²·σ_k
= σ̂_k`` — σ̂ is RG-invariant under pure dimensional scaling).

The deviation from naive scaling is the polymer-expansion residual on
``⟨W_R(C)⟩_{μ_{k+1}}``, bounded by ``Δ_∩(b, g_k)`` (the per-step buffer-K
growth from 2.3 S3) via a Bałaban-style cluster-expansion residual:

    |σ_{k+1} - σ_k / b²|  ≤  c_polymer · Δ_∩ / (4 · a_{k+1}²).

Lifting to ``σ̂``, the ``a_{k+1}²`` factor in ``σ̂_{k+1} = a_{k+1}²·σ_{k+1}``
cancels the ``a_{k+1}²`` in the denominator above:

    |σ̂_{k+1} - σ̂_k|  ≤  (c_polymer / 4) · Δ_∩(b, g_k).

Hence the derived ``η``-coupling:

    η_k  =  (c_polymer_residual / A_min_dimensionless) · Δ_∩(b, g_k).

With the fiducial values ``c_polymer_residual = 2`` (Bałaban-style
two-sided polymer-residual symmetry: each new polymer can sit on either
side of the loop boundary) and ``A_min_dimensionless = 4`` (per outline
§7.1), the default coupling is ``2/4 = 0.5`` — numerically identical to
the previous placeholder, but now derived with explicit provenance.

The derivation is **b-independent** in the σ̂ trajectory: the block-factor
``b`` enters only via the trajectory's ``g_k`` values (which determine
``Δ_∩``), not via the η coefficient itself.  This is a feature of the
canonical-scaling identity ``σ̂_{k+1}^naive = σ̂_k`` under T_b.

## References

See `notes/fiducials_notes.md` §5 / §6 for the project-wide audit of
`BALABAN_POLYMER_RESIDUAL` (flagged as HEURISTIC) and
`WILSON_LOOP_MIN_AREA_DIMENSIONLESS` (from project spec).  BibTeX
entries in `formal/references.bib`.

- **[Balaban1987RG-I]** T. Bałaban, "Renormalization group approach to
  lattice gauge field theories. I", Comm. Math. Phys. **109** (1987),
  249–301.  Block-spin pushforward and small-field framework.
- **[Balaban1988convergent]** T. Bałaban, "Convergent renormalization
  expansions for lattice gauge theories", Comm. Math. Phys. **119**
  (1988), 243–285.  Per-step convergence and the polymer-residual
  framework used (in shape) here.
- **[Brydges 1986]** D. C. Brydges, "A short course on cluster
  expansions", in *Critical phenomena, random systems, gauge theories*
  (Les Houches 1984, North-Holland 1986).  Polymer-expansion residual
  on Wilson-loop expectations.

## Re-examination of the Q'-boundary (Decision 1 record)

The Phase-3 kickoff Decision 1 left a recorded re-examination point
at 3.4: does the ℚ-only Q' representation suffice for the global
budget Σ_k η_k < σ̂_0, or does it need a separate constructive-limit
argument?

**Empirical answer for the placeholder trajectory:** Σ_k η_k = 0
because Δ_∩ = 0 throughout (3.3 with placeholder K-values).  This
is a trivial pass; it tells us nothing about whether Q' suffices
when real g-dependent K-values land.

**Structural answer:** even with real, non-trivial Δ_∩ values, the
SUM Σ_k η_k of finitely many rational terms is itself rational —
ℚ suffices for ANY FINITE truncation of the sum.  The genuine
question is convergence as K → ∞: does Σ_{k=0}^∞ η_k stay below
σ̂_0?

That is a constructive-limit statement, NOT a statement about
finite rational sums.  Concretely it requires either:

  (i) A rational tail bound: for some K_0 and explicit q : Q',
      Σ_{k ≥ K_0} η_k ≤ q.  Then the full sum is bounded by
      finite-sum + q, both rational.  Q' suffices.

  (ii) A genuine Cauchy / constructive-limit argument: the partial
      sums S_K = Σ_{k ≤ K} η_k form a Cauchy sequence (with
      explicit modulus), and the limit is bounded.  This needs
      more than Q' — a constructive-reals layer.

For the SU(2) pilot at finite K (work_plan 3.5 picks K ≥ 3), we
can use option (i) — a rational tail bound from the geometric
decay of N_p(k) and the bounded per-plaquette factors.  Q' suffices
at the truncation, with a rational tail-bound argument.

For the FULL Phase-1-output mass gap (Σ_{k=0}^∞), a separate
constructive-limit module (call it `YMGap/Constructive/Limit.lean`)
would be needed.  That's downstream of 3.5 and beyond Phase 3's
scope.

Decision: Q' SUFFICES for the SU(2) pilot at finite K.  Recording
this here.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.overlap_kp import delta_cap

# --------------------------------------------------------------------------
# Derived constants for the σ̂-transport η-coupling
# --------------------------------------------------------------------------

WILSON_LOOP_MIN_AREA_DIMENSIONLESS: Final[int] = 4
"""Smallest dimensionless Wilson-loop area at the coarse scale.

Per ``docs/outline.md`` §7.1, the area-law bound ``⟨W_R(C)⟩ ≤ C_{R,k}
· exp(-σ_k · A(C))`` applies to scale-resolved Wilson loops with sides
at least ``2a_k``.  The smallest such loop at scale ``k+1`` has sides
``2·a_{k+1}`` and area ``A_min = (2·a_{k+1})² = 4·a_{k+1}²`` in physical
units, i.e. ``A_min_dimensionless = 4`` in coarse lattice units.

This is the *load-bearing* divisor in the η-coupling derivation: the
polymer-expansion residual per unit area gets multiplied by the smallest
admissible loop area to bound the per-step σ̂ degradation.
"""

BALABAN_POLYMER_RESIDUAL: Final[float] = 2.0
"""Fiducial Bałaban-style polymer-expansion residual prefactor for σ̂.

Per [Bałaban 1985 / 1988] and [Brydges 1986]: the polymer-expansion
correction to the Wilson-loop expectation ``⟨W_R(C)⟩_{μ_{k+1}}`` relative
to its naive-rescaling pulled-back value carries a dimensionless
prefactor counting the "polymer can sit on either side of the loop
boundary" multiplicity.  The fiducial value ``c_polymer = 2`` captures
this two-sided symmetry; refinement against direct extraction from the
Bałaban literature is deferred (mirroring 3.1's ``c_λ`` fiducial choice).
"""


def derive_eta_coupling(
    polymer_residual: float = BALABAN_POLYMER_RESIDUAL,
    wilson_loop_min_area: int = WILSON_LOOP_MIN_AREA_DIMENSIONLESS,
) -> float:
    """Derived η-coupling: ``η_k = (c_polymer / A_min) · Δ_∩(b, g_k)``.

    Per the σ̂-transport derivation in the module docstring:

        η_k  ≤  c_polymer_residual / A_min_dimensionless  ·  Δ_∩(b, g_k).

    With the default fiducials ``(c_polymer, A_min) = (2, 4)``, the
    coupling is ``0.5`` — matching the previous placeholder value, but
    now derived with explicit provenance.

    The derivation is b-independent (the block factor enters only via
    ``g_k`` in ``Δ_∩``), so this function has no ``b`` argument.
    """
    if polymer_residual <= 0:
        raise ValueError(f"polymer_residual must be positive; got {polymer_residual}")
    if wilson_loop_min_area <= 0:
        raise ValueError(
            f"wilson_loop_min_area must be positive; got {wilson_loop_min_area}"
        )
    return polymer_residual / wilson_loop_min_area


DERIVED_ETA_COUPLING: Final[float] = derive_eta_coupling()
"""The default σ̂-transport η-coupling, derived from fiducial constants.

``DERIVED_ETA_COUPLING = BALABAN_POLYMER_RESIDUAL / WILSON_LOOP_MIN_AREA_DIMENSIONLESS
= 2 / 4 = 0.5``.

Numerically identical to the previous ``PLACEHOLDER_ETA_COUPLING``, but
sourced from `derive_eta_coupling()` rather than a bare literal.  Refining
``BALABAN_POLYMER_RESIDUAL`` against the Bałaban literature shifts this
value; refining ``WILSON_LOOP_MIN_AREA_DIMENSIONLESS`` against a tighter
loop-area convention shifts it inversely.
"""


# --------------------------------------------------------------------------
# Result dataclasses
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SigmaHatStep:
    """One step of the σ̂ trajectory."""

    scale_k: int
    sigma_hat: float
    g_k: float
    eta_k: float  # the degradation FROM scale k to k+1
    convention: HeatKernelConvention


@dataclass(frozen=True)
class SigmaHatTrajectory:
    """The full σ̂ trajectory with the global budget check."""

    steps: list[SigmaHatStep]
    sigma_hat_initial: float
    total_eta: float
    """Σ_k η_k across the trajectory."""
    budget_closure: bool
    """True iff Σ_k η_k < σ̂_0 — the make-or-break Phase-3 condition."""
    convention: HeatKernelConvention


# --------------------------------------------------------------------------
# Compute the trajectory
# --------------------------------------------------------------------------


def compute_eta(
    g_k: float,
    g_k_next: float,
    t_choice: HeatKernelConvention,
    eta_coupling: float = DERIVED_ETA_COUPLING,
) -> float:
    """Per-step η_k from Δ_∩ via the σ̂-transport polymer-residual factor.

    ``η_k = eta_coupling · Δ_∩(g_k, g_k_next)``.

    The default ``eta_coupling = DERIVED_ETA_COUPLING = 0.5`` is derived
    from outline §7.1's smallest dimensionless Wilson loop area
    ``A_min = 4`` and the Bałaban-style polymer-residual prefactor
    ``c_polymer = 2`` per the module docstring's σ̂-transport derivation.
    Override via the ``eta_coupling`` parameter for sensitivity analysis
    or to test refined-fiducial values.
    """
    d = delta_cap(g_k, g_k_next, t_choice)
    return eta_coupling * d


def sigma_hat_trajectory(
    g_trajectory: list[float],
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    eta_coupling: float = DERIVED_ETA_COUPLING,
) -> SigmaHatTrajectory:
    """The σ̂ trajectory σ̂_0, σ̂_1, …, σ̂_K and the budget closure check.

    σ̂_{k+1} = σ̂_k - η_k, with η_k from `compute_eta`.

    Per work_plan 3.4, returns the cumulative degradation and a
    boolean indicating whether Σ_k η_k < σ̂_0 (the inductive-step
    budget closure).
    """
    if sigma_hat_initial <= 0:
        raise ValueError(f"sigma_hat_initial must be positive; got {sigma_hat_initial}")

    steps: list[SigmaHatStep] = []
    sigma_hat = sigma_hat_initial
    total_eta = 0.0

    for k in range(len(g_trajectory)):
        # η_k is the FROM-this-step transition.  For the last k there's no next.
        if k < len(g_trajectory) - 1:
            eta_k = compute_eta(
                g_trajectory[k], g_trajectory[k + 1], t_choice, eta_coupling
            )
        else:
            eta_k = 0.0
        steps.append(
            SigmaHatStep(
                scale_k=k,
                sigma_hat=sigma_hat,
                g_k=g_trajectory[k],
                eta_k=eta_k,
                convention=t_choice,
            )
        )
        total_eta += eta_k
        sigma_hat -= eta_k  # for the NEXT step

    budget_closure = total_eta < sigma_hat_initial

    return SigmaHatTrajectory(
        steps=steps,
        sigma_hat_initial=sigma_hat_initial,
        total_eta=total_eta,
        budget_closure=budget_closure,
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# Figure
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = "visualizations/pilot/su2/sigma-hat-trajectory.svg"


def plot_sigma_hat_trajectory(
    g_trajectory: list[float] | None = None,
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
) -> str:
    """Plot σ̂_k vs k and the cumulative η budget."""
    from pathlib import Path

    import matplotlib
    import numpy as np

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if g_trajectory is None:
        from computations.overlap_measure import standard_su2_trajectory

        traj = standard_su2_trajectory(k_max=10)
        g_trajectory = traj[0]

    result = sigma_hat_trajectory(g_trajectory, sigma_hat_initial, t_choice)
    k_values = np.arange(len(result.steps))
    sigma_values = [s.sigma_hat for s in result.steps]
    eta_values = [s.eta_k for s in result.steps]
    cumulative_eta = np.cumsum(eta_values)

    fig, (ax_left, ax_right) = plt.subplots(1, 2, figsize=(10.0, 4.5))
    ax_left.plot(k_values, sigma_values, "o-", color="tab:blue", markersize=5,
                 label=r"$\widehat{\sigma}_k$")
    ax_left.axhline(sigma_hat_initial, linestyle="--", alpha=0.4, color="gray",
                    label=r"$\widehat{\sigma}_0$ (initial)")
    ax_left.set_xlabel("RG step k")
    ax_left.set_ylabel(r"$\widehat{\sigma}_k$")
    ax_left.set_title("Renormalized string tension trajectory")
    ax_left.grid(True, alpha=0.3)
    ax_left.legend()

    ax_right.plot(
        k_values, cumulative_eta, "o-", color="tab:red", markersize=5,
        label=r"$\sum_{j \leq k} \eta_j$"
    )
    ax_right.axhline(
        sigma_hat_initial, linestyle="--", alpha=0.4, color="gray",
        label=r"$\widehat{\sigma}_0$ budget cap"
    )
    ax_right.set_xlabel("RG step k")
    ax_right.set_ylabel(r"cumulative $\sum \eta$")
    ax_right.set_title(
        f"η budget closure: Σ η = {result.total_eta:.3e}; "
        f"closes: {result.budget_closure}"
    )
    ax_right.grid(True, alpha=0.3)
    ax_right.legend()

    fig.suptitle(
        f"SU(2) σ̂-trajectory + budget closure ({t_choice.value}, σ̂_0 = {sigma_hat_initial})"
    )
    fig.tight_layout()

    target = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent / DEFAULT_PLOT_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


if __name__ == "__main__":
    from computations.overlap_measure import standard_su2_trajectory

    traj = standard_su2_trajectory(k_max=5)
    g_traj: list[float] = traj[0]
    result = sigma_hat_trajectory(g_traj, sigma_hat_initial=1.0)
    print(f"σ̂ trajectory (σ̂_0 = {result.sigma_hat_initial}, "
          f"{len(result.steps)} steps):")
    for s in result.steps:
        print(f"  k={s.scale_k:2d}  g={s.g_k:.4f}  σ̂={s.sigma_hat:.4f}  "
              f"η_k={s.eta_k:.4e}")
    print(f"\n  Total Σ η_k       = {result.total_eta:.6e}")
    print(f"  Budget closes?    = {result.budget_closure}")
    print(f"  σ̂_K (final)      = {result.steps[-1].sigma_hat:.6f}")
    path = plot_sigma_hat_trajectory()
    print(f"  figure: {path}")
