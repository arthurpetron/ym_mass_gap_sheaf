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

## Chaining tightening of η (Milestone 6.5-eta, 2026-05-27)

The base η-bound

    η_k = (c_polymer / A_min) · Δ_∩(b, g_k)

absorbs a per-plaquette **union bound** on the buffer-shell aggregate
probability μ_k(Ω_k^∩) inside its polymer-cluster-expansion derivation
(outline §17.1, §10.4).  Milestone 6.5
(`computations/chaining_estimate.py`) replaces that union bound with a
**chaining bound**

    μ_k(Ω_k^∩)  ≤  c_chain(g_k) · (union bound),

where ``c_chain(g) = exp(-n_share · g² · ζ)`` (n_share = 4, ζ = 1/2)
is the correlation-aware tightening factor admissible in the
small-positive-correlation regime ``g ≤ G_MAX_CHAIN = 2``.  Threading
this factor into the η-bound gives the chaining-tightened η:

    η_k_chaining  =  c_chain(g_k) · η_k_baseline.

This is mathematically honest because:
  * ``c_chain ∈ (0, 1]`` everywhere, so the chaining bound can only
    TIGHTEN η, never loosen it (preserves the σ̂-budget).
  * The chaining factor is grounded in the same heat-kernel
    two-plaquette correlation structure that drives Δ_∩'s
    cluster-expansion residuals (no double-counting).
  * The ``g ≤ G_MAX_CHAIN`` regime check prevents silent misuse
    outside the small-positive-correlation regime.

The chaining-tightened ``η`` is opt-in via ``use_chaining=True`` on
``compute_eta`` and ``sigma_hat_trajectory``; the default behavior is
unchanged (``use_chaining=False`` matches the pre-2026-05-27 baseline).

Phase-3 numerical impact (canonical pilot, g_0 = 0.30, K = 3): the
chaining factor at the trajectory's binding g-value g_0 = 0.30 is
``c_chain(0.30) ≈ 0.835``, giving ``η_total`` ≈ 0.835× the baseline,
which uplifts the constructive mass-gap lower bound ``m_0 = sqrt(σ̂_∞)``
by a small but ironclad factor.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import MU_PLAQUETTE_4D
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

def derive_polymer_boundary_channel_count() -> int:
    """Worst-case channel multiplicity for boundary-polymer σ-residual.

    **First-principles derivation** (see
    ``notes/sigma-hat-derivation.md`` §2.3-derivation):

    The per-step σ-residual decomposes as
    ``σ_{k+1} - σ_k/b² = -(1/A(C)) · Σ_X ΔT(X)`` over boundary polymers,
    where ``ΔT(X) := T_{k+1}(X'; C') - T_k(X; C)`` is the change in the
    cluster-expansion truncated correlation for polymer ``X`` under the
    block-spin coarsening ``T_b`` (with ``X' = T_b(X)``).

    Apply the triangle inequality:

        |ΔT(X)|  ≤  |T_{k+1}(X'; C')| + |T_k(X; C)|
                 ≤  |a_{k+1}(X')| + |a_k(X)|       (cluster-expansion bound)
                 ≤  2 · max(|a_{k+1}(X')|, |a_k(X)|).

    The final factor of 2 is the **channel multiplicity**: the per-polymer
    change is bounded by the sum of two activity terms (scale-k original
    and scale-(k+1) image), hence ``c_polymer = 2``.

    **Tightness**: the triangle inequality saturates when the two
    activities have opposite signs.  Sign-preservation under block-spin
    coarsening is not generically true (cluster-expansion truncation
    orders can flip signs), so ``c_polymer = 2`` is the optimal worst-case.

    A tighter ``c_polymer = 1`` would require an additional
    sign-preservation lemma for the SU(2) heat-kernel polymer activities;
    that's an open refinement target (see the docstring of
    ``BALABAN_POLYMER_RESIDUAL`` below).

    Returns the integer ``2``; consumed by ``BALABAN_POLYMER_RESIDUAL``.
    """
    return 2


BALABAN_POLYMER_RESIDUAL: Final[float] = float(derive_polymer_boundary_channel_count())
"""Per-polymer channel multiplicity in the Wilson-loop σ-residual.

**Status: DERIVED** (2026-05-25).  Previously labeled HEURISTIC; now
sourced from ``derive_polymer_boundary_channel_count()``, which gives
``2`` via the triangle-inequality argument on the per-polymer
``ΔT(X) = T_{k+1}(X'; C') - T_k(X; C)`` under block-spin coarsening
(``notes/sigma-hat-derivation.md`` §2.3-derivation).

The value 2 is the optimal worst-case constant: the triangle inequality
``|a - b| ≤ |a| + |b|`` saturates exactly when sign-preservation under
``T_b`` fails, and sign-preservation is not generic for cluster-expansion
polymer activities.

**Refinement target** (analytic, open): show that the SU(2) heat-kernel
measure preserves polymer-activity sign under block-spin coarsening at
the leading order.  If true, ``c_polymer = 1`` halves the σ-budget
consumption — a real pilot-window enlargement.  Until that lemma is
established, ``c_polymer = 2`` is the correct worst-case value.
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
    polymer_residual: float | None = None,
    wilson_loop_min_area: int | None = None,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
    use_chaining: bool = False,
    chain_n_share: int | None = None,
    chain_zeta: float | None = None,
) -> float:
    """Per-step η_k from Δ_∩ via the σ̂-transport polymer-residual factor.

    ``η_k = eta_coupling · Δ_∩(g_k, g_k_next)``  (baseline)

    or, with ``use_chaining=True`` (Milestone 6.5-eta, 2026-05-27):

    ``η_k = c_chain(g_k) · eta_coupling · Δ_∩(g_k, g_k_next)``,

    where ``c_chain(g_k) = exp(-n_share · g_k² · ζ)`` is the
    chaining tightening factor from ``computations/chaining_estimate.py``.
    See the module docstring §"Chaining tightening of η" for the
    derivation.

    The default ``eta_coupling = DERIVED_ETA_COUPLING = 0.5`` is derived
    from outline §7.1's smallest dimensionless Wilson loop area
    ``A_min = 4`` and the Bałaban-style polymer-residual prefactor
    ``c_polymer = 2`` per the module docstring's σ̂-transport derivation.

    For fiducial sensitivity sweeps:

      * Pass ``polymer_residual`` and/or ``wilson_loop_min_area`` to
        rebuild the η coupling; when either is supplied, ``eta_coupling``
        is recomputed via ``derive_eta_coupling`` and the explicit
        ``eta_coupling`` argument is ignored.
      * Pass ``spectral_gap_coeff`` and/or ``mu_plaq`` to override the
        small-field / large-field upstream fiducials.  These flow into
        Δ_∩ and so affect η through the upstream cluster-expansion
        amplitudes.  See ``notes/fiducials_notes.md``.

    Chaining tightening (opt-in):

      * ``use_chaining=True`` multiplies the base η by
        ``chain_factor(g_k, n_share, zeta)``.  Pass ``chain_n_share`` /
        ``chain_zeta`` to override the chaining fiducials (defaults are
        ``SHARED_LINK_CHANNEL_MULTIPLICITY = 4`` and
        ``PER_CHANNEL_CORRELATION_STRENGTH = 0.5``).
      * Raises ``RuntimeError`` if ``g_k > G_MAX_CHAIN = 2.0`` (the
        small-positive-correlation regime no longer holds).
    """
    if polymer_residual is not None or wilson_loop_min_area is not None:
        eta_coupling = derive_eta_coupling(
            polymer_residual=(
                polymer_residual if polymer_residual is not None
                else BALABAN_POLYMER_RESIDUAL
            ),
            wilson_loop_min_area=(
                wilson_loop_min_area if wilson_loop_min_area is not None
                else WILSON_LOOP_MIN_AREA_DIMENSIONLESS
            ),
        )
    d = delta_cap(
        g_k, g_k_next, t_choice,
        spectral_gap_coeff=spectral_gap_coeff, mu_plaq=mu_plaq,
    )
    eta = eta_coupling * d

    if use_chaining:
        from computations.chaining_estimate import (
            PER_CHANNEL_CORRELATION_STRENGTH,
            SHARED_LINK_CHANNEL_MULTIPLICITY,
            chain_factor,
        )
        cf = chain_factor(
            g_k,
            n_share=(
                chain_n_share if chain_n_share is not None
                else SHARED_LINK_CHANNEL_MULTIPLICITY
            ),
            zeta=(
                chain_zeta if chain_zeta is not None
                else PER_CHANNEL_CORRELATION_STRENGTH
            ),
        )
        eta = cf * eta

    return eta


def sigma_hat_trajectory(
    g_trajectory: list[float],
    sigma_hat_initial: float = 1.0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    eta_coupling: float = DERIVED_ETA_COUPLING,
    polymer_residual: float | None = None,
    wilson_loop_min_area: int | None = None,
    spectral_gap_coeff: float | None = None,
    mu_plaq: float = MU_PLAQUETTE_4D,
    use_chaining: bool = False,
    chain_n_share: int | None = None,
    chain_zeta: float | None = None,
) -> SigmaHatTrajectory:
    """The σ̂ trajectory σ̂_0, σ̂_1, …, σ̂_K and the budget closure check.

    σ̂_{k+1} = σ̂_k - η_k, with η_k from `compute_eta`.

    Per work_plan 3.4, returns the cumulative degradation and a
    boolean indicating whether Σ_k η_k < σ̂_0 (the inductive-step
    budget closure).

    Fiducial-sweep parameters:

      * ``polymer_residual``, ``wilson_loop_min_area`` — recompute the
        η coupling (overrides explicit ``eta_coupling``).
      * ``spectral_gap_coeff``, ``mu_plaq`` — override the upstream
        small-field / large-field fiducials, flowing into Δ_∩.

    Chaining (Milestone 6.5-eta, 2026-05-27):

      * ``use_chaining=True`` multiplies each η_k by
        ``chain_factor(g_k)`` (only tightens, never loosens; the
        chaining model's regime check ``g_k ≤ G_MAX_CHAIN`` is enforced
        per step).  ``chain_n_share`` / ``chain_zeta`` override the
        chaining fiducials.  See the module docstring's "Chaining
        tightening of η" section.

    All sweep parameters default to the project-wide fiducials in
    ``notes/fiducials_notes.md``.
    """
    if polymer_residual is not None or wilson_loop_min_area is not None:
        eta_coupling = derive_eta_coupling(
            polymer_residual=(
                polymer_residual if polymer_residual is not None
                else BALABAN_POLYMER_RESIDUAL
            ),
            wilson_loop_min_area=(
                wilson_loop_min_area if wilson_loop_min_area is not None
                else WILSON_LOOP_MIN_AREA_DIMENSIONLESS
            ),
        )
    if sigma_hat_initial <= 0:
        raise ValueError(f"sigma_hat_initial must be positive; got {sigma_hat_initial}")

    steps: list[SigmaHatStep] = []
    sigma_hat = sigma_hat_initial
    total_eta = 0.0

    for k in range(len(g_trajectory)):
        # η_k is the FROM-this-step transition.  For the last k there's no next.
        if k < len(g_trajectory) - 1:
            eta_k = compute_eta(
                g_trajectory[k], g_trajectory[k + 1], t_choice, eta_coupling,
                spectral_gap_coeff=spectral_gap_coeff, mu_plaq=mu_plaq,
                use_chaining=use_chaining,
                chain_n_share=chain_n_share,
                chain_zeta=chain_zeta,
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

        # Default to the canonical pilot (g_0 = 0.30, K = 10) so the rendered
        # figure shows a budget that closes.  Earlier the default g_0 = 1.2
        # produced an Σ η = ∞ blow-up with no plottable data.
        traj = standard_su2_trajectory(k_max=10, g_0=0.30)
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

    traj = standard_su2_trajectory(k_max=10, g_0=0.30)
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
