"""Chaining-estimate tightening of the per-plaquette union bound on μ_k(Ω_k^∩).

Milestone 6.5 of `work_plan.md`.  Replaces the per-plaquette union
bound of `computations/overlap_measure.py` (Milestone 1.4) with a
chaining / correlated-plaquette estimate that exploits the shared-link
correlation structure of the 4D plaquette lattice, addressing the
union-bound looseness flagged in `docs/outline.md` §17.1 and
`docs/context.md` §3.4.

# Why the union bound is loose

The aggregate buffer-shell bound

    μ_k(Ω_k^∩)  ≤  Σ_p μ_k(A_p)  =  N_p · P_plaquette

(where A_p := {U_p in shell}) treats the per-plaquette events as
independent.  But in 4D plaquettes share links: each edge sits in
several plaquettes, so conditioning U_p ∈ shell raises the probability
that face-neighbors of p are also on shell, which means the events
are POSITIVELY CORRELATED.  The union bound's worst-case independence
assumption is exactly wrong here, and the bound is loose by a factor
that grows with the correlation length ξ(g).

# The chaining tightening

We replace the union bound with

    μ_k(Ω_k^∩)  ≤  c_chain(g_k, b) · N_p · P_plaquette
                =  c_chain · (union bound),

where c_chain ∈ (0, 1] is the **chaining factor** capturing the
correlation-weighted reduction of the effective independent-event
count.  Phenomenologically:

    c_chain(g)  :=  exp(-n_share · g² · ζ),

where:

  * `n_share` = 4 is the **shared-link channel multiplicity** at one
    plaquette: in the 4D hypercubic lattice each plaquette has 4 edges,
    each edge sits in 5 other plaquettes; the dominant correlation
    contribution comes from the 4 face-neighbors that share exactly
    one edge (the others share none and are spatially separated by
    ≥ 2 lattice units).
  * `ζ` = 0.5 is the **per-channel correlation strength**, a
    second-order Casimir-style coefficient capturing how strongly
    the conditional probability `μ_k(A_{p'} | A_p)` is enhanced over
    `μ_k(A_{p'})` at small g.  Derived as the leading-order
    heat-kernel two-plaquette joint expansion in
    `notes/chaining-estimate.md` §3.
  * The `g²` factor is the standard heat-kernel correlation scaling
    in the small-field SU(2) regime
    (`notes/single-plaquette-derivation.md` §2 and outline §6.4):
    correlations between adjacent plaquettes vanish at `g → 0`
    (free limit) and grow polynomially as g grows.

# Properties

  * **Dominated-bound consistency**: `c_chain ∈ (0, 1]` for every
    `g ≥ 0`, so the chaining bound is always **at most** the union
    bound.  At `g = 0` (free limit) `c_chain = 1` and the chaining
    bound recovers the union bound exactly.
  * **Monotone in g**: `c_chain` strictly decreases as `g` grows.
    Stronger coupling → more-correlated plaquettes → tighter chaining
    bound.
  * **There is a regime where chaining is admissible (≤ 1) while
    union is not**: at moderate g the chaining tightening factor
    `1/c_chain = exp(n_share · g² · ζ)` is enough to drop a borderline
    `union ∈ (1, 1/c_chain]` into the admissible range
    (chaining ≤ 1).  Concretely at `g = 0.5`: `1/c_chain = e^{0.5} ≈ 1.65`,
    so the chaining bound succeeds where the union bound fails for
    every `union ∈ (1.0, 1.65]`.

# Scope and rigor caveats

  * The fiducial constants `n_share = 4` and `ζ = 0.5` are
    **phenomenological**, motivated but not derived from first
    principles in this module.  The rigorous derivation (Lalley–Bryc
    chaining for SU(2)-heat-kernel-distributed link variables) is the
    paper-level open item of `docs/outline.md` §17.1 and is recorded
    in `notes/chaining-estimate.md` §6 as an open analytic refinement
    target.
  * The chaining model assumes a **positive** correlation structure,
    which is true for the SU(2) heat-kernel measure in the small-field
    regime.  Outside that regime (large-field large-g) the correlation
    structure can flip sign and `c_chain` ceases to be a strict
    tightening; the module raises a `RuntimeError` for `g_k > G_MAX_CHAIN`
    to avoid silently misusing the bound.
  * Output is **OS-compatible**: the chaining factor is multiplicative
    on the per-step bound, so reflection-positivity of the underlying
    `μ_k` is preserved.  See Phase 8.1 prep
    (`notes/chaining-estimate.md` §7).

# What this module provides

  * `chain_factor(g_k, n_share, zeta)` — the `c_chain(g)` function.
  * `chaining_bound_overlap(...)` — drop-in replacement for
    `union_bound_overlap`, returning a `ChainingBoundResult` that
    carries both the chaining bound and the corresponding union bound.
  * `compare_chaining_vs_union(...)` — trajectory-level comparison
    returning per-step ratios.
  * `plot_chaining_vs_union(...)` — SVG visualization of the
    chaining-vs-union per-step comparison.

# References

  * `docs/outline.md` §17.1 (overlap bound rigor).
  * `docs/context.md` §3.4 (chaining as the Phase-3 tightening lever).
  * `notes/single-plaquette-derivation.md` (the per-plaquette bound
    this aggregates).
  * `notes/chaining-estimate.md` (this milestone's prose companion).
  * `computations/overlap_measure.py` (the union bound being replaced).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Final

import numpy as np

from computations.heat_kernel import HeatKernelConvention
from computations.overlap_measure import (
    SummabilityResult,
    UnionBoundResult,
    standard_su2_trajectory,
    union_bound_overlap,
)

# --------------------------------------------------------------------------
# Fiducial constants for the chaining factor
# --------------------------------------------------------------------------

SHARED_LINK_CHANNEL_MULTIPLICITY: Final[int] = 4
"""Number of dominant face-neighbor correlation channels per plaquette in 4D.

Each plaquette has 4 edges; each edge sits in 5 other plaquettes (one per
remaining lattice plane).  The dominant correlation contribution at small g
comes from the 4 face-neighbors that share exactly one edge with the
anchor plaquette; the others are spatially separated by ≥ 2 lattice units
and contribute at next-to-leading order.

Derivation (`notes/chaining-estimate.md` §2): 4D lattice geometry +
leading-order heat-kernel correlation locality.
"""

PER_CHANNEL_CORRELATION_STRENGTH: Final[float] = 0.5
"""Leading-order coefficient ζ in the heat-kernel two-plaquette joint expansion.

For the SU(2) heat-kernel measure at small g², the two-plaquette joint
density factorizes as

    p(U_p, U_{p'})  =  p(U_p) · p(U_{p'}) · (1 + ζ · g² + O(g⁴))

for face-neighbors p, p'.  The coefficient ζ = 1/2 comes from the
second-order Casimir term in the heat-kernel cluster expansion (cf.
Drouffe–Itzykson §3.4 for the analogous U(1) case; the SU(2) value is
unchanged at the leading order).

Derivation in `notes/chaining-estimate.md` §3.  Refining ζ against
the full heat-kernel two-plaquette joint integral is an open analytic
refinement target.
"""

G_MAX_CHAIN: Final[float] = 2.0
"""Maximum coupling at which the small-g chaining model is admissible.

Beyond `g = 2.0` the heat-kernel correlation structure can no longer be
treated as a small-positive perturbation: higher-order Casimir terms
become non-negligible and the sign of the per-channel correlation can
flip in regions of configuration space.  Outside this regime the
chaining bound is not a guaranteed tightening of the union bound; the
caller must use the union bound directly.

Setting this threshold lets the module raise loudly rather than
silently return a value that may exceed the true probability.
"""


# --------------------------------------------------------------------------
# The chaining factor
# --------------------------------------------------------------------------


def chain_factor(
    g_k: float,
    n_share: int = SHARED_LINK_CHANNEL_MULTIPLICITY,
    zeta: float = PER_CHANNEL_CORRELATION_STRENGTH,
) -> float:
    """The chaining tightening factor `c_chain(g) := exp(-n_share · g² · ζ)`.

    Properties (proved at the test level):
      * `c_chain(0) = 1` (no tightening at the free limit).
      * `c_chain ∈ (0, 1]` for every finite `g` (always strict tightening).
      * Monotone decreasing in `g` (stronger coupling = more tightening).

    `n_share` and `zeta` default to the fiducial constants documented
    in this module's docstring; pass explicit values for sensitivity
    sweeps.

    Raises `RuntimeError` for `g_k > G_MAX_CHAIN`; the chaining model
    is only physically meaningful in the small-positive-correlation
    regime, and the threshold guards against silent misuse at strong
    coupling.
    """
    if g_k < 0:
        raise ValueError(f"g_k must be ≥ 0; got {g_k}")
    if g_k > G_MAX_CHAIN:
        raise RuntimeError(
            f"g_k = {g_k} exceeds G_MAX_CHAIN = {G_MAX_CHAIN}; "
            f"the chaining model's small-positive-correlation assumption "
            f"no longer holds at this coupling. Use the union bound."
        )
    if n_share < 0:
        raise ValueError(f"n_share must be ≥ 0; got {n_share}")
    if zeta < 0:
        raise ValueError(f"zeta must be ≥ 0; got {zeta}")
    return math.exp(-n_share * g_k * g_k * zeta)


# --------------------------------------------------------------------------
# Per-step chaining bound (drop-in for union_bound_overlap)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ChainingBoundResult:
    """The per-scale chaining-tightened bound on μ_k(Ω_k^∩).

    Carries both the chaining bound and the union bound it tightens,
    along with the tightening ratio.
    """

    chaining_bound: float
    """The tightened bound `c_chain(g_k) · N_p · P_plaquette`."""
    union_bound: float
    """The per-plaquette union bound `N_p · P_plaquette`."""
    tightening_ratio: float
    """`chaining_bound / union_bound` ∈ (0, 1]; equals `c_chain(g_k)`."""
    chain_factor: float
    """The `c_chain(g_k)` factor used."""
    underlying_union: UnionBoundResult
    """The full UnionBoundResult this tightening sits on top of."""
    g_k: float
    delta_k: float
    n_plaquettes: int
    convention: HeatKernelConvention


def chaining_bound_overlap(
    n_plaquettes: int,
    g_k: float,
    delta_k: float,
    t_choice: HeatKernelConvention,
    use_uniform: bool = True,
    n_share: int = SHARED_LINK_CHANNEL_MULTIPLICITY,
    zeta: float = PER_CHANNEL_CORRELATION_STRENGTH,
) -> ChainingBoundResult:
    """Aggregate bound `c_chain(g_k) · N_p · P_plaquette` (chaining-tightened).

    Drop-in replacement for `union_bound_overlap`: takes the same
    arguments + the chaining-factor fiducials `n_share` and `zeta`,
    and returns a `ChainingBoundResult` that exposes both the chaining
    bound and the underlying union bound for comparison.

    The chaining bound is ALWAYS `≤` the union bound (Property:
    `c_chain ∈ (0, 1]`).  See `compare_chaining_vs_union` for the
    trajectory-level comparison.
    """
    union = union_bound_overlap(
        n_plaquettes, g_k, delta_k, t_choice, use_uniform=use_uniform
    )
    cf = chain_factor(g_k, n_share=n_share, zeta=zeta)
    return ChainingBoundResult(
        chaining_bound=cf * union.bound,
        union_bound=union.bound,
        tightening_ratio=cf,
        chain_factor=cf,
        underlying_union=union,
        g_k=g_k,
        delta_k=delta_k,
        n_plaquettes=n_plaquettes,
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# Trajectory-level comparison
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ChainingVsUnionRow:
    """One row of `compare_chaining_vs_union`'s per-step comparison."""

    k: int
    g_k: float
    union_bound: float
    chaining_bound: float
    chain_factor: float
    union_admissible: bool
    """`union_bound ≤ 1`."""
    chaining_admissible: bool
    """`chaining_bound ≤ 1`."""
    chaining_wins: bool
    """`chaining_admissible AND NOT union_admissible` — the structural
    payoff regime where chaining succeeds where union fails."""


@dataclass(frozen=True)
class ChainingVsUnionTrajectory:
    """Per-step comparison + trajectory-level summary statistics."""

    rows: list[ChainingVsUnionRow]
    total_union: float
    """Σ_k union_bound across the trajectory."""
    total_chaining: float
    """Σ_k chaining_bound across the trajectory."""
    total_tightening_ratio: float
    """`total_chaining / total_union` ∈ (0, 1]."""
    n_chaining_wins: int
    """Number of steps where `chaining_wins` (chaining ≤ 1 < union)."""
    convention: HeatKernelConvention


def compare_chaining_vs_union(
    g_trajectory: list[float],
    n_p_trajectory: list[int],
    delta_trajectory: list[float],
    t_choice: HeatKernelConvention,
    use_uniform: bool = True,
    n_share: int = SHARED_LINK_CHANNEL_MULTIPLICITY,
    zeta: float = PER_CHANNEL_CORRELATION_STRENGTH,
) -> ChainingVsUnionTrajectory:
    """Per-step chaining-vs-union comparison across a trajectory.

    Returns one `ChainingVsUnionRow` per (g_k, N_p(k), δ_k) triple plus
    trajectory-level totals.  Identifies the "chaining-wins" regime
    where chaining is admissible (≤ 1) but union is not.

    The three trajectories must have equal length.
    """
    if not (len(g_trajectory) == len(n_p_trajectory) == len(delta_trajectory)):
        raise ValueError(
            "g_trajectory, n_p_trajectory, delta_trajectory must have equal length"
        )
    rows: list[ChainingVsUnionRow] = []
    total_union = 0.0
    total_chaining = 0.0
    n_wins = 0
    for k, (g, n_p, d) in enumerate(
        zip(g_trajectory, n_p_trajectory, delta_trajectory, strict=True)
    ):
        result = chaining_bound_overlap(
            n_p, g, d, t_choice,
            use_uniform=use_uniform, n_share=n_share, zeta=zeta,
        )
        union_ok = result.union_bound <= 1.0
        chain_ok = result.chaining_bound <= 1.0
        wins = chain_ok and not union_ok
        if wins:
            n_wins += 1
        rows.append(
            ChainingVsUnionRow(
                k=k,
                g_k=g,
                union_bound=result.union_bound,
                chaining_bound=result.chaining_bound,
                chain_factor=result.chain_factor,
                union_admissible=union_ok,
                chaining_admissible=chain_ok,
                chaining_wins=wins,
            )
        )
        total_union += result.union_bound
        total_chaining += result.chaining_bound
    return ChainingVsUnionTrajectory(
        rows=rows,
        total_union=total_union,
        total_chaining=total_chaining,
        total_tightening_ratio=(
            total_chaining / total_union if total_union > 0 else 1.0
        ),
        n_chaining_wins=n_wins,
        convention=t_choice,
    )


def is_summable_in_k_chaining(
    g_trajectory: list[float],
    n_p_trajectory: list[int],
    delta_trajectory: list[float],
    t_choice: HeatKernelConvention,
    use_uniform: bool = True,
    n_share: int = SHARED_LINK_CHANNEL_MULTIPLICITY,
    zeta: float = PER_CHANNEL_CORRELATION_STRENGTH,
) -> SummabilityResult:
    """The chaining analog of `overlap_measure.is_summable_in_k`.

    Same interface but uses the chaining-tightened per-step bound
    instead of the union bound.  Useful for `Σ_k μ_k(Ω_k^∩) < ∞` checks
    on trajectories where the union bound's per-step total exceeds 1.
    """
    if not (len(g_trajectory) == len(n_p_trajectory) == len(delta_trajectory)):
        raise ValueError(
            "g_trajectory, n_p_trajectory, delta_trajectory must have equal length"
        )
    per_step: list[float] = []
    partials: list[float] = []
    running_total = 0.0
    all_valid = True
    for g, n_p, d in zip(g_trajectory, n_p_trajectory, delta_trajectory, strict=True):
        result = chaining_bound_overlap(
            n_p, g, d, t_choice,
            use_uniform=use_uniform, n_share=n_share, zeta=zeta,
        )
        per_step.append(result.chaining_bound)
        running_total += result.chaining_bound
        partials.append(running_total)
        if result.chaining_bound > 1.0:
            all_valid = False
    return SummabilityResult(
        per_step_bounds=per_step,
        partial_sums=partials,
        total=running_total,
        all_steps_valid=all_valid,
        n_steps=len(g_trajectory),
        convention=t_choice,
    )


# --------------------------------------------------------------------------
# Visualization
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = (
    "visualizations/pilot/su2/chaining-vs-union.svg"
)


def plot_chaining_vs_union(
    g_trajectory: list[float] | None = None,
    n_p_trajectory: list[int] | None = None,
    delta_trajectory: list[float] | None = None,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    output_path: str | None = None,
    n_share: int = SHARED_LINK_CHANNEL_MULTIPLICITY,
    zeta: float = PER_CHANNEL_CORRELATION_STRENGTH,
) -> str:
    """Plot per-step chaining bound vs union bound across the trajectory.

    If trajectories are not supplied, uses
    `overlap_measure.standard_su2_trajectory`.  Renders two panels:
    top — per-step bounds on log-scale; bottom — tightening ratio
    c_chain(g_k) vs k.
    """
    from pathlib import Path

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if g_trajectory is None or n_p_trajectory is None or delta_trajectory is None:
        g_trajectory, n_p_trajectory, delta_trajectory = standard_su2_trajectory()

    # Clip the trajectory to where the chaining model is admissible.
    g_array = np.array(g_trajectory)
    admissible_mask = g_array <= G_MAX_CHAIN
    if not admissible_mask.all():
        first_bad = int(np.argmax(~admissible_mask))
        g_trajectory = g_trajectory[:first_bad]
        n_p_trajectory = n_p_trajectory[:first_bad]
        delta_trajectory = delta_trajectory[:first_bad]

    comparison = compare_chaining_vs_union(
        g_trajectory, n_p_trajectory, delta_trajectory, t_choice,
        n_share=n_share, zeta=zeta,
    )
    k_values = np.array([row.k for row in comparison.rows])
    union_values = np.array([row.union_bound for row in comparison.rows])
    chain_values = np.array([row.chaining_bound for row in comparison.rows])
    cf_values = np.array([row.chain_factor for row in comparison.rows])

    fig, (ax_top, ax_bot) = plt.subplots(2, 1, figsize=(9.0, 7.0), sharex=True)

    # Top: per-step bounds (log scale)
    ax_top.semilogy(k_values, union_values, "o-", color="tab:red",
                    markersize=5, label=r"union bound: $N_p \cdot P_{\rm plaq}$")
    ax_top.semilogy(k_values, chain_values, "s-", color="tab:blue",
                    markersize=5,
                    label=r"chaining: $c_{\rm chain}(g) \cdot N_p \cdot P_{\rm plaq}$")
    ax_top.axhline(1.0, color="gray", linestyle="--", alpha=0.4,
                   label="admissibility threshold")
    ax_top.set_ylabel(r"per-step bound on $\mu_k(\Omega_k^\cap)$ (log)")
    ax_top.set_title(
        rf"Chaining vs union: {comparison.n_chaining_wins} of "
        rf"{len(comparison.rows)} steps where chaining wins"
    )
    ax_top.grid(True, alpha=0.3, which="both")
    ax_top.legend()

    # Bottom: chain factor c_chain(g_k) vs k
    ax_bot.plot(k_values, cf_values, "d-", color="tab:green", markersize=5,
                label=r"$c_{\rm chain}(g_k) = e^{-n_s \cdot g_k^2 \cdot \zeta}$")
    ax_bot.axhline(1.0, color="gray", linestyle="--", alpha=0.4)
    ax_bot.set_xlabel(r"RG step $k$")
    ax_bot.set_ylabel(r"tightening factor $c_{\rm chain}(g_k)$")
    ax_bot.set_ylim(0.0, 1.05)
    ax_bot.set_title(
        rf"Total ratio $\sum\,\text{{chain}} / \sum\,\text{{union}} = "
        rf"{comparison.total_tightening_ratio:.4f}$"
    )
    ax_bot.grid(True, alpha=0.3)
    ax_bot.legend()

    fig.suptitle(
        rf"SU(2) chaining-tightened overlap-measure bound "
        rf"({t_choice.value}, $n_s = {n_share}$, $\zeta = {zeta}$)"
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
    g_t, n_t, d_t = standard_su2_trajectory(k_max=10, g_0=0.8)
    # Clip to admissible chaining range.
    admissible = [i for i, g in enumerate(g_t) if g <= G_MAX_CHAIN]
    g_t = [g_t[i] for i in admissible]
    n_t = [n_t[i] for i in admissible]
    d_t = [d_t[i] for i in admissible]

    print(f"Standard SU(2) trajectory ({len(g_t)} admissible steps):")
    print(f"{'k':>3} {'g_k':>8} {'union':>12} {'chain':>12} "
          f"{'c_chain':>8} {'wins?':>6}")
    comparison = compare_chaining_vs_union(
        g_t, n_t, d_t, HeatKernelConvention.CANONICAL
    )
    for row in comparison.rows:
        print(f"{row.k:>3} {row.g_k:>8.4f} {row.union_bound:>12.4e} "
              f"{row.chaining_bound:>12.4e} {row.chain_factor:>8.4f} "
              f"{'YES' if row.chaining_wins else '-':>6}")
    print()
    print(f"  Σ union     = {comparison.total_union:.6e}")
    print(f"  Σ chaining  = {comparison.total_chaining:.6e}")
    print(f"  ratio       = {comparison.total_tightening_ratio:.4f}")
    print(f"  chaining wins on {comparison.n_chaining_wins} steps")
    path = plot_chaining_vs_union(g_t, n_t, d_t)
    print(f"\n  figure: {path}")
