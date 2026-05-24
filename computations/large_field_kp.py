"""Large-field Kotecký–Preiss constants for SU(2): heat-kernel character-tail derivation.

Milestone 3.2 of `work_plan.md`, post-upgrade.  Computes the large-field
KP certificate `(ρ_lf, K_lf)` for SU(2) at scale `k` from a constructive
truncation of the SU(2) heat-kernel character sum, with explicit tail
bound and cluster-expansion convergence regime.

## Status: literature-grounded synthesis with constructive Z_t bound

This module replaces the original placeholder ``K_lf = 1.0`` with a
derived value from:

  - **ρ_lf** — the rigorous per-plaquette activity-decay rate
    ``ρ_lf = -log(Z_t^upper)``, where ``Z_t^upper`` is a constructive
    upper bound on the SU(2) heat-kernel character sum

        Z_t = Σ_{2j ≥ 1} (2j+1)² · exp(-t · j(j+1)),

    truncated explicitly at ``2j ≤ J_MAX_DEFAULT`` with a geometric tail
    bound at the cutoff ratio.  Positive iff ``Z_t < 1`` (the bound
    is non-vacuous as an exponential-suppression rate).

  - **K_lf** — the cluster-expansion summability constant
    ``K_lf = q / (1 - q)`` with ``q = μ_plaq · Z_t^upper``, finite iff
    ``q < 1``.  Per [Brydges–Federbush 1978], the polymer KP sum
    ``Σ_{X ∋ p₀} |a_k^lf(X)|`` is bounded by ``K_lf`` in the convergent
    regime; infinite otherwise.

The asymptotic rate ``κ(G)/g²`` quoted in `docs/outline.md` §18.5 is
preserved as the ``rho_lf_asymptotic`` field; the strict ``rho_lf``
differs from it by ≈ ``-log 4`` in the small-``g`` limit (canonical
convention), reflecting the prefactor of the leading ``j = 1/2`` term.

## Convention audit (re-examined 2026-05-24 for 3.2-upgrade)

The character weights ``exp(-t · C_2(j))`` are *inverse-coupling weights*
in ``CANONICAL`` (``t = 1/g²``) and ``WILSON`` (``t = 2N/g²``): large
``t`` corresponds to small ``g`` and to strong suppression of non-trivial
irreps.  ``t`` here is the **activity-exponent rescaling**, not a literal
heat-kernel diffusion time (a literal diffusion-time reading would have
``t`` SMALL at small ``g`` and would carry the Haar-floor issue
documented in `notes/single-plaquette-derivation.md` §4).

For the large-field activity bound, the one-sided ``Z_t``-upper-bound
reading is what we need: ``|a^lf(X)| ≤ Z_t^{|X|}``.  The bound shrinks
as ``g`` shrinks (``Z_t → 0`` as ``t → ∞``), matching the spec form
``exp(-ρ_lf · |X|_plaq)`` in `docs/outline.md` §6.5.  The Haar-floor
issue from §1.3 does not arise here because we are bounding a polymer
activity, not a probability that has a non-vanishing Haar measure.

See `notes/heat-kernel-normalization.md` §3 (canonical-vs-Wilson
bookkeeping) and the 2026-05-24 audit note in §1.

## References

- [Seiler 1982] E. Seiler, "Gauge theories as a problem of constructive
  quantum field theory and statistical mechanics", Lecture Notes in
  Physics 159, Springer 1982.  Plaquette-polymer connectivity bound
  ``μ_plaq ≤ 5d - 4 = 16`` for d-dimensional cubic lattice (d = 4).
- [DrouffeItzykson1978] J.-M. Drouffe and C. Itzykson, "Lattice gauge
  fields", Phys. Rep. 38 (1978), 133–175.  Heat-kernel character
  expansion for compact gauge groups.
- [ItzyksonDrouffe1989] C. Itzykson and J.-M. Drouffe, *Statistical
  Field Theory* (Vol. 1 & 2), Cambridge Monographs on Mathematical
  Physics, Cambridge University Press 1989.  Standard textbook
  treatment of the heat-kernel character expansion.
- [GlimmJaffe1987] J. Glimm and A. Jaffe, *Quantum Physics: A
  Functional Integral Point of View* (2nd ed., Springer 1987), Ch. 18.
  Polymer cluster expansion and convergence criteria.
- [BrydgesFederbush1978] D. Brydges and P. Federbush, "A new form of
  the Mayer expansion in classical statistical mechanics", J. Math.
  Phys. 19 (1978), 2064–2067.  Cluster-expansion convergence theorem.

See `notes/fiducials_notes.md` §3 / §4 for the project-wide audit of
`MU_PLAQUETTE_4D` and `J_MAX_DEFAULT`; BibTeX entries are in
`formal/references.bib`.  The specific value ``μ_plaq = 5d - 4 = 16``
for `d = 4` is widely cited in lattice gauge theory but the project's
2026-05-24 web-search pass did not directly verify it against a
primary source verbatim — `MU_PLAQUETTE_4D` is therefore marked as a
literature-shape fiducial pending direct paper consultation.

## Structural independence from small-field

Per the [P2.3-addendum] encoded-but-unverified prediction
(``Obligation_lf`` takes no ``sf_part`` input), the large-field
derivation is structurally independent of the small-field one.  This
module imports ``small_field_kp`` for nothing; ``Z_t``, ``μ_plaq``, and
``K_lf`` are functions of ``(g_k, t_choice)`` alone.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import (
    C_2_SU2_FUNDAMENTAL,
    HeatKernelConvention,
    kappa_from_casimir,
)

# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------

J_MAX_DEFAULT: Final[int] = 12
"""Default truncation ``2j_max`` for the SU(2) character sum ``Z_t``.

``j`` ranges over half-integers; ``2j_max = 12`` means we sum
``2j = 1, 2, …, 12`` (irreps from spin 1/2 up to spin 6).  For
``t ≥ 0.5`` (canonical ``g ≤ √2`` or Wilson ``g ≤ 2√2``), the geometric
tail bound below the truncation is small and ``Z_t^upper`` is tight to
better than one part in ``1e-10`` of the value.

For ``t < 0.5`` (very strong coupling) the tail-ratio test below may
fail and the tail bound is reported as ``+∞`` — in that regime ``Z_t``
is far above the convergence threshold anyway, so ``K_lf = ∞`` is
the correct (vacuous) result.
"""

MU_PLAQUETTE_4D: Final[float] = 16.0
"""Plaquette-connectivity ``μ_plaq`` for the d = 4 cubic lattice.

Per [Seiler 1982] / [Drouffe–Itzykson 1989]: the number of connected
plaquette-polymers of size ``n`` containing a fixed plaquette on a
d-dimensional cubic lattice is bounded by ``(5d - 4)^n``.  For
``d = 4``: ``16^n``.  This is a fiducial literature value with the
cited form; specific numerical refinement (tighter polymer-counting
bounds) is deferred to a future analytic upgrade.

See `notes/fiducials_notes.md` §3 for the project-wide audit: the
``5d - 4`` formula is widely cited in lattice gauge theory but was not
verified verbatim against a primary source in the 2026-05-24 web-search
pass.  A rigorously-derivable alternative is
``MU_PLAQUETTE_CONSERVATIVE_4D`` below.
"""

MU_PLAQUETTE_CONSERVATIVE_4D: Final[float] = 8.0 * math.e
"""**Deprecated as "BF-conservative".** ``8e ≈ 21.746`` at d = 4.

The original claim that ``8e`` is BF-conservative for plaquette polymers
"a fortiori, because plaquettes have fewer neighbours than sites" is
**not correct**: the 4D plaquette edge-neighbour degree is 20
(``plaquette_edge_neighbor_count(4)``), strictly *greater* than the
2d = 8 site-neighbour degree.  The Brydges–Federbush universal bound
``μ ≤ e · max-degree`` applied directly to plaquette polymers gives
``e · 20 ≈ 54.4``, not ``8e``.

The constant is preserved here under its historical name for
backwards compatibility (existing callers, tests, sweep history).  For
a genuinely BF-conservative bound, use
``MU_PLAQUETTE_BF_CONSERVATIVE_4D`` below.

The 8e value is still meaningful as a **site-bound transfer**: it
correctly bounds site-polymer connectivity on Z^4 per
[Brydges–Federbush 1978].  Whether it bounds plaquette-polymer
connectivity under any non-trivial transfer map (e.g., centroid
sublattice with a non-standard adjacency) is an open question; the
current code makes no such claim.

See ``notes/fiducials_notes.md`` §3.1 / §3.2 for the audit and the
corrected derivation.
"""


MU_PLAQUETTE_4D_LOG: Final[float] = math.log(MU_PLAQUETTE_4D)
"""``log μ_plaq = log 16 ≈ 2.7726``.  The cluster-expansion convergence
threshold on the activity rate: ``ρ_lf > log μ_plaq`` is necessary for
``K_lf`` to be finite.
"""


def plaquette_edge_neighbor_count(d: int) -> int:
    """Direct combinatorial count of edge-neighbors of a $d$-dim plaquette.

    A plaquette in $d$-dim has 4 edges; each edge lies in $2(d-1)$
    plaquettes total ($d-1$ perpendicular directions $\\times$ 2 sides),
    of which 1 is the current plaquette, leaving $2d - 3$ other
    plaquettes per edge.  Total: $4 (2d - 3) = 8d - 12$ edge-neighbors.

    Spot values:
      * $d = 2$: $4$
      * $d = 3$: $12$
      * $d = 4$: $20$

    **Audit use** (``notes/fiducials_notes.md`` §3.1, 2026-05-25): the
    Brydges–Federbush universal bound for connected n-subgraphs of a
    max-degree-$\\Delta$ graph gives $\\mu \\le e \\cdot \\Delta$, so
    the direct-count BF bound for ``MU_PLAQUETTE_4D`` is
    ``e * plaquette_edge_neighbor_count(4) ≈ 54.4`` — strictly looser
    than Seiler's literature 16 and the project's conservative 8e fallback.
    This function exposes the direct count for sanity-checking;
    it does NOT replace ``MU_PLAQUETTE_4D``.

    Raises ``ValueError`` for $d < 2$ (no plaquettes in 1D or 0D).
    """
    if d < 2:
        raise ValueError(f"plaquettes require d ≥ 2; got d = {d}")
    return 8 * d - 12


def mu_plaquette_bf_conservative(d: int) -> float:
    """Genuinely-BF-conservative bound on plaquette-polymer connectivity
    at dimension ``d``: ``e · (8d - 12)``.

    The Brydges–Federbush universal bound: for a graph with max-degree
    ``Δ``, the cluster-expansion convergence rate is bounded by
    ``e · Δ``.  Applied to the plaquette-edge-adjacency graph at
    dimension ``d`` (max-degree ``8d - 12`` from
    ``plaquette_edge_neighbor_count``):

        μ_plaq^{BF}(d)  =  e · (8d - 12).

    Spot values:
      * d = 2: ``4e ≈ 10.873``
      * d = 3: ``12e ≈ 32.619``
      * d = 4: ``20e ≈ 54.366``

    This is the **honest** rigorous-from-direct-count alternative to the
    Seiler-cited (but unverified) ``MU_PLAQUETTE_4D = 16``.  Strictly
    looser than ``16`` (the literature value depends on refinements
    beyond the BF universal bound), but truly conservative — derivable
    from first principles, no paper-specific argument required.

    Replaces ``MU_PLAQUETTE_CONSERVATIVE_4D = 8e`` as the project's
    preferred genuinely-conservative fallback; the 8e value is the
    site-bound, **not** a true plaquette-polymer BF-conservative bound
    (the original "plaquettes have fewer neighbours than sites"
    justification is inverted in 4D: plaquette degree 20 > site
    degree 8 — see ``notes/fiducials_notes.md`` §3.1).

    Use cases:
      * Phase-3 audit margin: run the pilot at this μ to confirm
        closure under the genuinely-rigorous upper bound.
      * Sensitivity-sweep upper edge: the largest μ the project will
        defend without paper-specific refinements.
    """
    if d < 2:
        raise ValueError(f"plaquettes require d ≥ 2; got d = {d}")
    return math.e * float(plaquette_edge_neighbor_count(d))


MU_PLAQUETTE_BF_CONSERVATIVE_4D: Final[float] = mu_plaquette_bf_conservative(4)
"""**Genuinely-BF-conservative** plaquette-polymer μ at d = 4: ``20e ≈ 54.366``.

The project's preferred rigorous-fallback for ``MU_PLAQUETTE_4D``.
Derivation: ``e · 20`` where 20 = ``plaquette_edge_neighbor_count(4)``
(4 edges × 5 other plaquettes per edge in 4D, the direct combinatorial
count).  See ``mu_plaquette_bf_conservative`` and
``notes/fiducials_notes.md`` §3.2.

**Pilot impact** (canonical convention, K = 3):
  * Default ``MU_PLAQUETTE_4D = 16``:                   ``g_max_lf ≈ 0.4245``.
  * Site-bound ``MU_PLAQUETTE_CONSERVATIVE_4D = 8e``:   ``g_max_lf ≈ 0.4098``.
  * Genuine BF ``MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e``: ``g_max_lf ≈ 0.374``.

Switching to the genuine-BF default shrinks the pilot lf-window by ~12%
vs the literature default, but the small-field sf-window (≈ 0.40) is
the binding constraint on the SU(2) pilot, so pilot closure at the
canonical ``g_0 = 0.30`` wire-in is essentially unchanged.
"""


# --------------------------------------------------------------------------
# Heat-kernel character sum with constructive tail bound
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class CharacterTailSum:
    """Rigorous upper bound on the SU(2) character sum ``Z_t``.

    ``Z_t := Σ_{2j ≥ 1} (2j+1)² · exp(-t · j(j+1))``.

    Fields:
      * ``partial_sum`` — explicit sum of terms ``2j ∈ {1, …, j_max_int}``.
      * ``tail_bound`` — geometric upper bound on the truncated tail
        (``+∞`` when the ratio test fails).
      * ``upper_bound`` — ``partial_sum + tail_bound``; a rigorous upper
        bound on the actual ``Z_t``.
      * ``tail_ratio`` — the geometric ratio at the cutoff; the bound is
        a true geometric series only when ``tail_ratio < 1``.
      * ``tail_finite`` — True iff ``tail_ratio < 1``.
      * ``j_max_int`` — the ``2j`` truncation.
      * ``t`` — the heat-kernel time used.
    """

    partial_sum: float
    tail_bound: float
    upper_bound: float
    tail_ratio: float
    tail_finite: bool
    j_max_int: int
    t: float


def _t_from_g_su2(g_k: float, t_choice: HeatKernelConvention) -> float:
    """Heat-kernel time ``t`` for SU(2) under the given convention.

    ``CANONICAL: t = 1/g²``.  ``WILSON: t = 2N/g² = 4/g²`` (N = 2).
    Raises for ``MANTON`` (bound shape mismatch).
    """
    if t_choice is HeatKernelConvention.CANONICAL:
        return 1.0 / (g_k * g_k)
    if t_choice is HeatKernelConvention.WILSON:
        return 4.0 / (g_k * g_k)  # 2N = 4 for SU(2)
    raise ValueError(
        f"Manton convention has bound shape exp(-c·g²); Z_t in this module "
        f"requires CANONICAL or WILSON.  Got: {t_choice!r}"
    )


def heat_kernel_character_tail_Z(
    g_k: float,
    t_choice: HeatKernelConvention,
    j_max_int: int = J_MAX_DEFAULT,
) -> CharacterTailSum:
    """Rigorous upper bound on the SU(2) character sum ``Z_t``.

    ``Z_t = Σ_{2j ≥ 1} (2j+1)² · exp(-t · j(j+1))``.

    Truncates the sum at ``2j ≤ j_max_int`` and adds a geometric tail
    bound from the worst-case (largest) ratio of successive terms at the
    cutoff.  Term ratio:

        f(n+1) / f(n)
            = ((n+2)/(n+1))² · exp(-t · (2n+3) / 4),   n = 2j.

    For ``n ≥ j_max_int`` this ratio decreases in ``n`` (both factors
    decrease), so the worst case is at ``n = j_max_int``.  When that
    worst-case ratio is ``< 1``, the tail is bounded by a geometric
    series; otherwise ``tail_bound = +∞`` (rigorous, vacuous).
    """
    if g_k <= 0:
        raise ValueError(f"g_k must be positive; got {g_k}")
    if j_max_int < 1:
        raise ValueError(f"j_max_int must be ≥ 1; got {j_max_int}")

    t = _t_from_g_su2(g_k, t_choice)

    # Sum 2j = 1, 2, …, j_max_int.
    partial = 0.0
    for two_j in range(1, j_max_int + 1):
        j = two_j / 2.0
        d_j = two_j + 1
        partial += (d_j * d_j) * math.exp(-t * j * (j + 1.0))

    # Geometric tail-bound ratio at 2j = j_max_int.
    n = j_max_int
    ratio = ((n + 2.0) / (n + 1.0)) ** 2 * math.exp(-t * (2 * n + 3) / 4.0)

    if ratio < 1.0:
        # First-omitted term × 1/(1 - ratio) bounds the tail.
        first_omitted_2j = j_max_int + 1
        j_omit = first_omitted_2j / 2.0
        d_omit = first_omitted_2j + 1
        first_omitted = (d_omit * d_omit) * math.exp(
            -t * j_omit * (j_omit + 1.0)
        )
        tail = first_omitted / (1.0 - ratio)
        tail_finite = True
    else:
        tail = float("inf")
        tail_finite = False

    upper = partial + tail

    return CharacterTailSum(
        partial_sum=partial,
        tail_bound=tail,
        upper_bound=upper,
        tail_ratio=ratio,
        tail_finite=tail_finite,
        j_max_int=j_max_int,
        t=t,
    )


# --------------------------------------------------------------------------
# Result dataclass
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class LargeFieldKP:
    """The large-field KP certificate ``(ρ_lf, K_lf)`` at one RG scale.

    Fields:
      * ``rho_lf`` — strict per-plaquette activity-decay rate
        ``-log(Z_t_upper)``.  Positive iff the character sum is ``< 1``
        (the activity bound is non-vacuous as exponential suppression).
      * ``rho_lf_asymptotic`` — leading-asymptotic rate ``κ(G)/g²`` from
        outline §18.5 (``κ = 3/4`` canonical, ``3`` Wilson).  Equal to
        the small-``g`` limit of ``rho_lf + log 4`` (canonical).
      * ``K_lf`` — cluster-expansion summability constant.  Finite iff
        ``MU_PLAQUETTE_4D · Z_t_upper < 1`` (cluster expansion converges).
      * ``convergent`` — True iff ``q := μ_plaq · Z_t_upper < 1``.
      * ``Z_t_upper`` — rigorous upper bound on
        ``Σ (2j+1)² · exp(-t · C_2(j))``, from the character-tail truncation.
      * ``g_k``, ``scale_k``, ``convention`` — context.
      * ``provenance`` — per-constant origin with literature citations.
    """

    rho_lf: float
    rho_lf_asymptotic: float
    K_lf: float
    convergent: bool
    Z_t_upper: float
    g_k: float
    scale_k: int
    convention: HeatKernelConvention
    provenance: dict[str, str]


# --------------------------------------------------------------------------
# Compute the certificate
# --------------------------------------------------------------------------


def compute_large_field_kp(
    g_k: float,
    scale_k: int = 0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    j_max_int: int = J_MAX_DEFAULT,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> LargeFieldKP:
    """Compute ``(ρ_lf, K_lf)`` via heat-kernel character-tail truncation.

    Per [Drouffe–Itzykson 1989] / [Glimm–Jaffe 1987] §18:

        |a_k^lf(X)|  ≤  Z_t^{|X|_plaq}

    (per-plaquette character-tail bound; ``Z_t`` is the non-trivial-irrep
    sum), equivalently ``|a_k^lf(X)| ≤ exp(-ρ_lf · |X|_plaq)`` with
    ``ρ_lf := -log Z_t`` per outline §6.5's spec form.

    Per [Brydges–Federbush 1978] cluster-expansion convergence on a 4D
    cubic lattice with plaquette connectivity ``μ = 16`` ([Seiler 1982]):

        Σ_{X ∋ p₀} |a_k^lf(X)|  ≤  Σ_n μ^n · e^{-ρ_lf · n}  =  q / (1 - q)

    with ``q := μ · Z_t``.  Converges iff ``q < 1``, i.e., ``Z_t < 1/μ
    = 1/16``.  Estimated thresholds (small-``g`` leading asymptotic):
    canonical ``g_max ≈ √(3 / (4 · log 64)) ≈ 0.4247``; Wilson
    ``g_max ≈ √(3 / log 64) ≈ 0.849``.

    ``Z_t`` is computed via ``heat_kernel_character_tail_Z`` as a
    constructive upper bound (partial sum + geometric tail).  The
    returned ``rho_lf`` is the corresponding strict *lower* bound on the
    activity rate; ``K_lf`` is the corresponding *upper* bound on the
    cluster-expansion sum.
    """
    if g_k <= 0:
        raise ValueError(f"g_k must be positive; got {g_k}")
    if scale_k < 0:
        raise ValueError(f"scale_k must be non-negative; got {scale_k}")
    if t_choice is HeatKernelConvention.MANTON:
        raise ValueError(
            "Manton's exp(-c·g²) shape mismatches the large-field bound "
            "shape exp(-ρ_lf · |X|_plaq).  Use CANONICAL or WILSON."
        )
    if mu_plaq <= 0:
        raise ValueError(f"mu_plaq must be positive; got {mu_plaq}")

    # Step 1: Z_t with rigorous truncation tail bound.
    Z = heat_kernel_character_tail_Z(g_k, t_choice, j_max_int)

    # Step 2: ρ_lf (strict activity rate).  Negative when Z_t > 1; -∞ when
    # the tail bound is non-finite; +∞ in the degenerate Z_t → 0 limit.
    if Z.upper_bound == float("inf"):
        rho_lf = -float("inf")
    elif Z.upper_bound > 0.0:
        rho_lf = -math.log(Z.upper_bound)
    else:
        rho_lf = float("inf")  # Z_t == 0 (effectively t → ∞)

    # Step 3: ρ_lf_asymptotic (leading form per outline §18.5).
    kappa = kappa_from_casimir(
        C_2_min=float(C_2_SU2_FUNDAMENTAL), N=2, t_choice=t_choice
    )
    rho_lf_asymptotic = kappa / (g_k * g_k)

    # Step 4: K_lf via cluster-expansion convergence (Brydges–Federbush 1978).
    q = mu_plaq * Z.upper_bound
    if math.isfinite(q) and q < 1.0:
        K_lf = q / (1.0 - q)
        convergent = True
    else:
        K_lf = float("inf")
        convergent = False

    # Estimated convergence threshold from the small-g leading asymptotic.
    convention_factor = 4.0 if t_choice is HeatKernelConvention.WILSON else 1.0
    log_threshold_g_sq = math.log(4.0) + math.log(mu_plaq)
    g_max_estimate = math.sqrt(
        (float(C_2_SU2_FUNDAMENTAL) * convention_factor) / log_threshold_g_sq
    )

    provenance = {
        "rho_lf": (
            f"DERIVED from heat-kernel character tail: "
            f"ρ_lf = -log(Z_t^upper) = {rho_lf:.4e}.  "
            f"Z_t = Σ (2j+1)²·exp(-t·j(j+1)) with rigorous truncation "
            f"at 2j ≤ {j_max_int} + geometric tail bound; "
            f"Z_t^upper = {Z.upper_bound:.6e} at t = {Z.t:.4f} "
            f"({t_choice.value} convention)."
        ),
        "rho_lf_asymptotic": (
            f"LEADING ASYMPTOTIC: κ({t_choice.value})/g_k² = "
            f"{kappa:.4f} / {g_k:.4f}² = {rho_lf_asymptotic:.6e}.  "
            f"κ from smallest nonzero Casimir C_2(1/2) = 3/4 "
            f"(outline §18.5 verbatim)."
        ),
        "K_lf": (
            f"DERIVED via Brydges–Federbush cluster-expansion: "
            f"K_lf = q/(1-q) with q = μ_plaq · Z_t^upper = "
            f"{mu_plaq:.4f}·{Z.upper_bound:.4e} = {q:.4e}.  "
            f"{'Convergent' if convergent else 'NOT convergent (K_lf = ∞)'}; "
            f"K_lf = {K_lf:.4e}.  "
            f"μ_plaq = {mu_plaq:.4f} "
            f"({'literature-shape (5d-4 = 16, Seiler 1982)' if mu_plaq == MU_PLAQUETTE_4D else 'site-bound 8e (NOT a true plaquette BF-conservative; see fiducials_notes §3.1)' if mu_plaq == MU_PLAQUETTE_CONSERVATIVE_4D else 'BF-conservative 20e (genuine plaquette-BF bound from direct count)' if mu_plaq == MU_PLAQUETTE_BF_CONSERVATIVE_4D else 'custom override'})."
        ),
        "convergent": (
            f"q = μ_plaq · Z_t^upper = {q:.4e} "
            f"{'<' if convergent else '≥'} 1: {convergent}.  "
            f"Estimated threshold g_max ≈ {g_max_estimate:.4f} "
            f"({t_choice.value}) from small-g leading asymptotic "
            f"(Z_t ≈ 4·exp(-κ/g²))."
        ),
        "Z_t_upper": (
            f"partial_sum = {Z.partial_sum:.6e} (2j ≤ {j_max_int}); "
            f"tail_bound = {Z.tail_bound:.6e} "
            f"(geometric, ratio = {Z.tail_ratio:.4e}, "
            f"{'finite' if Z.tail_finite else 'NON-FINITE → ∞'}); "
            f"upper = {Z.upper_bound:.6e}."
        ),
        "convention": f"{t_choice.value}; t = {Z.t:.4f}",
        "scale_k": str(scale_k),
        "status": (
            "DERIVED: ρ_lf and K_lf computed constructively via heat-kernel "
            "character-tail truncation + Brydges–Federbush cluster expansion. "
            "μ_plaq = 16 is a fiducial literature value (Seiler 1982)."
        ),
    }

    return LargeFieldKP(
        rho_lf=rho_lf,
        rho_lf_asymptotic=rho_lf_asymptotic,
        K_lf=K_lf,
        convergent=convergent,
        Z_t_upper=Z.upper_bound,
        g_k=g_k,
        scale_k=scale_k,
        convention=t_choice,
        provenance=provenance,
    )


# --------------------------------------------------------------------------
# Per-step degradation budget ε_lf
# --------------------------------------------------------------------------


def eps_lf(
    g_k: float,
    g_k_next: float,
    t_choice: HeatKernelConvention,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> float:
    """Per-step ``ε_lf`` budget: ``ρ_lf(k+1) ≥ ρ_lf(k) - ε_lf(b, g_k)``.

    Computed as ``max(0, ρ_lf(k) - ρ_lf(k+1))`` when both rates are
    finite; returns ``+∞`` when either rate is non-finite (which signals
    the character-tail truncation diverged at the corresponding ``g_k``).
    """
    kp_k = compute_large_field_kp(g_k, t_choice=t_choice, mu_plaq=mu_plaq)
    kp_next = compute_large_field_kp(g_k_next, t_choice=t_choice, mu_plaq=mu_plaq)
    if not math.isfinite(kp_k.rho_lf) or not math.isfinite(kp_next.rho_lf):
        return float("inf")
    return max(0.0, kp_k.rho_lf - kp_next.rho_lf)


# --------------------------------------------------------------------------
# Trajectory
# --------------------------------------------------------------------------


def first_few_rg_steps(
    g_trajectory: list[float],
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> list[LargeFieldKP]:
    """Compute the large-field KP certificate at each scale."""
    return [
        compute_large_field_kp(g, scale_k=k, t_choice=t_choice, mu_plaq=mu_plaq)
        for k, g in enumerate(g_trajectory)
    ]


# --------------------------------------------------------------------------
# Convergence threshold helper
# --------------------------------------------------------------------------


def convergence_threshold_g_lf(
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    j_max_int: int = J_MAX_DEFAULT,
    g_search_range: tuple[float, float] = (1e-3, 5.0),
    tolerance: float = 1e-6,
    max_iter: int = 200,
    mu_plaq: float = MU_PLAQUETTE_4D,
) -> float:
    """Largest ``g_k`` (within ``g_search_range``) for which ``K_lf`` is finite.

    Convergence is monotone in ``g``: smaller ``g`` ↔ larger ``t`` ↔
    smaller ``Z_t`` ↔ smaller ``q`` ↔ more likely ``q < 1``.  Uses
    bisection.  Returns the lower edge of the range if no ``g_k`` in
    the range is convergent; the upper edge if every ``g_k`` converges.

    Pass ``mu_plaq=MU_PLAQUETTE_CONSERVATIVE_4D`` (= 8e) for the rigorous
    site-connectivity fallback per `notes/fiducials_notes.md` §3 option 2.
    """
    g_low, g_high = g_search_range
    if not compute_large_field_kp(
        g_low, t_choice=t_choice, j_max_int=j_max_int, mu_plaq=mu_plaq,
    ).convergent:
        return g_low
    if compute_large_field_kp(
        g_high, t_choice=t_choice, j_max_int=j_max_int, mu_plaq=mu_plaq,
    ).convergent:
        return g_high
    for _ in range(max_iter):
        g_mid = 0.5 * (g_low + g_high)
        if compute_large_field_kp(
            g_mid, t_choice=t_choice, j_max_int=j_max_int, mu_plaq=mu_plaq,
        ).convergent:
            g_low = g_mid
        else:
            g_high = g_mid
        if g_high - g_low < tolerance:
            break
    return g_low


if __name__ == "__main__":
    from computations.overlap_measure import standard_su2_trajectory

    g_threshold_canon = convergence_threshold_g_lf()
    g_threshold_wilson = convergence_threshold_g_lf(HeatKernelConvention.WILSON)
    print("Large-field KP — heat-kernel character-tail derivation")
    print("=" * 65)
    print(f"MU_PLAQUETTE_4D                     = {MU_PLAQUETTE_4D}")
    print(f"J_MAX_DEFAULT (2j truncation)        = {J_MAX_DEFAULT}")
    print(f"Convergence threshold g_max (canon.) = {g_threshold_canon:.4f}")
    print(f"                          (Wilson)   = {g_threshold_wilson:.4f}")
    print()
    print("Per-scale large-field KP on standard trajectory (g_0 = 1.2):")
    print(f"{'k':>3} {'g_k':>8} {'rho_lf':>10} {'rho_asy':>10} "
          f"{'K_lf':>14} {'conv?':>6}")
    traj = standard_su2_trajectory(k_max=5)
    g_traj: list[float] = traj[0]
    for kp in first_few_rg_steps(g_traj):
        K_str = f"{kp.K_lf:.4e}" if math.isfinite(kp.K_lf) else "∞"
        print(
            f"{kp.scale_k:>3} {kp.g_k:>8.4f} {kp.rho_lf:>10.4f} "
            f"{kp.rho_lf_asymptotic:>10.4f} {K_str:>14} "
            f"{str(kp.convergent):>6}"
        )
    print()
    print("Per-scale at convergent g_k values:")
    for g in (0.05, 0.1, 0.2, 0.3, 0.4):
        kp = compute_large_field_kp(g)
        K_str = f"{kp.K_lf:.4e}" if math.isfinite(kp.K_lf) else "∞"
        print(
            f"     g={g:>5.2f}  ρ_lf={kp.rho_lf:>8.2f}  "
            f"ρ_asy={kp.rho_lf_asymptotic:>8.2f}  K_lf={K_str:>14}  "
            f"conv={kp.convergent}"
        )
    print()
    print("Provenance (g = 0.2, canonical):")
    sample = compute_large_field_kp(0.2)
    for key, val in sample.provenance.items():
        print(f"  {key}: {val}")
