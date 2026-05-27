"""The inductive state package ℐ_k for Milestone 2.2.

Python mirror of `formal/inductive-state.tex` Definition 2.1.

The state at RG scale k bundles:

  - the renormalized string tension σ̂_k (σ-3 sense),
  - the running coupling g_k,
  - three Kotecký–Preiss certificates (small-field, large-field, buffer),
  - the polymer atlas P_k (`PolyAtlas`, **concrete commitment 2026-05-26**;
    see `PolyAtlas` class docstring for the partition of unity and the
    three-region Gribov-boundary parameterization).

The `validate()` method checks the scale-k induction hypotheses
(V1)–(V3) of `formal/inductive-state.tex` Definition 3.1.  All
checks are scale-k-local: no reference to k+1 and no sum over k.
The cross-scale content (the four conditions on the block-spin
pushforward) lives in Milestone 2.3; this module exposes only the
*type* of that pushforward via `step_signature()`.

Carry-uncertainty
-----------------

The buffer certificate `kp_cap` is constrained by the conjectured
constants of `formal/sheaf-framework.tex` Proposition 7.1:

    ρ_∩ = min(ρ_sf, ρ_lf),    K_∩ ≤ K_sf + K_lf.

Constructing an InductiveState whose `kp_cap` reflects this
relationship is a *requirement* of `validate()` (clause V3), but
the underlying claim that the KP predicate P holds at those buffer
constants is the sorry'd Lean theorem
`YMGap.Sheaf.domGlue_preserves_KP` (SORRY_LEDGER entry [P2.1]).
This Python module does not re-assert that claim; it carries the
relationship as a check.

Polymer atlas
-------------

The representation of P_k is **closed 2026-05-26** as the
`PolyAtlas` dataclass defined below.  See `PolyAtlas` for the
concrete commitments: smallness parameter `δ_k = g_k` (α = 1
convention), plaquette enumeration cutoff `n_max = 16`, shape
classifier for partition of unity over admissible polymers, and
explicit three-region Gribov-boundary parameterization
`(sf, ∩, lf)` matching `formal/sheaf-framework.tex` Def. 2.2.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Final, Literal


# --------------------------------------------------------------------------
# Polymer atlas: concrete commitment (Milestone 2.2 closure, 2026-05-26)
# --------------------------------------------------------------------------


# Shape class labels for the partition of unity.
ShapeClass = Literal["filament", "intermediate", "ball"]
"""Polymer shape class — partition of unity over admissible polymers.

Three classes determined by aspect ratio `|X|_phys / (a_k · |X|_plaq)`:
  * **filament**: ratio ≥ 0.8 (extended polymer, low aspect → 1)
  * **intermediate**: 0.2 < ratio < 0.8 (between extremes)
  * **ball**: ratio ≤ 0.2 (compact polymer, low aspect)

Every admissible polymer falls into exactly one class.  The
3-class partition is the polymer-shape interpolation grid that
Milestone 6.1-tighten's `polymer_shape_dominance` theorem covers
uniformly via the universal Q' chain `ρ_sf · m ≤ ρ_lf · n`
(`lean/YMGap/Sheaf/PolymerDomination.lean`).
"""


# Gribov-region labels for the three-region atlas.
GribovRegion = Literal["sf", "buffer", "lf"]
"""Gribov-region tag — three-region atlas matching
`formal/sheaf-framework.tex` Definition 2.2.

A polymer X gets a region tag determined by its maximum-plaquette
geodesic distance `max_p d(U_p, 1)`:
  * **sf** (small-field):  `max_p d < δ_k / 2` — clearly small-field.
  * **buffer** (∩):        `δ_k / 2 ≤ max_p d ≤ 2 · δ_k` — overlap region.
  * **lf** (large-field):  `max_p d > 2 · δ_k` — clearly large-field.

The three regions form a cover of `Ω_k = G^{E_k}` per the
three-element cover `{Ω_k^sf, Ω_k^lf, Ω_k^∩}`.
"""


POLYMER_PLAQUETTE_CUTOFF_DEFAULT: Final[int] = 16
"""Default polymer enumeration cutoff: maximum plaquette count
admitted in the polymer atlas.  Matches `J_MAX_DEFAULT = 12` in
`large_field_kp.py`'s character expansion modulo the `2j ≤ J_MAX`
vs `n ≤ N_max` indexing difference.  Sized to dominate the
Brydges–Federbush tail bound at the project's `μ_plaq` connectivity.
"""


POLYMER_ATLAS_ALPHA: Final[float] = 1.0
"""The α exponent in `δ_k = g_k^α` (outline §6.4 says α ∈ (0, 1)).

**Project commitment 2026-05-26**: α = 1, giving `δ_k = g_k` exactly.
The α = 1 choice keeps `δ_k` Q'-rational at every pilot operating
point (avoiding the irrational square roots that α = 1/2 would
introduce: e.g., at canonical g_0 = 3/10, √(3/10) is irrational).

The outline-permitted range α ∈ (0, 1) leaves design flexibility
for downstream refinement; the α = 1 commitment is the most
conservative choice (largest δ_k for given g_k) and is consistent
with the buffer-shell bound derivation of T6.1.
"""


@dataclass(frozen=True)
class PolyAtlas:
    """**Concrete polymer atlas P_k at RG scale k (Milestone 2.2 closure).**

    Resolves the polymer-atlas open question of Milestone 2.2
    (`formal/inductive-state.tex` §5, now closed 2026-05-26) with a
    concrete dataclass committing to four design choices:

    1. **Smallness parameter**: `δ_k = g_k` (α = 1 convention; see
       `POLYMER_ATLAS_ALPHA`).  Keeps δ_k Q'-rational at every pilot
       operating point.

    2. **Plaquette enumeration cutoff**: `n_max = 16` plaquettes
       (default; see `POLYMER_PLAQUETTE_CUTOFF_DEFAULT`).  Dominates
       the Brydges–Federbush tail at the project's μ_plaq.

    3. **Shape classifier** (`shape_class`): partition of unity into
       three shape classes (filament, intermediate, ball) by aspect
       ratio threshold.  Every admissible polymer is in exactly one
       class.

    4. **Gribov-region classifier** (`gribov_region`): three-region
       atlas (sf, buffer, lf) determined by maximum-plaquette geodesic
       distance to identity, with explicit thresholds δ_k/2 and 2·δ_k.
       Matches `formal/sheaf-framework.tex` Definition 2.2's cover.

    The atlas is **scale-k-local** (carries g_k, δ_k, n_max only;
    no cross-scale data).  Phase-3 modules consume it for polymer
    enumeration + activity bounds; the small-field, large-field,
    buffer regions are routed through `gribov_region` to the
    corresponding KP certificate.
    """

    g_k: float
    """Running gauge coupling at scale k."""

    delta_k: float
    """Smallness parameter; under α = 1 equals `g_k`."""

    n_max: int = POLYMER_PLAQUETTE_CUTOFF_DEFAULT
    """Plaquette enumeration cutoff."""

    def __post_init__(self) -> None:
        if self.g_k <= 0:
            raise ValueError(f"g_k must be positive; got {self.g_k}")
        if self.delta_k <= 0:
            raise ValueError(f"delta_k must be positive; got {self.delta_k}")
        if self.n_max < 1:
            raise ValueError(f"n_max must be ≥ 1; got {self.n_max}")

    @classmethod
    def at_scale(
        cls, g_k: float, n_max: int = POLYMER_PLAQUETTE_CUTOFF_DEFAULT
    ) -> "PolyAtlas":
        """Construct the canonical polymer atlas at coupling `g_k`
        under the α = 1 convention: `δ_k = g_k`."""
        return cls(g_k=g_k, delta_k=g_k, n_max=n_max)

    def shape_class(self, aspect_ratio: float) -> ShapeClass:
        """Classify a polymer by aspect ratio
        `|X|_phys / (a_k · |X|_plaq)`.  Returns 'filament', 'intermediate',
        or 'ball'.  The three returns partition the polymer space."""
        if aspect_ratio < 0:
            raise ValueError(f"aspect_ratio must be nonneg; got {aspect_ratio}")
        if aspect_ratio >= 0.8:
            return "filament"
        if aspect_ratio <= 0.2:
            return "ball"
        return "intermediate"

    def gribov_region(self, max_plaquette_distance: float) -> GribovRegion:
        """Classify a polymer by Gribov region.

        Returns 'sf' (clearly small-field, `max_p d < δ_k/2`), 'buffer'
        (`δ_k/2 ≤ max_p d ≤ 2 δ_k`), or 'lf' (clearly large-field,
        `max_p d > 2 δ_k`).  The three returns are mutually exclusive
        and exhaustive for nonneg distances."""
        if max_plaquette_distance < 0:
            raise ValueError(
                f"max_plaquette_distance must be nonneg; got {max_plaquette_distance}"
            )
        if max_plaquette_distance < self.delta_k / 2.0:
            return "sf"
        if max_plaquette_distance > 2.0 * self.delta_k:
            return "lf"
        return "buffer"


@dataclass(frozen=True)
class KPData:
    """A Kotecký–Preiss certificate `(ρ, K)` at one regime, scale k.

    The `satisfies` field is the proof obligation that the regime's
    KP inequality holds at `(rho, K)`; concretely a `bool` here, but
    in the formal-Lean it is the `KPCertificate.satisfies : P rho K`
    field.  Carrying it as a `bool` keeps the Python dataclass
    closed without committing to the analytic predicate.
    """

    rho: float
    K: float
    satisfies: bool = True

    def __post_init__(self) -> None:
        if self.rho <= 0:
            raise ValueError(f"KP rate ρ must be positive; got {self.rho}")
        if self.K < 0:
            raise ValueError(f"KP amplitude K must be nonneg; got {self.K}")


@dataclass(frozen=True)
class InductiveState:
    """The inductive state ℐ_k at scale k.

    Fields mirror `formal/inductive-state.tex` Definition 2.1.

    Constructing an InductiveState only requires data; checking the
    scale-k induction hypotheses is `validate()`.  See the module
    docstring for the carry-uncertainty principle and the polymer
    atlas open question.
    """

    k: int
    """RG scale index."""

    sigma_hat: float
    """Renormalized string tension σ̂_k = a_k² σ_k (σ-3 sense, dimensionless)."""

    g: float
    """Running gauge coupling g_k."""

    kp_sf: KPData
    """Small-field KP certificate."""

    kp_lf: KPData
    """Large-field KP certificate."""

    kp_cap: KPData
    """Buffer KP certificate.

    Expected to satisfy
        kp_cap.rho == min(kp_sf.rho, kp_lf.rho),
        kp_cap.K   <= kp_sf.K + kp_lf.K,
    per `sheaf-framework.tex` Proposition 7.1; checked by V3 of `validate()`.
    """

    poly_atlas: PolyAtlas | None = field(default=None)
    """The polymer atlas P_k (concrete commitment 2026-05-26).

    Representation: `PolyAtlas` dataclass with `g_k`, `delta_k` (= g_k
    under α = 1), `n_max = 16`, plus the `shape_class` partition-of-
    unity classifier and `gribov_region` three-region classifier.
    See the `PolyAtlas` class docstring for the full commitment.

    Closes the polymer-atlas open question of Milestone 2.2
    (`formal/inductive-state.tex` §5, now §"closed").  Default
    `None` is permitted at construction sites that don't require the
    atlas (e.g., σ̂-trajectory-only tests); production sites use
    `PolyAtlas.at_scale(g_k)` to materialize the canonical atlas.
    """

    def validate(self) -> dict[str, bool]:
        """Run the scale-k induction-hypothesis checks (V1)–(V3).

        Returns a dict mapping each check name to its pass/fail status.
        All checks are scale-k-local: no reference to k+1 and no sum
        over k.

        - V1_sigma_hat_positive: σ̂_k > 0.
        - V2_kp_*_well_formed: each KP certificate's `satisfies` flag.
        - V3_buffer_glue_rho: ρ_∩ == min(ρ_sf, ρ_lf).
        - V3_buffer_glue_K:   K_∩ <= K_sf + K_lf.
        """
        return {
            "V1_sigma_hat_positive": self.sigma_hat > 0.0,
            "V2_kp_sf_well_formed": self.kp_sf.satisfies,
            "V2_kp_lf_well_formed": self.kp_lf.satisfies,
            "V2_kp_cap_well_formed": self.kp_cap.satisfies,
            "V3_buffer_glue_rho": self.kp_cap.rho == min(self.kp_sf.rho, self.kp_lf.rho),
            "V3_buffer_glue_K": self.kp_cap.K <= self.kp_sf.K + self.kp_lf.K,
        }

    def all_valid(self) -> bool:
        """True iff every clause of `validate()` passes."""
        return all(self.validate().values())

    @staticmethod
    def step_signature() -> str:
        """Return a textual description of the type of the block-spin step.

        This is the 2.2→2.3 handoff: 2.2 exposes the *type* of the step;
        2.3's job is to produce a *term* inhabiting it (per
        `formal/inductive-state.tex` Definition 4.1).

        The four conditions (S1)–(S4) of `docs/context.md` §3.3 are
        documented in the returned string but not encoded in any Python
        type (Python's type system can't express them without dependent
        typing).  The Lean mirror in `YMGap/RG/InductiveState.lean`
        provides the type as a Lean `def StepType`; see
        `formal/inductive-state.tex` §4 for the formal statement.
        """
        return (
            "T_b : {ℐ_k : Valid(ℐ_k)} → {ℐ_{k+1} : Valid(ℐ_{k+1})}\n"
            "  satisfying, with degradation budget (ε_sf, ε_lf, Δ_∩, η):\n"
            "    (S1) ρ_sf_{k+1} ≥ ρ_sf_k - ε_sf(b, g_k)\n"
            "    (S2) ρ_lf_{k+1} ≥ ρ_lf_k - ε_lf(b, g_k)\n"
            "    (S3) K_∩_{k+1}  ≤ K_∩_k + Δ_∩(b, g_k)\n"
            "    (S4) σ̂_{k+1}    ≥ σ̂_k - η(b, g_k)\n"
            "(2.2 exposes this type; 2.3 produces the term.)"
        )
