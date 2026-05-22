"""The inductive state package ℐ_k for Milestone 2.2.

Python mirror of `formal/inductive-state.tex` Definition 2.1.

The state at RG scale k bundles:

  - the renormalized string tension σ̂_k (σ-3 sense),
  - the running coupling g_k,
  - three Kotecký–Preiss certificates (small-field, large-field, buffer),
  - the polymer atlas P_k (representation left abstract; see open question).

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

The representation of P_k is the open question of Milestone 2.2.
Here it is typed as `Any` with a docstring acknowledging the
deferral.  Concrete representations are pinned in Phase 3 against
the polymer activities of Milestones 3.1–3.3.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


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

    poly_atlas: Any = field(default=None)
    """The polymer atlas P_k.

    Representation deliberately abstract (`Any`).  The decision is
    the open question of Milestone 2.2; see `formal/inductive-state.tex`
    §5 and `work_plan.md` Milestone 2.2 open-question paragraph.
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
