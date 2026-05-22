"""The block-spin step: refined type and proof obligations.

Python mirror of `formal/block-spin-morphism.tex` (Definitions 4.1,
5.1, 5.2, 6.1).

The block-spin step `T_b` takes a Valid `InductiveState` at scale
`k` to a Valid `InductiveState` at scale `k+1`, with controlled
degradation in each of the three KP certificates and in the
renormalized string tension.  This module exposes:

  * `BudgetFunctions` — the four per-step budget functions
    (ε_sf, ε_lf, Δ_cap, η), each `(b, g_k) -> float`.  Abstract
    parameters here; concrete forms come from Milestones 3.1–3.4.

  * `TwoCellTheta` — the σ̂-transport 2-cell as a separate typed
    object per `formal/block-spin-morphism.tex` Definition 4.1.

  * `BlockSpinStepObligation` — a record encoding the proof
    obligations a 2.3 step term must discharge.  Carries the block
    scale `b` and the budget; its `check(s_k, s_next)` method
    verifies whether a *candidate* (input, output) pair satisfies
    S1–S4.  This is a CHECK, not a CONSTRUCTION: 2.3 does not
    inhabit `T_b`; the inhabitation is the joint job of Milestones
    3.1 (ε_sf), 3.2 (ε_lf), 3.3 (Δ_cap), 3.4 (η).

Boundary discipline
-------------------

S1–S4 are PER-STEP, single-k constraints.  Nothing in this module
sums over `k` or asserts a uniform-in-`k` property; that would be
the Phase-3 budget-closure content.  The `check()` method takes
two states and one budget; it does not iterate.

When a candidate `s_next` is checked, V1 (`σ̂_{k+1} > 0`) is part
of the codomain's `Valid` predicate; this module does not separately
re-derive `σ̂_{k+1} > 0` from S4, and the S4 check is just the
inequality `σ̂_{k+1} ≥ σ̂_k - η`.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from computations.inductive_state import InductiveState

# A budget function takes (b, g_k) and returns a budget value at scale k.
BudgetFn = Callable[[float, float], float]


@dataclass(frozen=True)
class BudgetFunctions:
    """The four per-step budget functions.

    Mirrors `formal/block-spin-morphism.tex` Definition 5.1.  Each
    field is a `(b, g_k) -> float` callable; the concrete forms are
    abstract here and pinned in Milestones 3.1–3.4.
    """

    eps_sf: BudgetFn
    """Small-field ρ-degradation budget per RG step.  Milestone 3.1."""

    eps_lf: BudgetFn
    """Large-field ρ-degradation budget per RG step.  Milestone 3.2."""

    delta_cap: BudgetFn
    """Overlap K-growth budget per RG step.  Milestone 3.3."""

    eta: BudgetFn
    """String-tension degradation budget per RG step (the η of Θ_k).  Milestone 3.4."""


@dataclass(frozen=True)
class TwoCellTheta:
    """The σ̂-transport 2-cell Θ_k as a separate typed object.

    Mirrors `formal/block-spin-morphism.tex` Definition 4.1 and the
    work_plan.md 2.3 open-question recommendation ("a separate
    typed object for clarity").

    A Θ_k-witness bundles:
      * `sigma_in`  — input renormalized string tension σ̂_k (σ-3 sense),
      * `eta_k`     — per-step degradation budget,
      * `sigma_out` — output renormalized string tension σ̂_{k+1},
      * proof       — implicit in `decrease_satisfied()`: σ̂_in - η_k ≤ σ̂_out.

    Constructing a `TwoCellTheta` does not enforce the decrease
    inequality; use `decrease_satisfied()` to verify.  This matches
    the Python convention from `inductive_state.py`: dataclass
    enforces data shape, not analytic content.
    """

    sigma_in: float
    eta_k: float
    sigma_out: float

    def decrease_satisfied(self) -> bool:
        """Verify the Θ_k transport inequality σ̂_in - η_k ≤ σ̂_out."""
        return self.sigma_in - self.eta_k <= self.sigma_out


@dataclass(frozen=True)
class BlockSpinStepObligation:
    """The proof obligation a 2.3 step term must discharge.

    Mirrors `formal/block-spin-morphism.tex` Definition 6.1.

    Carries the block scale `b` and the four budget functions;
    its `check(s_k, s_next)` method verifies whether a *candidate*
    (input, output) pair satisfies the four conditions S1–S4 of
    `docs/context.md` §3.3.  This is verification of a candidate,
    NOT construction of `s_next`.  Constructing `s_next` from `s_k`
    is the joint job of Milestones 3.1–3.4.
    """

    b: float
    """Block scale factor (a_{k+1} = b · a_k)."""

    budget: BudgetFunctions
    """The four per-step budget functions."""

    def check(
        self, s_k: InductiveState, s_next: InductiveState
    ) -> dict[str, bool]:
        """Check whether `(s_k, s_next)` satisfies S1–S4.

        Returns a dict mapping each check name to its pass/fail
        status.  Includes the structural `scale_increment` check
        that `s_next.k == s_k.k + 1`.

        Note: this is a CHECK, not a CONSTRUCTION.  The method does
        not produce `s_next`; the caller supplies a candidate.
        """
        g_k = s_k.g
        return {
            "scale_increment": s_next.k == s_k.k + 1,
            "S1_eps_sf": (
                s_next.kp_sf.rho >= s_k.kp_sf.rho - self.budget.eps_sf(self.b, g_k)
            ),
            "S2_eps_lf": (
                s_next.kp_lf.rho >= s_k.kp_lf.rho - self.budget.eps_lf(self.b, g_k)
            ),
            "S3_delta_cap": (
                s_next.kp_cap.K <= s_k.kp_cap.K + self.budget.delta_cap(self.b, g_k)
            ),
            "S4_eta_sigma": (
                s_next.sigma_hat >= s_k.sigma_hat - self.budget.eta(self.b, g_k)
            ),
        }

    def all_satisfied(self, s_k: InductiveState, s_next: InductiveState) -> bool:
        """True iff every clause of `check(s_k, s_next)` passes."""
        return all(self.check(s_k, s_next).values())

    def extract_two_cell(
        self, s_k: InductiveState, s_next: InductiveState
    ) -> TwoCellTheta:
        """Extract the Θ_k typed object from a candidate pair.

        Returns a `TwoCellTheta` with `sigma_in = s_k.sigma_hat`,
        `eta_k = η(b, g_k)`, `sigma_out = s_next.sigma_hat`.  Use
        `.decrease_satisfied()` to verify S4.
        """
        return TwoCellTheta(
            sigma_in=s_k.sigma_hat,
            eta_k=self.budget.eta(self.b, s_k.g),
            sigma_out=s_next.sigma_hat,
        )

    @staticmethod
    def signature() -> str:
        """Return a textual description of the refined step type.

        This mirrors `InductiveState.step_signature()` but at the
        refined level (S1–S4 spelled out, budgets named, 2-cell
        Θ_k pulled out as separate object).
        """
        return (
            "T_b : {ℐ_k // Valid(ℐ_k)} → {ℐ_{k+1} // Valid(ℐ_{k+1})}\n"
            "  with budget (ε_sf, ε_lf, Δ_cap, η):\n"
            "    (S1) ρ_sf_{k+1} ≥ ρ_sf_k - ε_sf(b, g_k)   [Milestone 3.1]\n"
            "    (S2) ρ_lf_{k+1} ≥ ρ_lf_k - ε_lf(b, g_k)   [Milestone 3.2]\n"
            "    (S3) K_∩_{k+1}  ≤ K_∩_k + Δ_cap(b, g_k)   [Milestone 3.3]\n"
            "    (S4) σ̂_{k+1}    ≥ σ̂_k - η(b, g_k)         [Milestone 3.4 / Θ_k]\n"
            "(2.3 states the type; 3.1-3.4 jointly produce the term.)"
        )
