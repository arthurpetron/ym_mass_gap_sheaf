/-
The abstract codynamic-closure theorem: the **load-bearing** foundation
of which the SU(2) σ̂-budget closure (`SigmaHatPilot`, `SigmaHatLimit`)
is one named instance and a synthetic EKF sensor-fusion system is
another.

Milestone 4.1-promotion of `work_plan.md` (Lean upgrade authorized
2026-05-26): promote the codynamic transfer template from a decorative
appendix (Part B Ch. 19) to a load-bearing foundational chapter,
making Part III ("RG closure: SU(2) pilot") read as **the SU(2)
instance** of an abstract theorem rather than a self-contained RG
argument.

# The promotion

Previously, `RationalTail.sigma_hat_uniform_positive_lower_bound`
discharged the σ̂-budget closure with SU(2)-flavored names (`η`,
`σ̂_0`, `ε`).  The proof has no SU(2)-specific content; it is a
pure-Q' arithmetic chain (monotonicity of `+` on `≤`, transitivity).
This module **re-exposes** that theorem under abstract codynamic
naming — bound witness, degradation, budget, gap — and exhibits
**two named instances** sharing the same proof:

  * `su2_ym_system` — the SU(2) σ̂ pilot wrapped in the abstract
    structure.  The terminal invariant is σ̂_N ≥ ε > 0 (Phase-7.1's
    `sigma_hat_uv_limit_positive` re-derived as a corollary).
  * `ekf_system` — a synthetic Q'-rational sensor-fusion example
    (EKF-style) demonstrating that the structural shape applies
    well beyond gauge theory.  The terminal invariant is
    `P_N ≥ 95/100 > 0` (the covariance bound stays positive).

The two instances differ ONLY in their concrete Q' values; the proof
text `terminal_invariant_bound` works identically for both, which is
the load-bearing structural claim: *the SU(2) mass-gap inductive step
is one instance of an abstract codynamic-closure theorem*.

# The abstract theorem

**`terminal_invariant_bound`**: Given an `InductiveBoundWitnessSystem`
with:
  * a per-step **degradation** sequence in Q',
  * an **initial bound** in Q',
  * a **budget** that uniformly bounds partial sums of degradation,
  * a **gap** (strictly positive Q') such that `budget + gap ≤ initial_bound`,

conclude that the running bound witness `B_N := initial_bound -
Σ_{k<N} degradation_k` stays above the gap at every finite N:
`gap ≤ B_N`.

In the additive form (no Q'-subtraction): for every N,
`(Σ_{k<N} degradation_k) + gap ≤ initial_bound`.

This is the constructive form of "summable degradation budget ⇒
uniform-positivity lower bound on the terminal invariant" — the
manuscript-level claim of `docs/outline.md` Part B Ch. 19.

# Cross-references

  * `lean/YMGap/Constructive/RationalTail.lean::sigma_hat_uniform_positive_lower_bound`
    — the underlying proof, now re-exposed under codynamic naming.
  * `lean/YMGap/RG/SigmaHatPilot.lean` — the σ̂ pilot, now an instance.
  * `computations/transfer_examples/protocol.py` —
    `InductiveBoundWitness` Protocol (Python-side); this module is
    the Lean-formal companion.
  * `docs/outline.md` Part B Ch. 19 — the manuscript chapter that
    states the abstract theorem and exhibits the two instances.
  * `notes/codynamic-transfer.md` — the prose companion.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` only (inherited from
`Q'.le_trans'` and `Q'.add_le_add_right`).
-/

import YMGap.Constructive.RationalTail
import YMGap.RG.SigmaHatPilot
import YMGap.Continuum.SigmaHatLimit

namespace YMGap.Codynamic

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.SigmaHatPilot
open YMGap.Continuum.SigmaHatLimit

/-! ## The abstract `InductiveBoundWitnessSystem`

A bundled Q'-rational version of the `InductiveBoundWitness` Protocol
of `computations/transfer_examples/protocol.py`.  The four fields plus
three hypotheses parallel the protocol's contract: a degradation
sequence with a budget upper bound, an initial bound that exceeds
budget + gap, and a strictly-positive gap that the terminal invariant
inherits.

The structure deliberately does NOT carry the "bound witness sequence"
as data — that sequence is *derived* from the initial bound and the
cumulative degradation (`bound_witness_N := initial_bound -
finSum degradation N`).  Carrying degradation + initial_bound suffices
to determine the bound-witness sequence; this is the minimal
formulation. -/

/-- The abstract codynamic inductive system: every system satisfying
this signature admits the abstract terminal-invariant lower bound
(`terminal_invariant_bound` below).

  * `degradation` — per-step degradation `d_k : Q'`.
  * `initial_bound` — the starting bound `B_0 : Q'`.
  * `budget` — a Q' upper bound on `Σ_{k<N} d_k` uniform in N.
  * `gap` — the strict-positive Q' margin between budget and
    initial bound: `budget + gap ≤ initial_bound`. -/
structure InductiveBoundWitnessSystem where
  /-- The per-step degradation sequence. -/
  degradation : QSeq
  /-- The starting bound witness value. -/
  initial_bound : Q'
  /-- A Q' upper bound on the partial sums of `degradation`. -/
  budget : Q'
  /-- The strict-positivity margin (the terminal invariant's lower
  bound). -/
  gap : Q'
  /-- Hypothesis: the partial sums of degradation are uniformly
  bounded by `budget`. -/
  budget_summable : ∀ N, finSum degradation N ≤ budget
  /-- Hypothesis: the gap is strictly positive. -/
  gap_positive : (0 : Q') < gap
  /-- Hypothesis: budget + gap fits under the initial bound. -/
  gap_fits : budget + gap ≤ initial_bound

namespace InductiveBoundWitnessSystem

/-! ## The abstract theorem (load-bearing) -/

/-- **The abstract codynamic-closure theorem.**

Given any `InductiveBoundWitnessSystem`, the running degradation
totals plus the gap stay below the initial bound at every finite
truncation:

    ∀ N, (Σ_{k<N} degradation_k) + gap ≤ initial_bound.

Equivalently (interpreting `B_N := initial_bound - Σ_{k<N} degradation_k`
as the bound witness at step `N`):

    ∀ N, gap ≤ B_N    (i.e., B_N is uniformly bounded below by gap > 0).

This is the **load-bearing structural theorem** of the codynamic
transfer template (`docs/outline.md` Part B Ch. 19): the SU(2)
mass-gap inductive step (Phase-3 σ̂-budget closure) is one instance
of this theorem; a synthetic EKF sensor-fusion system is another.

**Proof.**  Mechanical composition of monotonicity of `+` on `≤` and
transitivity of `≤` at Q'.  Imported verbatim from
`RationalTail.sigma_hat_uniform_positive_lower_bound`, demonstrating
that the σ̂-budget closure has no SU(2)-specific content beyond the
choice of (degradation, initial_bound, budget, gap). -/
theorem terminal_invariant_bound (s : InductiveBoundWitnessSystem) :
    ∀ N, finSum s.degradation N + s.gap ≤ s.initial_bound :=
  sigma_hat_uniform_positive_lower_bound
    s.degradation s.budget s.initial_bound s.gap
    s.budget_summable s.gap_fits

/-- Strict-positivity of the gap, exposed for downstream use. -/
theorem gap_is_positive (s : InductiveBoundWitnessSystem) :
    (0 : Q') < s.gap :=
  s.gap_positive

/-- The terminal-invariant **existence** statement: there is a strictly
positive Q' that uniformly lower-bounds the running bound witnesses. -/
theorem terminal_invariant_exists (s : InductiveBoundWitnessSystem) :
    ∃ g : Q', (0 : Q') < g ∧
      (∀ N, finSum s.degradation N + g ≤ s.initial_bound) :=
  ⟨s.gap, s.gap_positive, terminal_invariant_bound s⟩

end InductiveBoundWitnessSystem

/-! ## Instance 1: SU(2) Yang–Mills σ̂-budget closure

The SU(2) pilot of Phase 3 + Phase 7.1 wrapped in the abstract
structure.  The Phase-7.1 closure `sigma_hat_uv_limit_positive`
becomes a corollary of `terminal_invariant_bound` applied to this
instance — demonstrating that the σ̂-budget closure has no
SU(2)-specific content beyond the choice of Q' constants. -/

namespace SU2_YM_Instance

open YMGap.RG.SigmaHatPilot

/-- The SU(2) σ̂-budget closure gap at the canonical pilot
(post-2026-05-26 c_λ Casimir-gap derivation):
`ε = σ̂_0 - eta_total_pilot = 1 - 9/10000 = 9991/10000`. -/
def su2_gap : Q' := Q'.mkPos 9991 10000 (by decide)

/-- The gap is strictly positive: `0 < 9991/10000`. -/
theorem su2_gap_positive : (0 : Q') < su2_gap := by decide

/-- The gap-fits inequality: `eta_total_pilot + gap ≤ sigma_hat_0_pilot`,
i.e., `9/10000 + 9991/10000 ≤ 1`. -/
theorem su2_gap_fits :
    eta_total_pilot + su2_gap ≤ sigma_hat_0_pilot := by decide

/-- **The SU(2) YM instance of `InductiveBoundWitnessSystem`.**

Wraps the Phase-3 pilot data (`eta_pilot`, `eta_total_pilot`,
`sigma_hat_0_pilot`) in the abstract structure with the gap supplied
by `su2_gap`. -/
def su2_ym_system : InductiveBoundWitnessSystem :=
  { degradation := eta_pilot,
    initial_bound := sigma_hat_0_pilot,
    budget := eta_total_pilot,
    gap := su2_gap,
    budget_summable := eta_pilot_partial_sum_bound,
    gap_positive := su2_gap_positive,
    gap_fits := su2_gap_fits }

/-- **SU(2) YM closure as an instance of the abstract theorem.**

The terminal invariant is uniformly bounded below by `9991/10000`:
`σ̂_N := 1 - finSum eta_pilot N` stays ≥ `9991/10000` at every N. -/
theorem su2_ym_closure :
    ∀ N, finSum eta_pilot N + su2_gap ≤ sigma_hat_0_pilot :=
  InductiveBoundWitnessSystem.terminal_invariant_bound su2_ym_system

end SU2_YM_Instance

/-! ## Instance 2: synthetic EKF sensor-fusion system

A Q'-rational synthetic instance demonstrating that the abstract
theorem applies far beyond gauge theory.  Captures the EKF-side of
`computations/transfer_examples/ekf_example.py`'s
`InductiveBoundWitness` Protocol implementation in arithmetic-only
form.

Concrete numbers:
  * Initial covariance bound `P_0 = 1` (normalized).
  * Per-step innovation `|D_n| = 1/100` (truncated at K = 3 steps).
  * Innovation total budget `5/100` (allows up to 5% total
    innovation across the run).
  * Gap `95/100` (the covariance bound stays ≥ 0.95 at every step).

The structure is identical to `su2_ym_system`; only the Q' constants
differ.  This is the structural payoff: **the SU(2) mass-gap
inductive step and the EKF sensor-fusion closure share their proof
verbatim**. -/

namespace EKF_Instance

/-- Per-step EKF innovation magnitude: `|D_n| ≤ 1/100`. -/
def ekf_innovation_max : Q' := Q'.mkPos 1 100 (by decide)

/-- Total innovation budget across K = 3 steps: `3 · 1/100 = 3/100`,
rounded UP to `5/100` for the running closure (matches the
truncated_const_3 partial-sum bound shape). -/
def ekf_innovation_budget : Q' := Q'.mkPos 5 100 (by decide)

/-- Initial covariance bound: `P_0 = 1`. -/
def ekf_initial_covariance : Q' := 1

/-- Closure gap: `P_N ≥ 95/100`. -/
def ekf_gap : Q' := Q'.mkPos 95 100 (by decide)

/-- The EKF innovation sequence: constant `1/100` for 3 steps, 0
afterward.  Matches the `truncated_const_3` shape from
`RationalTail`. -/
def ekf_innovation : QSeq := truncated_const_3 ekf_innovation_max

/-- The EKF innovation partial-sum bound: `∀ N, finSum ekf_innovation N ≤ ekf_innovation_budget`.

Discharged by `truncated_const_3_partial_sum_bound` at the EKF values
via four `decide` checks. -/
theorem ekf_innovation_partial_sum_bound :
    ∀ N, finSum ekf_innovation N ≤ ekf_innovation_budget :=
  truncated_const_3_partial_sum_bound
    ekf_innovation_max ekf_innovation_budget
    (by decide) (by decide) (by decide) (by decide)

/-- The EKF gap is strictly positive. -/
theorem ekf_gap_positive : (0 : Q') < ekf_gap := by decide

/-- The EKF gap-fits inequality: `5/100 + 95/100 ≤ 1`. -/
theorem ekf_gap_fits :
    ekf_innovation_budget + ekf_gap ≤ ekf_initial_covariance := by decide

/-- **The EKF sensor-fusion instance of `InductiveBoundWitnessSystem`.**

Same shape as `su2_ym_system` but with EKF-flavored Q' constants.
The proof of closure is *identical* (`terminal_invariant_bound`); only
the witnesses differ. -/
def ekf_system : InductiveBoundWitnessSystem :=
  { degradation := ekf_innovation,
    initial_bound := ekf_initial_covariance,
    budget := ekf_innovation_budget,
    gap := ekf_gap,
    budget_summable := ekf_innovation_partial_sum_bound,
    gap_positive := ekf_gap_positive,
    gap_fits := ekf_gap_fits }

/-- **EKF closure as an instance of the abstract theorem.**

The terminal invariant `P_N := 1 - finSum innovation N` stays ≥ `95/100`
at every step. -/
theorem ekf_closure :
    ∀ N, finSum ekf_innovation N + ekf_gap ≤ ekf_initial_covariance :=
  InductiveBoundWitnessSystem.terminal_invariant_bound ekf_system

end EKF_Instance

/-! ## Sentinel: both instances close by the same proof

Packages the two instances + a witness that they share the abstract
closure as their proof.  This is the explicit Lean realization of the
manuscript claim "SU(2) YM and EKF are two instances of one abstract
theorem." -/

/-- **Both named instances close via the abstract theorem.**

The SU(2) YM and EKF closures are *function applications* of
`terminal_invariant_bound` to two different `InductiveBoundWitnessSystem`
values.  The proof text is identical; only the instance differs.

This is the load-bearing structural claim of the codynamic transfer
template (`docs/outline.md` Part B Ch. 19). -/
theorem codynamic_transfer_load_bearing :
    (∀ N, finSum YMGap.RG.SigmaHatPilot.eta_pilot N
            + SU2_YM_Instance.su2_gap
          ≤ YMGap.RG.SigmaHatPilot.sigma_hat_0_pilot) ∧
    (∀ N, finSum EKF_Instance.ekf_innovation N
            + EKF_Instance.ekf_gap
          ≤ EKF_Instance.ekf_initial_covariance) :=
  ⟨SU2_YM_Instance.su2_ym_closure, EKF_Instance.ekf_closure⟩

end YMGap.Codynamic

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Codynamic.InductiveBoundWitnessSystem.terminal_invariant_bound
#print axioms YMGap.Codynamic.InductiveBoundWitnessSystem.gap_is_positive
#print axioms YMGap.Codynamic.InductiveBoundWitnessSystem.terminal_invariant_exists
#print axioms YMGap.Codynamic.SU2_YM_Instance.su2_gap_positive
#print axioms YMGap.Codynamic.SU2_YM_Instance.su2_gap_fits
#print axioms YMGap.Codynamic.SU2_YM_Instance.su2_ym_closure
#print axioms YMGap.Codynamic.EKF_Instance.ekf_innovation_partial_sum_bound
#print axioms YMGap.Codynamic.EKF_Instance.ekf_gap_positive
#print axioms YMGap.Codynamic.EKF_Instance.ekf_gap_fits
#print axioms YMGap.Codynamic.EKF_Instance.ekf_closure
#print axioms YMGap.Codynamic.codynamic_transfer_load_bearing
