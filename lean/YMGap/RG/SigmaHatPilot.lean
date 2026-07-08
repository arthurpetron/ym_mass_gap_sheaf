/-
SU(2) pilot wire-ins for the σ̂-budget closure.

This module instantiates `YMGap.Constructive.RationalTail.sigma_hat_budget_closure`
on concrete `Q'`-rational upper bounds for the per-step η_k of the SU(2)
pilot, in both canonical and Wilson conventions.

The structural proof (partial-sum bound at every N via stabilization past
the cut-off) lives in
`YMGap.Constructive.RationalTail.truncated_const_3_partial_sum_bound`;
each pilot here is a thin instantiation supplying the four arithmetic
inequalities (discharged by `decide` at the chosen rationals) plus the
closure condition.

# Data provenance

Python (`computations.q_lift.pilot_eta_rational_bound`) produces:

  * **Canonical** at `g_0 = 0.30`, `K = 3`, `denominator = 10000`:
    η_max numerator = 3, eta_total numerator = 9 (post-2026-05-26
    c_λ Casimir-gap derivation; previously 11 and 33 under c_λ = 1/2).
  * **Wilson** at `g_0 = 0.50`, `K = 3`, `denominator = 10000`:
    η_max numerator = 1, eta_total numerator = 3 (post-c_λ-upgrade;
    previously 4 and 12).

The Lean module hard-codes these.  A regression test
(`tests/test_q_lift.py::TestLeanWireInConsistency`) enforces lockstep:
if the Python fiducials drift, the test fails loudly and these constants
must be updated.

# What this module proves

  * Canonical: `∀ N, finSum eta_pilot N ≤ 1`.
  * Wilson:    `∀ N, finSum eta_pilot_wilson N ≤ 1`.

Both via `RationalTail.sigma_hat_budget_closure` composed with
`RationalTail.truncated_const_3_partial_sum_bound`.

# Axiom gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `depends on axioms: [propext]` only —
no `sorryAx`, no `Classical.*`.  See the `#print axioms` block at the
end of the file.
-/

import YMGap.Constructive.RationalTail
import YMGap.BudgetConstants

namespace YMGap.RG.SigmaHatPilot

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## Canonical-convention wire-in (g_0 = 0.30, K = 3, denominator = 10000) -/

/-- Rational upper bound on `max_k η_k` from the canonical SU(2) pilot at
`g_0 = 0.30`: `3/10000 = 3e-4` (post-2026-05-26 c_λ Casimir-gap
derivation; previously 11/10000 under c_λ = 1/2).  Dominates each of
the three per-step η_k ≈ 2.7e-4 from above. -/
def eta_max_pilot : Q' := YMGap.BudgetConstants.bcEtaMaxCanonical

/-- Total budget after K = 3 transitions: `9/10000` (post-c_λ-upgrade;
previously 33/10000). -/
def eta_total_pilot : Q' := Q'.mkPos 9 10000 (by decide)

/-- σ̂_0 for the canonical wire-in: `(1 : Q')`. -/
def sigma_hat_0_pilot : Q' := 1

/-- The canonical pilot's η-sequence — `truncated_const_3` at η_max. -/
def eta_pilot : QSeq := truncated_const_3 eta_max_pilot

/-- Closure condition for the canonical pilot: `9/10000 ≤ 1`. -/
theorem eta_total_le_sigma_0 : eta_total_pilot ≤ sigma_hat_0_pilot := by
  show (9 : Int) * (1 : Int) ≤ (1 : Int) * (10000 : Int)
  decide

/-- Partial-sum bound for the canonical pilot.  Discharges the four
arithmetic obligations of `truncated_const_3_partial_sum_bound` by `decide`
at the concrete `η_max = 11/10000`, `σ_0 = 33/10000`. -/
theorem eta_pilot_partial_sum_bound :
    ∀ N, finSum eta_pilot N ≤ eta_total_pilot :=
  truncated_const_3_partial_sum_bound eta_max_pilot eta_total_pilot
    (by decide) (by decide) (by decide) (by decide)

/-- **SU(2) pilot σ̂-budget closure (canonical wire-in).**

For every finite truncation `N`, the partial sum of the pilot's rational
upper-bounded η-sequence stays below `σ̂_0 = 1`:

  `∀ N, finSum eta_pilot N ≤ sigma_hat_0_pilot`.

This is the Phase-3 global closure `Σ_{k=0}^{N-1} η_k ≤ σ̂_0` (uniform in
`N`), specialized to the canonical pilot data and discharged at `Q'` via
`sigma_hat_budget_closure`.  No infinite-sum analytic content is invoked;
the bound holds at every finite truncation, which per
`lean/YMGap/Constructive/Rationals.lean`'s "Boundary" docstring is the
constructively correct form of the global claim in the Q'-only layer. -/
theorem eta_pilot_budget_closes :
    ∀ N, finSum eta_pilot N ≤ sigma_hat_0_pilot :=
  sigma_hat_budget_closure eta_pilot eta_total_pilot sigma_hat_0_pilot
    eta_pilot_partial_sum_bound eta_total_le_sigma_0

/-! ## Wilson-convention wire-in (g_0 = 0.50, K = 3, denominator = 10000)

Parallel to the canonical instance.  Wilson's convergence window is
wider (g_max_sf ≈ 0.81 vs canonical ≈ 0.40), so g_0 = 0.50 sits well
inside it with per-step η ≈ 3e-4. -/

/-- Wilson-pilot rational upper bound: `1/10000 = 1e-4` (post-2026-05-26
c_λ Casimir-gap derivation; previously 4/10000 under c_λ = 1/2). -/
def eta_max_pilot_wilson : Q' := Q'.mkPos 1 10000 (by decide)

/-- Wilson-pilot total bound: `3/10000` (post-c_λ-upgrade;
previously 12/10000). -/
def eta_total_pilot_wilson : Q' := YMGap.BudgetConstants.bcEtaMaxCanonical

/-- σ̂_0 for the Wilson wire-in: `(1 : Q')`. -/
def sigma_hat_0_pilot_wilson : Q' := 1

/-- The Wilson pilot's η-sequence. -/
def eta_pilot_wilson : QSeq := truncated_const_3 eta_max_pilot_wilson

/-- Wilson closure condition: `3/10000 ≤ 1`. -/
theorem eta_total_wilson_le_sigma_0 :
    eta_total_pilot_wilson ≤ sigma_hat_0_pilot_wilson := by
  show (3 : Int) * (1 : Int) ≤ (1 : Int) * (10000 : Int)
  decide

/-- Wilson partial-sum bound, via the generic K = 3 truncated-constant
theorem. -/
theorem eta_pilot_wilson_partial_sum_bound :
    ∀ N, finSum eta_pilot_wilson N ≤ eta_total_pilot_wilson :=
  truncated_const_3_partial_sum_bound eta_max_pilot_wilson eta_total_pilot_wilson
    (by decide) (by decide) (by decide) (by decide)

/-- **SU(2) pilot σ̂-budget closure (Wilson wire-in).**

Parallel to `eta_pilot_budget_closes` but for the Wilson convention at
`g_0 = 0.50`.  Confirms the closure framework is convention-agnostic. -/
theorem eta_pilot_wilson_budget_closes :
    ∀ N, finSum eta_pilot_wilson N ≤ sigma_hat_0_pilot_wilson :=
  sigma_hat_budget_closure eta_pilot_wilson eta_total_pilot_wilson
    sigma_hat_0_pilot_wilson
    eta_pilot_wilson_partial_sum_bound eta_total_wilson_le_sigma_0

/-! ## Composition via `prefix_plus_tail_closure` (infinite-trajectory framework)

The Phase-3 wire-in above uses the simpler `sigma_hat_budget_closure`,
which takes a uniform-in-N bound directly.  The Phase-4-prep alternative
`prefix_plus_tail_closure` derives the global bound from a uniform-PAST-
`K_0` bound plus nonneg-monotonicity for `N < K_0` — the natural shape
for an infinite-trajectory closure where the tail past `K_0` is rationally
bounded (e.g. via geometric decay of η_k in the UV-direction trajectory).

For the existing truncated-constant pilot the tail is exactly zero past
`K_0 = 3`, so both routes produce the same closure.  The pair of theorems
below confirms the new framework COMPOSES with the existing wire-ins
without changing the closure content. -/

/-- Every element of `eta_pilot` is nonneg (input to `prefix_plus_tail_closure`).

For `k ∈ {0, 1, 2}`: ``eta_pilot k = eta_max_pilot = 11/10000 ≥ 0``.
For `k = n + 3`: ``eta_pilot k = 0 ≥ 0``. -/
theorem eta_pilot_nonneg : ∀ k, (0 : Q') ≤ eta_pilot k
  | 0 => by show (0 : Q') ≤ eta_max_pilot; decide
  | 1 => by show (0 : Q') ≤ eta_max_pilot; decide
  | 2 => by show (0 : Q') ≤ eta_max_pilot; decide
  | _ + 3 => by
    show (0 : Q') ≤ (0 : Q')
    exact Q'.le_refl' _

/-- Canonical partial-sum bound at the cut-off `K = 3`, mirrors the
Wilson-side `finSum_eta_pilot_wilson_three_le`.  Exposed for use in the
`prefix_plus_tail` composition below. -/
theorem finSum_eta_pilot_three_le :
    finSum eta_pilot 3 ≤ eta_total_pilot := by
  show (((0 : Q') + eta_max_pilot) + eta_max_pilot) + eta_max_pilot
        ≤ eta_total_pilot
  decide

/-- The canonical pilot's closure derived via the new infinite-trajectory
framework `prefix_plus_tail_closure` (rather than `sigma_hat_budget_closure`).
Cut-off `K_0 = 3`; tail past 3 is zero (via `finSum_stabilizes_after_K`),
so the uniform-past-K_0 bound is exactly `finSum eta_pilot 3`.

Confirms the new framework composes; produces the same closure
``∀ N, finSum eta_pilot N ≤ sigma_hat_0_pilot`` as
`eta_pilot_budget_closes`. -/
theorem eta_pilot_budget_closes_via_prefix_tail :
    ∀ N, finSum eta_pilot N ≤ sigma_hat_0_pilot := by
  apply prefix_plus_tail_closure eta_pilot 3 eta_total_pilot sigma_hat_0_pilot
  · -- nonneg
    exact eta_pilot_nonneg
  · -- uniform-past-K_0: finSum eta_pilot (3 + M) ≤ eta_total_pilot for all M
    intro M
    -- Stabilization: finSum eta_pilot (3 + M) = finSum eta_pilot 3
    rw [finSum_stabilizes_after_K eta_pilot 3
        (truncated_const_3_zero_of_ge_3 eta_max_pilot) M]
    exact finSum_eta_pilot_three_le
  · -- budget condition
    exact eta_total_le_sigma_0

/-- Every element of `eta_pilot_wilson` is nonneg. -/
theorem eta_pilot_wilson_nonneg : ∀ k, (0 : Q') ≤ eta_pilot_wilson k
  | 0 => by show (0 : Q') ≤ eta_max_pilot_wilson; decide
  | 1 => by show (0 : Q') ≤ eta_max_pilot_wilson; decide
  | 2 => by show (0 : Q') ≤ eta_max_pilot_wilson; decide
  | _ + 3 => by
    show (0 : Q') ≤ (0 : Q')
    exact Q'.le_refl' _

/-- Wilson partial-sum bound at K = 3, exposed for use in the
`prefix_plus_tail` composition below. -/
theorem finSum_eta_pilot_wilson_three_le :
    finSum eta_pilot_wilson 3 ≤ eta_total_pilot_wilson := by
  show (((0 : Q') + eta_max_pilot_wilson) + eta_max_pilot_wilson) + eta_max_pilot_wilson
        ≤ eta_total_pilot_wilson
  decide

/-- Wilson pilot's closure via `prefix_plus_tail_closure`.  Same shape as
`eta_pilot_budget_closes_via_prefix_tail`. -/
theorem eta_pilot_wilson_budget_closes_via_prefix_tail :
    ∀ N, finSum eta_pilot_wilson N ≤ sigma_hat_0_pilot_wilson := by
  apply prefix_plus_tail_closure eta_pilot_wilson 3
        eta_total_pilot_wilson sigma_hat_0_pilot_wilson
  · exact eta_pilot_wilson_nonneg
  · intro M
    rw [finSum_stabilizes_after_K eta_pilot_wilson 3
        (truncated_const_3_zero_of_ge_3 eta_max_pilot_wilson) M]
    exact finSum_eta_pilot_wilson_three_le
  · exact eta_total_wilson_le_sigma_0

end YMGap.RG.SigmaHatPilot

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.SigmaHatPilot.eta_max_pilot
#print axioms YMGap.RG.SigmaHatPilot.eta_total_pilot
#print axioms YMGap.RG.SigmaHatPilot.sigma_hat_0_pilot
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_partial_sum_bound
#print axioms YMGap.RG.SigmaHatPilot.eta_total_le_sigma_0
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_budget_closes
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_wilson_partial_sum_bound
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_wilson_budget_closes
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_nonneg
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_budget_closes_via_prefix_tail
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_wilson_nonneg
#print axioms YMGap.RG.SigmaHatPilot.finSum_eta_pilot_wilson_three_le
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_wilson_budget_closes_via_prefix_tail
