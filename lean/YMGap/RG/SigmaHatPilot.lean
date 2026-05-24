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
    η_max numerator = 11, eta_total numerator = 33.
  * **Wilson** at `g_0 = 0.50`, `K = 3`, `denominator = 10000`:
    η_max numerator = 4, eta_total numerator = 12.

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

namespace YMGap.RG.SigmaHatPilot

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## Canonical-convention wire-in (g_0 = 0.30, K = 3, denominator = 10000) -/

/-- Rational upper bound on `max_k η_k` from the canonical SU(2) pilot at
`g_0 = 0.30`: `11/10000 = 1.1e-3`, dominates each of the three per-step
η_k ≈ 1.0e-3 from above. -/
def eta_max_pilot : Q' := Q'.mkPos 11 10000 (by decide)

/-- Total budget after K = 3 transitions: `33/10000`. -/
def eta_total_pilot : Q' := Q'.mkPos 33 10000 (by decide)

/-- σ̂_0 for the canonical wire-in: `(1 : Q')`. -/
def sigma_hat_0_pilot : Q' := 1

/-- The canonical pilot's η-sequence — `truncated_const_3` at η_max. -/
def eta_pilot : QSeq := truncated_const_3 eta_max_pilot

/-- Closure condition for the canonical pilot: `33/10000 ≤ 1`. -/
theorem eta_total_le_sigma_0 : eta_total_pilot ≤ sigma_hat_0_pilot := by
  show (33 : Int) * (1 : Int) ≤ (1 : Int) * (10000 : Int)
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

/-- Wilson-pilot rational upper bound: `4/10000 = 4e-4`. -/
def eta_max_pilot_wilson : Q' := Q'.mkPos 4 10000 (by decide)

/-- Wilson-pilot total bound: `12/10000`. -/
def eta_total_pilot_wilson : Q' := Q'.mkPos 12 10000 (by decide)

/-- σ̂_0 for the Wilson wire-in: `(1 : Q')`. -/
def sigma_hat_0_pilot_wilson : Q' := 1

/-- The Wilson pilot's η-sequence. -/
def eta_pilot_wilson : QSeq := truncated_const_3 eta_max_pilot_wilson

/-- Wilson closure condition: `12/10000 ≤ 1`. -/
theorem eta_total_wilson_le_sigma_0 :
    eta_total_pilot_wilson ≤ sigma_hat_0_pilot_wilson := by
  show (12 : Int) * (1 : Int) ≤ (1 : Int) * (10000 : Int)
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
