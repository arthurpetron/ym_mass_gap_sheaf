/-
SU(2) pilot wire-in for the σ̂-budget closure.

This module instantiates `YMGap.Constructive.RationalTail.sigma_hat_budget_closure`
on a concrete `Q'`-rational upper bound for the per-step η_k of the SU(2)
pilot, computed in Python at `g_0 = 0.30`, `K = 3` (transitions), canonical
heat-kernel convention.

# Data provenance

Python (`computations.q_lift.pilot_eta_rational_bound`) at the canonical
wire-in parameters yields:

  * `g_trajectory`            ≈ [0.30000, 0.30044, 0.30087, 0.30131]
  * `η₀`                      ≈ 1.008e-3
  * `η₁`                      ≈ 1.029e-3
  * `η₂`                      ≈ 1.050e-3
  * `max_k η_k`               ≈ 1.050e-3
  * `eta_max_numerator`       = 11    (at denominator 10000)
  * `eta_total_numerator`     = 33    (= K × 11 = 3 × 11)
  * `σ̂_0 (Q')`                = 1/1

The Lean module hard-codes these as:

  * `eta_max_pilot`           := `Q'.mkPos 11 10000 _`   (1.1e-3, bounds each η_k)
  * `eta_total_pilot`         := `Q'.mkPos 33 10000 _`   (3.3e-3, bounds Σ η_k)
  * `sigma_hat_0_pilot`       := `1`

A regression test (`tests/test_q_lift.py::TestLeanWireInConsistency`) verifies
the Python pilot still produces `(11, 33)` at denominator `10000` — if the
fiducials in `computations/sigma_hat_trajectory.py` change, that test breaks
loudly and this module's constants must be updated together.

# What this module proves

  `∀ N, finSum eta_pilot N ≤ sigma_hat_0_pilot`

via `RationalTail.sigma_hat_budget_closure`, where `eta_pilot` is the
truncated-constant sequence `(η_max, η_max, η_max, 0, 0, …)`.  The
partial-sum bound is shown directly for `N ≤ 3` and via
`finSum_stabilizes_after_K` for `N ≥ 4`.

# Axiom gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `depends on axioms: [propext]` only —
no `sorryAx`, no `Classical.*`.  See the `#print axioms` block at the
end of the file.
-/

import YMGap.Constructive.RationalTail

namespace YMGap.RG.SigmaHatPilot

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## Pilot constants (canonical wire-in: g_0 = 0.30, K = 3, denominator = 10000) -/

/-- Rational upper bound on `max_k η_k` from the SU(2) pilot at `g_0 = 0.30`.

Python value: `11 / 10000 = 1.1e-3`.  Dominates each of the three per-step
η_k ≈ 1.0e-3 from above. -/
def eta_max_pilot : Q' := Q'.mkPos 11 10000 (by decide)

/-- Rational upper bound on `Σ_{k<K} η_k` for `K = 3`: `33 / 10000 = 3.3e-3`.

This is `K · eta_max_pilot` realized exactly in `Q'` (3 × 11 = 33). -/
def eta_total_pilot : Q' := Q'.mkPos 33 10000 (by decide)

/-- σ̂_0 for the canonical wire-in.  Chosen as `(1 : Q')` so the closure
condition `eta_total_pilot ≤ sigma_hat_0_pilot` is the easy bound
`33/10000 ≤ 1`. -/
def sigma_hat_0_pilot : Q' := 1

/-! ## The pilot η-sequence

Truncated constant: `η_max_pilot` for `k < 3`, zero thereafter.  The
pattern `_ + 3 => 0` reduces by `rfl` for any explicit `n + 3`, which is
the load-bearing fact used by `finSum_stabilizes_after_K`. -/

/-- The pilot's truncated-constant η-sequence (Q'-rational upper bound). -/
def eta_pilot : QSeq
  | 0     => eta_max_pilot
  | 1     => eta_max_pilot
  | 2     => eta_max_pilot
  | _ + 3 => 0

/-! ## Per-step structural facts about `eta_pilot` -/

/-- `eta_pilot` is zero past index `3`.  Proof: case split on `k`, with the
three nonzero indices contradicted by `3 ≤ k` and `k + 3` matching the
`rfl` case of the definition. -/
theorem eta_pilot_zero_of_ge_3 : ∀ k, 3 ≤ k → eta_pilot k = 0
  | 0,     h => absurd h (by decide)
  | 1,     h => absurd h (by decide)
  | 2,     h => absurd h (by decide)
  | _ + 3, _ => rfl

/-! ## Partial-sum bound at the cut-off -/

/-- `finSum eta_pilot 3 ≤ eta_total_pilot` —
i.e. `(0 + η_max) + η_max + η_max ≤ 33/10000`.

Discharged by `decide`: the LHS reduces structurally to a closed `Q'` term
whose ≤ check reduces to a closed `Int` decision. -/
theorem finSum_eta_pilot_three_le : finSum eta_pilot 3 ≤ eta_total_pilot := by
  -- finSum eta_pilot 3
  --   = finSum eta_pilot 2 + eta_pilot 2
  --   = (finSum eta_pilot 1 + eta_pilot 1) + eta_pilot 2
  --   = ((finSum eta_pilot 0 + eta_pilot 0) + eta_pilot 1) + eta_pilot 2
  --   = ((0 + η_max) + η_max) + η_max  (by recursion on Q'.add, defs)
  show (((0 : Q') + eta_max_pilot) + eta_max_pilot) + eta_max_pilot
        ≤ eta_total_pilot
  decide

/-! ## The universal partial-sum bound

Split into the four base cases `N ∈ {0, 1, 2, 3}` and the tail case
`N = n + 4`, where stabilization reduces the partial sum to `finSum eta_pilot 3`. -/

/-- `∀ N, finSum eta_pilot N ≤ eta_total_pilot`. -/
theorem eta_pilot_partial_sum_bound : ∀ N, finSum eta_pilot N ≤ eta_total_pilot
  | 0     => by
    -- finSum eta_pilot 0 = 0 ≤ 33/10000
    show (0 : Q') ≤ eta_total_pilot
    decide
  | 1     => by
    -- finSum eta_pilot 1 = 0 + eta_max_pilot ≤ 33/10000
    show (0 : Q') + eta_max_pilot ≤ eta_total_pilot
    decide
  | 2     => by
    -- finSum eta_pilot 2 = (0 + η_max) + η_max ≤ 33/10000
    show ((0 : Q') + eta_max_pilot) + eta_max_pilot ≤ eta_total_pilot
    decide
  | 3     => finSum_eta_pilot_three_le
  | n + 4 => by
    -- For N ≥ 4 the partial sum equals finSum eta_pilot 3 (stabilization).
    -- n + 4 = (n + 1) + 3 holds by `rfl` (Nat.add recurses on the right arg);
    -- (n + 1) + 3 = 3 + (n + 1) by Nat.add_comm; then apply stabilization.
    show finSum eta_pilot ((n + 1) + 3) ≤ eta_total_pilot
    rw [Nat.add_comm (n + 1) 3,
        YMGap.Constructive.RationalTail.finSum_stabilizes_after_K
          eta_pilot 3 eta_pilot_zero_of_ge_3 (n + 1)]
    exact finSum_eta_pilot_three_le

/-! ## The closure condition -/

/-- `eta_total_pilot ≤ sigma_hat_0_pilot`: `33/10000 ≤ 1`.  The cross-product
check is `33 · 1 ≤ 1 · 10000`. -/
theorem eta_total_le_sigma_0 : eta_total_pilot ≤ sigma_hat_0_pilot := by
  show (33 : Int) * (1 : Int) ≤ (1 : Int) * (10000 : Int)
  decide

/-! ## Pilot closure — the assembled load-bearing theorem -/

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

end YMGap.RG.SigmaHatPilot

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.SigmaHatPilot.eta_max_pilot
#print axioms YMGap.RG.SigmaHatPilot.eta_total_pilot
#print axioms YMGap.RG.SigmaHatPilot.sigma_hat_0_pilot
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_zero_of_ge_3
#print axioms YMGap.RG.SigmaHatPilot.finSum_eta_pilot_three_le
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_partial_sum_bound
#print axioms YMGap.RG.SigmaHatPilot.eta_total_le_sigma_0
#print axioms YMGap.RG.SigmaHatPilot.eta_pilot_budget_closes
