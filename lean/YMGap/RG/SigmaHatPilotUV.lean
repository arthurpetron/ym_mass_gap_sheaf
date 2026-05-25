/-
SU(2) UV-direction pilot — genuine infinite-trajectory σ̂-budget closure.

Milestone 6.4 of `work_plan.md`.  Composes the Phase-3 infinite-trajectory
framework (`RationalTail.prefix_plus_tail_closure`, landed in `[P3.4-tail/P4-prep]`)
with the Phase-6 UV-direction trajectory (`computations/uv_trajectory.py`,
Milestone 6.3) to produce the first **genuine infinite-trajectory**
σ̂-budget closure in Lean.

# What "genuine infinite-trajectory" means here

The existing `SigmaHatPilot.lean` (canonical and Wilson IR-direction
wire-ins) proves σ̂-budget closure at FINITE truncation: the pilot's
η-sequence is truncated past K = 3, with the tail zeroed out via
`truncated_const_3`.  This is a uniform-in-N bound, but with the
"infinite" trajectory artificially truncated.

This module proves the closure for an **untruncated** sequence (η_k
defined for ALL k ∈ ℕ), which is what "genuine infinite-trajectory"
means.  The catch: in the UV direction, η_k = 0 for all k (because
K_∩ is non-increasing as g decreases; see
`computations/uv_trajectory.py` and `tests/test_uv_trajectory.py` for
the empirical confirmation and theoretical explanation).  So the
infinite-trajectory closure is the trivial closure `Σ_{k=0}^∞ 0 = 0
< σ̂_0`, but it IS the infinite-trajectory closure — no truncation.

# Why this matters for Phase 7

Phase 7 (continuum limit) requires showing σ̂_∞ > 0 as a *limit* of
σ̂_k under the UV-direction RG flow.  The infrastructure here — a
Lean-verified infinite-trajectory σ̂-budget at finite-K truncation
of arbitrary K, plus the trivial-UV-η fact — is the analytic
precondition for Phase 7.1.

# The non-trivial case (open follow-on)

The "non-trivially-decaying η_k" scenario — where η_k > 0 but decays
geometrically — would arise from a near-threshold UV trajectory or a
modified σ̂-transport that doesn't clip Δ_∩ at 0.  Formalizing that
case in Lean requires `geometric_tail_closure_strong` from
`Geometric.lean` (currently a framework stub, deferred to Milestone
6.2-extension; see the "Open work" note in `Geometric.lean`).  In the
meantime, this module delivers the closure for the genuine-zero case
that the UV trajectory actually produces.

# Lean axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` only.
-/

import YMGap.Constructive.Geometric

namespace YMGap.RG.SigmaHatPilotUV

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## UV-pilot data

The UV trajectory's η-sequence is identically zero, per the empirical
verification in `tests/test_uv_trajectory.py::test_eta_k_vanishes_in_uv_direction`
(canonical, g_0 = 0.30, K = 10 — all η_k = 0.0 exactly at floating-point
precision; the analytical claim is `η_k = c_polymer · Δ_∩ / A_min` with
`Δ_∩ = max(0, K_∩(g_next) - K_∩(g)) = 0` since K_∩ is non-increasing
in g for UV-direction trajectories). -/

/-- The UV-pilot η-sequence: identically zero. -/
def eta_pilot_uv : QSeq := fun _ => 0

/-- σ̂_0 for the UV wire-in: `1 : Q'` (matching SigmaHatPilot). -/
def sigma_hat_0_pilot_uv : Q' := 1

/-! ## Nonnegativity and uniform partial-sum bound -/

/-- Every element of `eta_pilot_uv` is nonneg (trivially: equal to 0). -/
theorem eta_pilot_uv_nonneg : ∀ k, (0 : Q') ≤ eta_pilot_uv k := by
  intro _
  show (0 : Q') ≤ (0 : Q')
  exact Q'.le_refl' _

/-- Uniform partial-sum bound: `∀ N, finSum eta_pilot_uv N ≤ 0`.

Proof: `finSum (fun _ => 0) N = 0` (by `finSum_zero_seq`), and `0 ≤ 0`
by `Q'.le_refl'`. -/
theorem eta_pilot_uv_partial_sum_bound :
    ∀ N, finSum eta_pilot_uv N ≤ (0 : Q') := by
  intro N
  show finSum (fun _ => (0 : Q')) N ≤ (0 : Q')
  rw [finSum_zero_seq]
  exact Q'.le_refl' _

/-- Closure condition: `0 ≤ sigma_hat_0_pilot_uv = 1`.  Trivially decidable. -/
theorem zero_le_sigma_hat_0_pilot_uv : (0 : Q') ≤ sigma_hat_0_pilot_uv := by
  show (0 : Int) * (1 : Int) ≤ (1 : Int) * (1 : Int)
  decide

/-! ## The genuine infinite-trajectory closure -/

/-- **SU(2) UV-direction pilot σ̂-budget closure (genuine infinite-trajectory).**

For every finite N (and equivalently, in the limit N → ∞ at the
semantics level), the partial sum `finSum eta_pilot_uv N ≤ σ̂_0`.

The sequence `eta_pilot_uv` is NOT truncated: it's defined for all
k ∈ ℕ and is identically zero, which is the genuine UV-direction
behavior per `computations/uv_trajectory.py` (Milestone 6.3).

Proof: composition of the uniform partial-sum bound (`= 0` for the
zero sequence) with the budget condition (`0 ≤ 1`) via
`sigma_hat_budget_closure`.

This is the FIRST Lean-verified σ̂-budget closure that handles the
genuinely-infinite trajectory (no `truncated_const_K` artifice).
For comparison, `SigmaHatPilot.eta_pilot_budget_closes` uses
`truncated_const_3` which zeroes the sequence past K = 3 explicitly;
here the sequence is intrinsically zero throughout.

Axiom-gate: `[propext]` only. -/
theorem eta_pilot_uv_budget_closes :
    ∀ N, finSum eta_pilot_uv N ≤ sigma_hat_0_pilot_uv :=
  sigma_hat_budget_closure eta_pilot_uv (0 : Q') sigma_hat_0_pilot_uv
    eta_pilot_uv_partial_sum_bound zero_le_sigma_hat_0_pilot_uv

/-- **Closure via `prefix_plus_tail_closure`** (alternative composition).

Same closure as `eta_pilot_uv_budget_closes` but routed through the
Phase-3 infinite-trajectory framework `prefix_plus_tail_closure` with
K_0 = 0 (no prefix; the entire trajectory is "tail").  Confirms the
framework composes for the genuine UV case. -/
theorem eta_pilot_uv_budget_closes_via_prefix_tail :
    ∀ N, finSum eta_pilot_uv N ≤ sigma_hat_0_pilot_uv := by
  apply prefix_plus_tail_closure eta_pilot_uv 0 (0 : Q') sigma_hat_0_pilot_uv
  · exact eta_pilot_uv_nonneg
  · intro M
    show finSum eta_pilot_uv (0 + M) ≤ (0 : Q')
    -- 0 + M = M (Nat.zero_add)
    rw [Nat.zero_add]
    exact eta_pilot_uv_partial_sum_bound M
  · exact zero_le_sigma_hat_0_pilot_uv

/-- **Closure via `geometric_tail_via_input`** (Phase 6.2 framework).

Same closure routed through `Geometric.geometric_tail_via_input`,
demonstrating that the Phase 6.2 framework theorem composes with the
UV pilot (with bound = 0 in the trivially-zero case).  When
`geometric_tail_closure_strong` is built out (Milestone 6.2-extension),
non-trivially-decaying η-sequences will compose through the same
interface. -/
theorem eta_pilot_uv_budget_closes_via_geometric_framework :
    ∀ N, finSum eta_pilot_uv N ≤ sigma_hat_0_pilot_uv := by
  apply geometric_tail_via_input eta_pilot_uv 0 (0 : Q') sigma_hat_0_pilot_uv
  · exact eta_pilot_uv_nonneg
  · intro M
    show finSum eta_pilot_uv (0 + M) ≤ (0 : Q')
    rw [Nat.zero_add]
    exact eta_pilot_uv_partial_sum_bound M
  · exact zero_le_sigma_hat_0_pilot_uv

end YMGap.RG.SigmaHatPilotUV

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.SigmaHatPilotUV.eta_pilot_uv
#print axioms YMGap.RG.SigmaHatPilotUV.sigma_hat_0_pilot_uv
#print axioms YMGap.RG.SigmaHatPilotUV.eta_pilot_uv_nonneg
#print axioms YMGap.RG.SigmaHatPilotUV.eta_pilot_uv_partial_sum_bound
#print axioms YMGap.RG.SigmaHatPilotUV.zero_le_sigma_hat_0_pilot_uv
#print axioms YMGap.RG.SigmaHatPilotUV.eta_pilot_uv_budget_closes
#print axioms YMGap.RG.SigmaHatPilotUV.eta_pilot_uv_budget_closes_via_prefix_tail
#print axioms YMGap.RG.SigmaHatPilotUV.eta_pilot_uv_budget_closes_via_geometric_framework
