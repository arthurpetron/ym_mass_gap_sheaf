/-
SU(2) UV-direction continuum-limit framework: σ̂_∞ > 0 at the Q' level.

Milestone 7.1 of `work_plan.md`.  Builds on the Phase-6.4
genuine-infinite-trajectory closure (`YMGap.RG.SigmaHatPilotUV`) to
establish the framework-level statement of σ̂_∞ > 0 for the UV-direction
SU(2) pilot.

# What "σ̂_∞ > 0 at the framework level" means here

A genuine constructive σ̂_∞ would live in a constructive-reals layer
(Cauchy sequences of `Q'` with explicit modulus), which the project
hasn't built out yet.  Instead, this module gives the rational-Q'
form of the same statement:

  **Theorem (UV σ̂-trajectory bounded away from zero).**
  There exists `ε : Q'` with `0 < ε` such that for every `N : Nat`,
  the running σ̂_N := σ̂_0 - Σ_{k<N} η_k satisfies `ε ≤ σ̂_N`, i.e.
  ``finSum η N + ε ≤ σ̂_0``.

This is the precise rational analog of `σ̂_∞ ≥ ε > 0`: every partial
σ̂_N stays bounded below by the strictly-positive ε, so the limit
(however it's later constructed) inherits the positivity.

# Why this is the framework precursor to the mass gap

Phase 9's mass-gap theorem needs `σ̂_∞ > 0` to inject the area-law
bound `⟨W_R(C)⟩ ≤ C · exp(-σ̂_∞ · A(C))` into the continuum gauge
theory.  The current module proves the FRAMEWORK form (uniform Q'
lower bound on σ̂_N) for the UV pilot; the constructive-reals layer
that lifts this to a single `σ̂_∞ : Real` is scoped as Milestone 7.3.

# Scope honesty

  * **Delivered**: Q'-level uniform positive lower bound for the UV
    pilot's σ̂_N sequence; framework theorem
    `sigma_hat_uniform_positive_lower_bound` that any project pilot
    can call.
  * **Deferred** (Milestone 7.3 / constructive-reals layer): a single
    `σ̂_∞ : RealConstr` defined as the limit of the Cauchy σ̂_N
    sequence, with `0 < σ̂_∞`.  Requires `RealConstr.lean` (Cauchy
    sequences + decidable equality + ordering), not yet built.

# Lean axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` only.
-/

import YMGap.RG.SigmaHatPilotUV

namespace YMGap.Continuum.SigmaHatLimit

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.SigmaHatPilotUV

/-! ## Framework theorem: uniform positive lower bound on σ̂_N -/

/-- **Framework: uniform positive lower bound on σ̂_N**.

Given:
  * `η : QSeq` — the per-step σ̂-degradation sequence;
  * `bound σ_0 ε : Q'` — analytic parameters;
  * `h_eta_bound : ∀ N, finSum η N ≤ bound` — the uniform partial-sum
    bound (supplied by Phase-6 framework: `sigma_hat_budget_closure`,
    `prefix_plus_tail_closure`, or `geometric_tail_via_input`);
  * `h_gap : bound + ε ≤ σ_0` — the "ε-gap" between the budget bound
    and the initial σ̂_0,

conclude: `∀ N, finSum η N + ε ≤ σ_0`.

**Reading**: the running σ̂_N := σ_0 - finSum η N stays ≥ ε at every N.
The strict positivity of σ̂_N follows when ε itself is strictly positive
(supplied by the caller as a separate fact).

**Proof**: monotone composition.  `finSum η N + ε ≤ bound + ε` by
right-monotonicity of `+` on `≤` (from `h_eta_bound N`), then
`bound + ε ≤ σ_0` by `h_gap`, then transitivity. -/
theorem sigma_hat_uniform_positive_lower_bound
    (η : QSeq) (bound σ_0 ε : Q')
    (h_eta_bound : ∀ N, finSum η N ≤ bound)
    (h_gap : bound + ε ≤ σ_0) :
    ∀ N, finSum η N + ε ≤ σ_0 := by
  intro N
  have h_step : finSum η N + ε ≤ bound + ε :=
    Q'.add_le_add_right _ _ ε (h_eta_bound N)
  exact Q'.le_trans' _ _ _ h_step h_gap

/-! ## UV-pilot σ̂_∞ > 0 (framework form)

For the UV pilot (`eta_pilot_uv ≡ 0`, `σ̂_0 = 1`), the canonical
ε-gap is `ε = 1` itself: every partial sum is 0, so `0 + 1 ≤ 1`
holds trivially, and σ̂_N = 1 stays at least 1 at every N. -/

/-- The UV pilot's ε-gap to the σ̂_0 budget: take `ε = 1`, leaving
σ̂_N ≥ 1 at every N (since `finSum eta_pilot_uv N = 0`). -/
def sigma_hat_uv_epsilon : Q' := 1

/-- `0 < sigma_hat_uv_epsilon`. -/
theorem zero_lt_sigma_hat_uv_epsilon : (0 : Q') < sigma_hat_uv_epsilon := by
  show (0 : Int) * (1 : Int) < (1 : Int) * (1 : Int)
  decide

/-- **UV-pilot σ̂_∞ > 0 (framework form).**

For the genuine-infinite-trajectory UV pilot (`eta_pilot_uv : QSeq` is
identically zero per `SigmaHatPilotUV.eta_pilot_uv_partial_sum_bound`),
there exists `ε : Q'` with `0 < ε` such that the running σ̂_N satisfies
`finSum eta_pilot_uv N + ε ≤ sigma_hat_0_pilot_uv` for every `N`.

**Reading**: σ̂_N := 1 - finSum eta_pilot_uv N stays ≥ 1 at every N
(trivially: the subtracted term is 0).  The positive ε = 1 is the
strict-positivity witness needed to inject `σ̂_∞ > 0` into the future
constructive-reals layer (Milestone 7.3).

**Proof**: composition of `sigma_hat_uniform_positive_lower_bound`
with `eta_pilot_uv_partial_sum_bound` (bound = 0) and the decidable
gap `0 + 1 ≤ 1`. -/
theorem sigma_hat_uv_limit_positive :
    ∃ ε : Q',
      (0 : Q') < ε ∧
      (∀ N, finSum eta_pilot_uv N + ε ≤ sigma_hat_0_pilot_uv) := by
  refine ⟨sigma_hat_uv_epsilon, zero_lt_sigma_hat_uv_epsilon, ?_⟩
  apply sigma_hat_uniform_positive_lower_bound
    eta_pilot_uv (0 : Q') sigma_hat_0_pilot_uv sigma_hat_uv_epsilon
  · exact eta_pilot_uv_partial_sum_bound
  · -- 0 + 1 ≤ 1 (= sigma_hat_0_pilot_uv); both decidable at Q' = Int/Nat.
    show (0 : Q') + sigma_hat_uv_epsilon ≤ sigma_hat_0_pilot_uv
    decide

/-! ## Direct unfolded form

A useful corollary: pulled-out form without the existential, suited for
downstream calls that already know the witness ε = 1. -/

/-- **Direct uniform positive lower bound for the UV pilot.**

The unpacked form of `sigma_hat_uv_limit_positive`: for every `N`,
`finSum eta_pilot_uv N + 1 ≤ 1`.  Equivalently, σ̂_N ≥ 1 throughout
the UV trajectory.

Proof: extract from `sigma_hat_uv_limit_positive`, or prove directly
via `eta_pilot_uv_partial_sum_bound` + `decide`. -/
theorem sigma_hat_uv_partial_lower_bound :
    ∀ N, finSum eta_pilot_uv N + (1 : Q') ≤ sigma_hat_0_pilot_uv := by
  apply sigma_hat_uniform_positive_lower_bound
    eta_pilot_uv (0 : Q') sigma_hat_0_pilot_uv (1 : Q')
  · exact eta_pilot_uv_partial_sum_bound
  · decide

end YMGap.Continuum.SigmaHatLimit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SigmaHatLimit.sigma_hat_uniform_positive_lower_bound
#print axioms YMGap.Continuum.SigmaHatLimit.sigma_hat_uv_epsilon
#print axioms YMGap.Continuum.SigmaHatLimit.zero_lt_sigma_hat_uv_epsilon
#print axioms YMGap.Continuum.SigmaHatLimit.sigma_hat_uv_limit_positive
#print axioms YMGap.Continuum.SigmaHatLimit.sigma_hat_uv_partial_lower_bound
