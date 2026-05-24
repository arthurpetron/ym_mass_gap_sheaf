/-
Rational tail bound module — the global σ̂ budget closure at Q'.

Phase-3 continuation of Milestone 3.4 (`computations/sigma_hat_trajectory.py`).
Provides the Q'-rational framework for the load-bearing global closure

    Σ_{k=0}^∞ η_k  <  σ̂_0

(`docs/outline.md` §10.4, `docs/context.md` §3.3 condition 4) at finite
truncation `N`.  Per the Decision-1 record (`notes/sigma-hat-derivation.md`
§4), the SU(2) pilot at finite `K` requires only a finite-K uniform
bound, which is constructively provable inside Q'.

# What this module provides

A `Q'`-rational framework for the σ̂-budget closure:

  - `QSeq` — a sequence of `Q'` values indexed by `Nat`.
  - `finSum f N` — the finite partial sum Σ_{k=0}^{N-1} f k.
  - `sigma_hat_budget_closure` — the framework theorem: given an η
    sequence, a uniform bound on its partial sums, and a closure-condition
    `eta_total_bound ≤ σ̂_0`, conclude `Σ_{k<N} η_k ≤ σ̂_0` for every N.

The "geometric rational tail" structure expected by the user is realized
NOT through an exponential decay assumption on `η_k` itself (which would
require Q'.pow and exponential-bound machinery) but through the
**telescoping-bounded** structure inherent in the Python derivation:
`η_k = c_η · (K_∩(k+1) - K_∩(k))` for monotone-bounded `K_∩`, so

    Σ_{k<N} η_k  =  c_η · (K_∩(N) - K_∩(0))  ≤  c_η · K_max.

The user supplies `eta_total_bound = c_η · K_max ∈ ℚ` and the closure
condition `eta_total_bound ≤ σ̂_0 ∈ ℚ`; the module discharges the rest
via `Q'.le_trans'`.

# What this module does NOT provide

- An infinite-K convergence proof.  Q' is countable-rational, not
  constructive-reals; "Σ_{k=0}^∞" is not directly representable.
  The framework is *uniform-in-N*: it proves `∀ N, Σ_{k<N} η_k ≤ σ̂_0`,
  which is the correct constructive form of the global claim at finite
  truncation (per `lean/YMGap/Constructive/Rationals.lean` module
  docstring §"Boundary" / `notes/sigma-hat-derivation.md` §4).
- A telescoping identity for general Q' sequences.  Q' equality is
  structural (not semantic), so `(a - b) + (b - c) = a - c` does not
  hold by `rfl` and requires either Q'.eqv or `Q'.reduce`.  The
  telescoping step is left to the user / a downstream module that
  needs it; here the framework just composes a user-supplied uniform
  partial-sum bound with the closure condition via transitivity.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing claim below ends in `Q'.le_trans'` (`[propext]`)
plus basic structural recursion.  No `sorryAx`, no `Classical.*`.
-/

import YMGap.Constructive.Rationals

namespace YMGap.Constructive.RationalTail

open YMGap.Constructive

/-! ## Q'-valued sequences and finite sums -/

/-- A sequence of `Q'` values indexed by `Nat`.

Models the per-step η trajectory (or Δ_∩ trajectory) of the σ̂ budget
closure.  The Python `compute_eta(g_k, g_k_next, t_choice)` returns a
single `Q'` value per `k`; aggregating across `k = 0, 1, …, K` gives
a `QSeq`. -/
def QSeq : Type := Nat → Q'

/-- The finite partial sum `Σ_{k=0}^{N-1} f k`.

Recursively: `finSum f 0 = 0`; `finSum f (N+1) = finSum f N + f N`.
Defined structurally; no axiom dependency. -/
def finSum (f : QSeq) : Nat → Q'
  | 0 => 0
  | n + 1 => finSum f n + f n

@[simp] theorem finSum_zero (f : QSeq) : finSum f 0 = 0 := rfl

@[simp] theorem finSum_succ (f : QSeq) (n : Nat) :
    finSum f (n + 1) = finSum f n + f n := rfl

/-- The constant-zero sequence sums to zero at every length. -/
theorem finSum_zero_seq (n : Nat) : finSum (fun _ => (0 : Q')) n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show finSum (fun _ => (0 : Q')) k + (0 : Q') = 0
    rw [Q'.add_zero']
    exact ih


/-! ## The σ̂-budget closure framework theorem

The Phase-3 load-bearing closure at finite truncation. -/


/-- **Global σ̂-budget closure** (Q' framework form).

Given:
  * `η : QSeq` — the per-step σ̂-degradation sequence;
  * `eta_total_bound : Q'` — a uniform upper bound on every partial sum;
  * `sigma_0 : Q'` — the initial dimensionless string tension;
  * `h_eta_bound : ∀ N, finSum η N ≤ eta_total_bound` — the partial-sum
    bound (analytic content: this is the telescoping-bounded form, supplied
    by the user / downstream from `K_∩` monotonicity + boundedness);
  * `h_budget : eta_total_bound ≤ sigma_0` — the closure condition,

conclude: `∀ N, finSum η N ≤ sigma_0`.

This is the global ``Σ_k η_k < σ̂_0`` claim of outline §10.4 at finite
truncation, expressed entirely in Q' (no constructive-reals layer).
The proof is a single transitivity step: each partial sum is bounded
by `eta_total_bound` (by hypothesis), and `eta_total_bound ≤ σ̂_0`
(by closure condition), so each partial sum is `≤ σ̂_0`. -/
theorem sigma_hat_budget_closure
    (η : QSeq) (eta_total_bound sigma_0 : Q')
    (h_eta_bound : ∀ N, finSum η N ≤ eta_total_bound)
    (h_budget : eta_total_bound ≤ sigma_0) :
    ∀ N, finSum η N ≤ sigma_0 :=
  fun N => Q'.le_trans' _ _ _ (h_eta_bound N) h_budget

/-! ## Smoke-test instance: zero-η trajectory

The trivially-closed pilot: an η sequence that is identically zero
(no σ̂ degradation per step) closes against any positive σ̂_0. -/

/-- For the zero-η sequence, every partial sum is `≤ 0` (in fact equals 0). -/
theorem zero_eta_bound (N : Nat) :
    finSum (fun _ => (0 : Q')) N ≤ (0 : Q') := by
  rw [finSum_zero_seq]
  exact Q'.le_refl' _

/-- **Smoke-test closure**: the zero-η sequence closes the budget against
σ̂_0 = 1.  Demonstrates that `sigma_hat_budget_closure` is callable with
real Q' values and discharges constructively. -/
theorem smoke_test_zero_eta_closes :
    ∀ N, finSum (fun _ => (0 : Q')) N ≤ (1 : Q') := by
  apply sigma_hat_budget_closure
  · -- eta partial sums all bounded by 0
    exact zero_eta_bound
  · -- 0 ≤ 1 in Q'
    show (0 : Int) * (1 : Int) ≤ (1 : Int) * (1 : Int)
    decide

/-! ## Pilot instance: constant-η trajectory

A more substantive instance.  For a constant η sequence `η k = η_0`
(every step contributes the same η_0), the partial sum after N steps
is `N · η_0`.  The closure requires `N · η_0 ≤ σ̂_0` uniformly — which
fails for any positive η_0 as N → ∞.  This honestly surfaces the
"need-for-telescoping-or-decay" boundary: a *constant* η sequence
does NOT admit a finite uniform bound, so the closure framework's
`eta_total_bound` hypothesis cannot be satisfied with a fixed Q' rational.

The substantive pilot (telescoping-bounded η from the SU(2) trajectory)
satisfies `eta_total_bound = c_η · K_max` with `K_max` finite, hence
admits closure — but only via the per-step bound supplied externally
(e.g. from a future `K_∩`-trajectory analysis module).

This instance below documents the inverse: a smoke test showing the
framework correctly handles a *bounded-trajectory* case via direct
witness, leaving the SU(2)-pilot integration as future work. -/

/-- A single-step η that bounds at η_0: the trivial bounded trajectory.

`finSum (single_step_eta η_0) N = if N = 0 then 0 else η_0`. -/
def single_step_eta (η_0 : Q') : QSeq := fun k => if k = 0 then η_0 else 0

/-- The single-step η has partial sum bounded by `η_0` from step 1 onward
(and 0 at step 0).  At every N, partial sum ≤ η_0 ∨ partial sum = 0. -/
theorem single_step_eta_partial_sum_bound
    (η_0 : Q') (h_η_nonneg : (0 : Q') ≤ η_0) (N : Nat) :
    finSum (single_step_eta η_0) N ≤ η_0 := by
  match N with
  | 0 =>
    -- finSum _ 0 = 0 ≤ η_0 (by hypothesis)
    show (0 : Q') ≤ η_0
    exact h_η_nonneg
  | n + 1 =>
    -- finSum f (n+1) = finSum f n + f n.  We'll show this equals η_0 when
    -- n = 0, and equals (prev sum) when n > 0; in either case ≤ η_0.
    -- For the smoke test we proceed by induction on the structure.
    show finSum (single_step_eta η_0) n + single_step_eta η_0 n ≤ η_0
    -- Use a separate inductive lemma that handles the structure cleanly.
    -- Below: a direct argument splitting on n.
    match n with
    | 0 =>
      -- finSum (...) 0 + (single_step η_0) 0 = 0 + η_0 = η_0.
      show (0 : Q') + (single_step_eta η_0) 0 ≤ η_0
      have h_step_zero : single_step_eta η_0 0 = η_0 := by
        show (if (0 : Nat) = 0 then η_0 else 0) = η_0
        simp
      rw [h_step_zero, Q'.zero_add']
      exact Q'.le_refl' _
    | k + 1 =>
      -- single_step_eta η_0 (k+1) = 0 since k+1 ≠ 0.
      -- finSum at (k+1) = (finSum at k) + 0 = (finSum at k) ≤ η_0 (by ind hyp).
      show finSum (single_step_eta η_0) (k + 1) + single_step_eta η_0 (k + 1) ≤ η_0
      have h_zero : single_step_eta η_0 (k + 1) = 0 := by
        show (if (k + 1 : Nat) = 0 then η_0 else 0) = 0
        simp
      rw [h_zero, Q'.add_zero']
      exact single_step_eta_partial_sum_bound η_0 h_η_nonneg (k + 1)

/-- **Pilot closure**: for a single-step η at value `η_0 ≥ 0`, the budget
closes against any `σ̂_0 ≥ η_0`. -/
theorem single_step_eta_closes
    (η_0 sigma_0 : Q')
    (h_η_nonneg : (0 : Q') ≤ η_0)
    (h_budget : η_0 ≤ sigma_0) :
    ∀ N, finSum (single_step_eta η_0) N ≤ sigma_0 :=
  sigma_hat_budget_closure (single_step_eta η_0) η_0 sigma_0
    (single_step_eta_partial_sum_bound η_0 h_η_nonneg)
    h_budget

end YMGap.Constructive.RationalTail

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.RationalTail.finSum
#print axioms YMGap.Constructive.RationalTail.finSum_zero
#print axioms YMGap.Constructive.RationalTail.finSum_succ
#print axioms YMGap.Constructive.RationalTail.finSum_zero_seq
#print axioms YMGap.Constructive.RationalTail.sigma_hat_budget_closure
#print axioms YMGap.Constructive.RationalTail.zero_eta_bound
#print axioms YMGap.Constructive.RationalTail.smoke_test_zero_eta_closes
#print axioms YMGap.Constructive.RationalTail.single_step_eta
#print axioms YMGap.Constructive.RationalTail.single_step_eta_partial_sum_bound
#print axioms YMGap.Constructive.RationalTail.single_step_eta_closes
