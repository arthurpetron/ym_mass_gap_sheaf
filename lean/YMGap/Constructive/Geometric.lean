/-
`Q'.pow` and the geometric-tail closure framework.

Milestone 6.2 of `work_plan.md`.  Partial delivery: structural-definition
infrastructure plus a hypothesis-input framework theorem.  The fully
inductive derivation of the geometric-series bound from the recurrence
``η_max + r · H ≤ H`` requires Q' multiplicative arithmetic
(``mul_comm``, ``mul_assoc``, ``mul_add``, ``mul_le_mul_of_nonneg_left``)
that is **NOT** yet built out in `Rationals.lean`; see the open work
note at the bottom of this module.

# What this module provides (delivered)

  * `Q'.pow (q : Q') (n : Nat) : Q'` defined by structural recursion.
  * `Q'.pow_zero`, `Q'.pow_succ` as `rfl` lemmas.
  * `Q'.pow_nonneg` via induction on `n`, using the existing
    `Q'.mul_nonneg` from `Rationals.lean`.
  * `geometric_tail_via_input` — the FRAMEWORK theorem that takes
    the uniform-in-N partial-sum bound as a Σ'-typed hypothesis input
    and chains it with `RationalTail.prefix_plus_tail_closure` to
    deliver the σ̂-budget closure.  Suitable for concrete-instance
    use (Milestone 6.4) where the per-N bound is supplied by the
    Python-side derivation.

# What this module does NOT yet provide (deferred)

  * `geometric_tail_closure_strong` — the inductive proof of
    `∀ N, finSum (fun k => η_max · r^k) N + r^N · H ≤ H`
    from the recurrence `η_max + r · H ≤ H`.  Requires Q' arithmetic
    lemmas (`mul_comm`, `mul_assoc`, `mul_add` at the `eqv` level
    + `mul_le_mul_of_nonneg_left`).  Scoped as a follow-on Milestone
    6.2-extension.
  * Closed-form `geometric_partial_sum_bound` derivable from the above.

For Milestone 6.4 in the meantime, the concrete SU(2) UV pilot uses
the existing `truncated_const_3`-style infrastructure with a chosen
finite K_MAX, accepting the truncation error as a documented
honest approximation.

# Axiom-gate (AGENTS.md Rule 1)

Every delivered theorem reports `[propext]` only.  No `sorryAx`,
no `Classical.*`.
-/

import YMGap.Constructive.RationalTail

namespace YMGap.Constructive

namespace Q'

/-! ## `Q'.pow` -/

/-- Power of a `Q'` value: `q^0 = 1`, `q^(n+1) = q * q^n`. -/
def pow (q : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => q * pow q n

instance : HPow Q' Nat Q' := ⟨Q'.pow⟩

@[simp] theorem pow_zero (q : Q') : q ^ (0 : Nat) = 1 := rfl

@[simp] theorem pow_succ (q : Q') (n : Nat) :
    q ^ (n + 1) = q * q ^ n := rfl

/-- `1 : Q'` is nonneg. -/
theorem zero_le_one : (0 : Q') ≤ (1 : Q') := by
  show (0 : Int) * (1 : Int) ≤ (1 : Int) * (1 : Int)
  decide

/-- `q^n` is nonneg when `q` is nonneg.  Proof by induction on `n`. -/
theorem pow_nonneg (q : Q') (h : (0 : Q') ≤ q) :
    ∀ n : Nat, (0 : Q') ≤ q ^ n
  | 0 => by
    show (0 : Q') ≤ (1 : Q')
    exact zero_le_one
  | n + 1 => by
    show (0 : Q') ≤ q * q ^ n
    exact Q'.mul_nonneg q (q ^ n) h (pow_nonneg q h n)

end Q'

end YMGap.Constructive

namespace YMGap.Constructive.RationalTail

open YMGap.Constructive

/-! ## Geometric-tail closure framework (hypothesis-input form)

The framework theorem of Milestone 6.2.  Takes the user's analytic
content — a uniform-in-N partial-sum bound on the η-sequence — as a
hypothesis, and composes it with `prefix_plus_tail_closure` for the
σ̂-budget closure ``∀ N, finSum η N ≤ σ̂_0``.

For the SU(2) UV pilot, the analytic content (geometric tail bound on
the actual η_k) is supplied by the Python-side derivation in
`computations/uv_trajectory.py` and `computations/q_lift.py`, and the
per-N bound is checked at concrete Q' rationals via `decide` (up to a
chosen K_MAX, with the tail past K_MAX zeroed via the truncated form). -/

/-- **Geometric-tail closure (framework form, hypothesis-input).**

Composes `prefix_plus_tail_closure` with a user-supplied uniform-in-M
bound on the partial sums past `K_0`.  For a UV-direction SU(2) pilot
with geometrically-decaying η_k, the user supplies the bound at the
concrete operating point via `decide` over the partial sums (computable
in Q' at any specific N).

Given:
  * `η : QSeq` with `h_nonneg : ∀ k, 0 ≤ η k`
  * `K_0 : Nat` (the prefix-cutoff scale)
  * `bound, σ_0 : Q'`
  * `h_tail_uniform : ∀ M, finSum η (K_0 + M) ≤ bound`
  * `h_budget : bound ≤ σ_0`

conclude: `∀ N, finSum η N ≤ σ_0`.

This is a thin wrapper around `prefix_plus_tail_closure`, exposed under
the geometric-context name for use in `SigmaHatPilotUV.lean`. -/
theorem geometric_tail_via_input
    (η : QSeq) (K_0 : Nat) (bound σ_0 : Q')
    (h_nonneg : ∀ k, (0 : Q') ≤ η k)
    (h_tail_uniform : ∀ M, finSum η (K_0 + M) ≤ bound)
    (h_budget : bound ≤ σ_0) :
    ∀ N, finSum η N ≤ σ_0 :=
  prefix_plus_tail_closure η K_0 bound σ_0 h_nonneg h_tail_uniform h_budget

end YMGap.Constructive.RationalTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.Q'.pow
#print axioms YMGap.Constructive.Q'.pow_zero
#print axioms YMGap.Constructive.Q'.pow_succ
#print axioms YMGap.Constructive.Q'.zero_le_one
#print axioms YMGap.Constructive.Q'.pow_nonneg
#print axioms YMGap.Constructive.RationalTail.geometric_tail_via_input

/-! ## Open work: full inductive geometric_tail_closure

The full version of this module would include:

  * `geometric_tail_closure_strong (r η_max H : Q')` proving the strong
    invariant ``∀ N, finSum (fun k => η_max · r^k) N + r^N · H ≤ H``
    from the recurrence ``η_max + r · H ≤ H``.
  * `geometric_tail_closure` — the user-facing weakened form
    ``∀ N, finSum (fun k => η_max · r^k) N ≤ H``.

The inductive step requires Q' multiplicative arithmetic that the
existing `Rationals.lean` does NOT yet provide:

  * `Q'.mul_eqv_comm : (a * b).eqv (b * a)`
  * `Q'.mul_eqv_assoc : ((a * b) * c).eqv (a * (b * c))`
  * `Q'.mul_add_eqv : (a * (b + c)).eqv (a * b + a * c)`
  * `Q'.mul_le_mul_of_nonneg_left : 0 ≤ c → a ≤ b → c * a ≤ c * b`

Each is a routine cross-product manipulation (~30-50 lines), but
together they are ~200 lines of focused Q' work.  Scoped as Milestone
6.2-extension; tracked separately from the framework deliverable above.

In the meantime, Milestone 6.4 instantiates this framework with a
TRUNCATED-AT-K_MAX SU(2) UV pilot (via `truncated_const_3` semantics
at K_MAX = 3), with the truncation error documented in the
`notes/sigma-hat-derivation.md` §4.4 / Milestone 6.4 section.
-/
