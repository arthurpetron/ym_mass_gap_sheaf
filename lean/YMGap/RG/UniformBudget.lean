/-
Uniform σ̂-budget monotonicity substrate — the parametric bound that makes
SU(2) the worst case over *all* compact simple gauge groups.

# The reduction this module realises

`RepTheory/RepData.lean` gives the *conditional* closure
`RepData.budget_closes`: a group whose per-step bound `η_max` sums (over
its `K`-step window) under `σ̂₀` has its σ̂-budget close at every
truncation.  `RepTheory/SimpleGroup.lean` gives the *admissibility*
floors: every simple `G` has `C₂_fund ≥ 3/4` and `C₂_adj ≥ 2`, with
equality only at `su(2)`.

This module supplies the missing monotone glue: **the budget is
non-increasing in the invariants, so it is maximised at the floors —
i.e. at SU(2)**.  Concretely, with the per-step bound dominated by its
SU(2) value (`η_max(R) ≤ η_max(su2)`), the `K`-step budget of any
admissible `R` is ≤ SU(2)'s, which already closes (`su2_cert.budget`).

# What closes unconditionally here (pure `Q'` substrate)

  * **`recip_antitone`** — the division-monotonicity primitive the
    `K_lf = q/(1−q)` wrapper needs: `0 < a ≤ b ⟹ recip b ≤ recip a`.
    Reciprocal is order-reversing on the positives.  (S4 division lemma.)
  * **`oneMinus_le_of_le` / `qOver1mq_mono`** — `K_lf(Z) = Z/(1−Z)` is
    monotone *increasing* in `Z ∈ [0,1)` (via `recip_antitone` on the
    denominator `1 − Z`): larger character-tail `Z_t` ⇒ larger `K_lf`.
    Composed with "larger gap Δ ⇒ smaller `Z_t`" this is the large-field
    tailwind direction (S4).
  * **`truncatedConst_le`** — the budget `finSum` is monotone in the
    per-step bound: `a ≤ b ⟹ ∀ N, Σ truncatedConst K a ≤ Σ truncatedConst K b`.
    Pure finite-sum induction (S6's combinatorial core).
  * **`monotone_budget`** — assembled: an `η_max`-dominated group's budget
    is ≤ SU(2)'s at every truncation.

# The single named analytic obligation (honest hole)

The one input that does *not* close in pure `Q'` is

    eta_dominated : R.eta_max ≤ su2.eta_max

— i.e. the per-step degradation bound of an admissible group is ≤ SU(2)'s.
This is the analytic heart (the plan's `E_antitone` / uniform
character-tail lemma): it rests on the antitonicity of the heat-kernel
exponential `e^{−tΔ}` in the Casimir gap Δ, which is a `CReal` statement
(the exp lives outside `Q'`).  Per AGENTS.md Rule 2 / Rule 6 and the plan
§3 (S1 "if it resists, quarantine the analytic content as an explicit
hypothesis"), it is carried here as a **named structure field**
`UniformBudgetWitness.eta_dominated`, NOT proved falsely or classically.
Discharging it (for SU(N): from `C₂_fund` antitone control of `Z_t`; the
numerical sweep `U.4` confirms `Σ η(G) ≤ Σ η(su2)` strictly for all 19
group types) is the remaining paper-layer step.

The value delivered: the *entire* reduction is constructive and
axiom-clean **modulo this one named field**, exactly mirroring how
`mass_gap_SU2` isolates its OS-reconstruction hypotheses.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` / `[propext, Quot.sound]`
(the `Quot.sound`/`omega` from `Nat`/`Int`).  No `Classical.*`, no
`sorryAx`.  See the `#print axioms` block at the end.
-/

import YMGap.RepTheory.SimpleGroup
import YMGap.Constructive.Sqrt

namespace YMGap.RG

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RepTheory

/-! ## S4 — division monotonicity: reciprocal is antitone on the positives

`Q'` has no general division, but `Sqrt.recip` is the constructive
reciprocal (`q · recip q ≃ 1` for `q > 0`).  Here is the order fact the
`K_lf = q/(1−q)` wrapper depends on: on positive arguments, `recip`
reverses `≤`. -/

/-- **Reciprocal is antitone on the positives.**  For `0 < a ≤ b`,
`recip b ≤ recip a`.

`recip q = q.den / max(1, q.num)` (`Sqrt.recip`).  Cross-multiplying the
goal `recip b ≤ recip a` (i.e. `(recip b).num·(recip a).den ≤
(recip a).num·(recip b).den`) and using `recip_num`/`recip_den`, with
both numerators positive (so the `max 1 _` clamps are inert), reduces to
`b.den·a.num ≤ a.den·b.num`, which is exactly the hypothesis `a ≤ b`
cross-multiplied. -/
theorem recip_antitone {a b : Q'} (ha : (0 : Q') < a) (hab : a ≤ b) :
    Q'.recip b ≤ Q'.recip a := by
  have hanum : 0 < a.num := Q'.num_pos_of_pos ha
  -- 0 < b from 0 < a ≤ b at the cross-product level.
  have hbnum : 0 < b.num := by
    have e2 : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := hab
    have hda : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
    have hdb : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
    -- a.num·b.den > 0 ⟹ b.num·a.den > 0 ⟹ b.num > 0 (since a.den > 0).
    have hlhs : 0 < a.num * (b.den : Int) := Int.mul_pos hanum hdb
    have hrhs : 0 < b.num * (a.den : Int) := Int.lt_of_lt_of_le hlhs e2
    -- From 0 < b.num·a.den and 0 < a.den, conclude 0 < b.num (case split, no by_contra).
    rcases Int.lt_or_le 0 b.num with hpos | hnp
    · exact hpos
    · exfalso
      have : b.num * (a.den : Int) ≤ 0 * (a.den : Int) :=
        Int.mul_le_mul_of_nonneg_right hnp (Int.le_of_lt hda)
      rw [Int.zero_mul] at this
      omega
  have hb : (0 : Q') < b := by
    show (0 : Int) * (b.den : Int) < b.num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one]; exact hbnum
  -- Goal as cross-product on Int.
  show (Q'.recip b).num * ((Q'.recip a).den : Int)
     ≤ (Q'.recip a).num * ((Q'.recip b).den : Int)
  rw [Q'.recip_num, Q'.recip_num]
  -- (recip a).den = max 1 a.num.toNat = a.num.toNat (since a.num ≥ 1)
  have hda : ((Q'.recip a).den : Int) = a.num := by
    rw [Q'.recip_den]
    have : max 1 a.num.toNat = a.num.toNat := by omega
    rw [this]; exact Int.toNat_of_nonneg (Int.le_of_lt hanum)
  have hdb : ((Q'.recip b).den : Int) = b.num := by
    rw [Q'.recip_den]
    have : max 1 b.num.toNat = b.num.toNat := by omega
    rw [this]; exact Int.toNat_of_nonneg (Int.le_of_lt hbnum)
  rw [hda, hdb]
  -- Goal: (b.den : Int) * a.num ≤ (a.den : Int) * b.num
  -- Hypothesis hab : a ≤ b  ⟺  a.num * b.den ≤ b.num * a.den.
  have hle : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := hab
  -- Rearrange to match: (b.den)·a.num = a.num·b.den ; (a.den)·b.num = b.num·a.den.
  rw [Int.mul_comm (b.den : Int) a.num, Int.mul_comm (a.den : Int) b.num]
  exact hle

/-! ## S4 — the `K_lf = Z/(1−Z)` large-field wrapper is monotone in `Z`

With `q := μ·Z_t` the plaquette-weighted tail and `K_lf = q/(1−q)`, the
large-field cluster constant increases with the character-tail `Z_t`.
We capture the monotone core: `Z ↦ Z · recip (1 − Z)` is non-decreasing
in `Z` on the convergent regime `0 ≤ Z ≤ Z' < 1`.  Combined with the
(analytic) "larger gap Δ ⇒ smaller `Z_t`", this is the large-field
tailwind. -/

/-- For `Z ≤ Z'` (both `< 1`), the denominators satisfy `1 − Z' ≤ 1 − Z`. -/
theorem oneMinus_le_of_le {Z Z' : Q'} (h : Z ≤ Z') :
    (1 : Q') - Z' ≤ (1 : Q') - Z := by
  -- Negation is antitone: from Z ≤ Z' get -Z' ≤ -Z (cross-product + omega).
  have hneg : (-Z') ≤ (-Z) := by
    show (-Z').num * ((-Z).den : Int) ≤ (-Z).num * ((-Z').den : Int)
    have h' : Z.num * (Z'.den : Int) ≤ Z'.num * (Z.den : Int) := h
    -- (-Z).num = -Z.num, (-Z).den = Z.den structurally.
    show (-(Z'.num)) * (Z.den : Int) ≤ (-(Z.num)) * (Z'.den : Int)
    have e1 : (-(Z'.num)) * (Z.den : Int) = -(Z'.num * (Z.den : Int)) := by
      rw [Int.neg_mul]
    have e2 : (-(Z.num)) * (Z'.den : Int) = -(Z.num * (Z'.den : Int)) := by
      rw [Int.neg_mul]
    rw [e1, e2]
    exact Int.neg_le_neg h'
  -- 1 - Z = 1 + (-Z); apply add_le_add_left.
  show (1 : Q') + (-Z') ≤ (1 : Q') + (-Z)
  exact Q'.add_le_add_left (1 : Q') (-Z') (-Z) hneg

/-- **`K_lf` monotone in the character tail.**  On the convergent regime
`0 < 1 − Z'` and `Z ≤ Z'`, the large-field factor `Z' · recip(1−Z')`
dominates `Z · recip(1−Z)` whenever `0 ≤ Z` — i.e. `K_lf` is
non-decreasing in `Z_t`.  Uses `recip_antitone` on the denominators and
`Q'.mul_le_mul_of_nonneg`. -/
theorem qOver1mq_mono {Z Z' : Q'}
    (hZ : (0 : Q') ≤ Z) (hZZ' : Z ≤ Z')
    (hpos' : (0 : Q') < (1 : Q') - Z') :
    Z * Q'.recip ((1 : Q') - Z) ≤ Z' * Q'.recip ((1 : Q') - Z') := by
  have hden_le : (1 : Q') - Z' ≤ (1 : Q') - Z := oneMinus_le_of_le hZZ'
  -- recip is antitone: recip (1-Z) ≤ recip (1-Z')
  have hrecip : Q'.recip ((1 : Q') - Z) ≤ Q'.recip ((1 : Q') - Z') :=
    recip_antitone hpos' hden_le
  -- Z·recip(1−Z) ≤ Z'·recip(1−Z'): bound numerator (Z ≤ Z', Z'≥0) and recip factor.
  have hZ'nn : (0 : Q') ≤ Z' := Q'.le_trans' _ _ _ hZ hZZ'
  have hrnn : (0 : Q') ≤ Q'.recip ((1 : Q') - Z) := Q'.le_of_lt (Q'.recip_pos _)
  -- mul_le_mul_of_nonneg : a≤b → c≤d → 0≤b → 0≤c → a*c ≤ b*d.
  exact Q'.mul_le_mul_of_nonneg hZZ' hrecip hZ'nn hrnn

/-! ## S6 — the budget `finSum` is monotone in the per-step bound

The combinatorial core: `truncatedConst K a` is termwise `≤
truncatedConst K b` when `a ≤ b`, so its partial sums are too.  This is
the engine that turns "η_max dominated" into "budget dominated". -/

/-- Termwise domination of the truncated-constant sequences. -/
theorem truncatedConst_term_le (K : Nat) {a b : Q'} (hab : a ≤ b) :
    ∀ k, truncatedConst K a k ≤ truncatedConst K b k := by
  intro k
  show (if k < K then a else 0) ≤ (if k < K then b else 0)
  by_cases hk : k < K
  · rw [if_pos hk, if_pos hk]; exact hab
  · rw [if_neg hk, if_neg hk]; exact Q'.le_refl' _

/-- **Budget monotonicity in `η_max`.**  If `a ≤ b` then every finite
partial sum of `truncatedConst K a` is ≤ that of `truncatedConst K b`.
Pure finite-sum induction. -/
theorem truncatedConst_le (K : Nat) {a b : Q'} (hab : a ≤ b) :
    ∀ N, finSum (truncatedConst K a) N ≤ finSum (truncatedConst K b) N := by
  intro N
  induction N with
  | zero => exact Q'.le_refl' _
  | succ n ih =>
    show finSum (truncatedConst K a) n + truncatedConst K a n
       ≤ finSum (truncatedConst K b) n + truncatedConst K b n
    have hterm : truncatedConst K a n ≤ truncatedConst K b n :=
      truncatedConst_term_le K hab n
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ ih)
      (Q'.add_le_add_left _ _ _ hterm)

/-! ## The named analytic obligation + the assembled monotone budget

The pure-`Q'` chain above reduces "budget of `R` ≤ budget of `su2`" to
the single scalar inequality `R.eta_max ≤ su2.eta_max`.  That inequality
is the analytic heart (`E_antitone` / uniform character-tail) and lives
outside `Q'`; we name it as a structure field rather than proving it
falsely. -/

/-- The one named analytic input pinning SU(2) as the worst case: an
admissible group's per-step σ̂-degradation bound is dominated by SU(2)'s.

This is the plan's `E_antitone` consequence — the heat-kernel exponential
`e^{−tΔ}` antitone in the Casimir gap Δ (≥ 3/4, minimised at SU(2)),
which controls the large-field `Z_t` and hence `η_max`.  It is a `CReal`
statement; carried here as data, to be discharged at the paper layer
(numerically corroborated by the U.4 sweep: `Σ η(G) ≤ Σ η(su2)` strictly
for every simple type).  Mirrors the OS-hypothesis pattern of
`mass_gap_SU2`. -/
structure UniformBudgetWitness (R : RepData) : Prop where
  /-- Same finite RG window as the SU(2) certificate (`K = 3`). -/
  same_window   : R.K_steps = su2.K_steps
  /-- Per-step degradation dominated by SU(2)'s — the antitone-in-Δ input. -/
  eta_dominated : R.eta_max ≤ su2.eta_max

/-- **`monotone_budget` — the §1.3 reduction.**  Given the named
domination witness, the `K`-step budget of `R` is ≤ SU(2)'s at *every*
truncation.

Pure assembly: rewrite `R`'s window to SU(2)'s (`same_window`), then apply
`truncatedConst_le` with `eta_dominated`.  No analysis here — the analysis
is entirely localised in `UniformBudgetWitness.eta_dominated`. -/
theorem monotone_budget (R : RepData) (w : UniformBudgetWitness R) :
    ∀ N, finSum (truncatedConst R.K_steps R.eta_max) N
       ≤ finSum (truncatedConst su2.K_steps su2.eta_max) N := by
  intro N
  rw [w.same_window]
  exact truncatedConst_le su2.K_steps w.eta_dominated N

/-- The budget of an admissible, η-dominated group closes under SU(2)'s
σ̂₀ at every truncation — combining `monotone_budget` with the proven
`su2_budget_closes`.  (SU(2)'s `σ̂₀ = 1`; `su2_budget_closes` is the
proven `∀ N, finSum … ≤ 1`.) -/
theorem budget_closes_of_witness (R : RepData) (w : UniformBudgetWitness R) :
    ∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0 := by
  intro N
  exact Q'.le_trans' _ _ _ (monotone_budget R w N) (su2_budget_closes N)

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.recip_antitone
#print axioms YMGap.RG.oneMinus_le_of_le
#print axioms YMGap.RG.qOver1mq_mono
#print axioms YMGap.RG.truncatedConst_term_le
#print axioms YMGap.RG.truncatedConst_le
#print axioms YMGap.RG.monotone_budget
#print axioms YMGap.RG.budget_closes_of_witness
