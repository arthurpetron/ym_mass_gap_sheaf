/-
Track B / R2 — **the codynamic gap: the surviving floor as a flow invariant**.

# The right lens (read first)

A *static* "gap at coupling `w`" is the wrong object.  The natural static
character margin `(1 − c₁)²/(1 + c₁²)` CROSSES ZERO through the intermediate
weak-coupling "middle" (it vanishes at `w ≈ 0.794`), so no fixed-scale spectral
quantity survives the whole trajectory.  That zero-crossing is a static-endpoint
ARTIFACT, not a property of the renormalization flow.

The genuine object is the **codynamic gap**: the gap that SURVIVES the RG flow's
accumulated degradation BUDGET.  It is a `ClosureWitness` on a `BudgetObj`
(`Categorical.CodynCat`): a strictly positive `g` with `budget + g ≤
initial_bound`, where `budget` is a uniform bound on the partial sums of the
per-step DEGRADATION.  The per-step degradation here is the renormalized
bond-moving defect `renDefect ∝ (1 − w)²` — QUADRATIC, hence SUMMABLE, with NO
zero-crossing through the middle (it is a nonnegative loss that merely shrinks).
That summability is already PROVED (`SummabilityCapstone.renDefect_summable`);
this module assembles it as the genuine codynamic object and reframes the open
obligation in flow form.

# What this module delivers

  * `rgFlowBudget : BudgetObj` — the SU(2) dominant-mode RG TAIL flow
    (`k ≥ k₀`), with `degradation` = the real `renDefect`, `budget` = the PROVED
    tail-sum bound, `budget_summable` DISCHARGED from `renDefect_summable`, and
    `initial_bound` = the exact single-link heat-semigroup gap `3/4`
    (`PerScaleContraction.su2CasimirGap`).
  * `rgFlowClosure : ClosureWitness rgFlowBudget` — PROVED: the surviving gap
    `g = 3/4 − budget > 0` with `budget + g ≤ 3/4`.  THE codynamic gap.
  * `codynamicGap`, `codynamicGap_pos`, `codynamicGap_terminal` — the gap as a
    transported flow invariant, positive at every flow truncation.
  * `rgFlowBudget'` + `rgFlowBudget'_to_rgFlowBudget : BudgetHom …` +
    `codynamicGap_transported` — the categorical payoff: the SAME surviving gap
    transports along a genuine `BudgetHom` to an easier flow (`transportClosure`).
  * `CodynamicExactIdentification` (UNINHABITED) + `codynamic_gap_of_exact` —
    the OPEN obligation reframed in FLOW form: that the approximate dominant-mode
    `renDefect` bounds the EXACT physical per-scale gap loss (the Balaban
    RG-control question).  GIVEN that, the physical codynamic gap is positive —
    the reduction PROVED; only the identification open.

# SCOPE — what this is and is NOT (CRITICAL honesty)

The codynamic gap built here is positive for the PROVED **approximate**
dominant-mode tail flow:

  * DOMINANT MODE ONLY (`s = 1`) — `renDefect` is the `s = 1` transverse residual.
  * RENORMALIZED defect — marginal drift absorbed by the `s = 1` retuning.
  * TAIL `k ≥ k₀` — the finite head is honestly excluded.
  * CANONICAL (non-4D) AF inhabitant — a concrete witness trajectory.

It is NOT the physical 4D Yang–Mills mass gap.  The physical gap requires
`CodynamicExactIdentification` (the approximate flow defect dominating the EXACT
per-scale loss along the GENUINE 4D AF trajectory, all modes) — left UNINHABITED.
The conceptual advance is that the OPEN obligation is now a WELL-BEHAVED FLOW
quantity (`renDefect ∝ (1 − w)²`, summable, no zero-crossing) rather than the
pathological static margin — better-positioned, still open.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over `Q'`/`Nat`; every load-bearing declaration gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.  All data is `Type`-level.
-/

import YMGap.Categorical.CodynCat
import YMGap.Continuum.SummabilityCapstone
import YMGap.Continuum.PerScaleContraction
import YMGap.Constructive.CharacterTail

namespace YMGap.Continuum.CodynamicGap

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Categorical
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SummabilityCapstone

/-! ## 0. The canonical tail-flow data

We fix the canonical AF inhabitant and the proved bond-moving multiplicity
`p = 1` (the minimal genuine value; `renDefect … 0 = 4 > 0`, so the flow is
non-degenerate).  `k₀ = defectCutoff` is the proved tail cutoff where
`renDefect ≤ 1/2`. -/

/-- The canonical (non-4D) AF trajectory. -/
def afr : AFRateModulus := afRateModulus_canonical

/-- The proved bond-moving multiplicity (minimal genuine value). -/
def pMult : Nat := 1

/-- The proved tail cutoff `k₀` (where `renDefect ≤ 1/2`).  Concretely `144`. -/
def k0 : Nat := defectCutoff afr pMult

/-- The per-step tail degradation: the REAL renormalized dominant-mode defect,
shifted to the tail `k ≥ k₀`.  This is `renDefect`, not a posited sequence. -/
def tailDegradation : QSeq := fun k => renDefect afr pMult (k0 + k)

/-- The PROVED tail-sum bound `R(k₀) = Aconst · pot 2 k₀`.  Concretely `72/145`. -/
def tailBudget : Q' := Aconst afr pMult * pot 2 (by decide) k0

/-! ## 1. `finSum` of the shifted degradation IS the defect's `tailSum`

`finSum` and `tailSum` have the same recursion shape; on the shifted sequence
`fun k => renDefect (k₀+k)` the partial sum equals `tailSum renDefect k₀`,
which `renDefect_summable` bounds.  (Same induction as
`SummabilityCapstone.lossSum_shift_eq`, re-derived for `finSum`.) -/

/-- `finSum tailDegradation N = tailSum (renDefect afr pMult) k₀ N` for all `N`. -/
theorem finSum_tailDegradation_eq :
    ∀ N, finSum tailDegradation N = tailSum (renDefect afr pMult) k0 N
  | 0 => rfl
  | N + 1 => by
    show finSum tailDegradation N + renDefect afr pMult (k0 + N)
        = tailSum (renDefect afr pMult) k0 N + renDefect afr pMult (k0 + N)
    rw [finSum_tailDegradation_eq N]

/-- **The summability discharge.**  Every partial sum of the tail degradation is
bounded by `tailBudget`, directly from the PROVED `renDefect_summable`.  This is
the `BudgetObj.budget_summable` field. -/
theorem tailDegradation_summable (N : Nat) :
    finSum tailDegradation N ≤ tailBudget := by
  rw [finSum_tailDegradation_eq N]
  exact renDefect_summable afr pMult k0 N

/-! ## 2. `rgFlowBudget` — the codynamic gap OBJECT (genuine) -/

/-- **The RG tail-flow budget object.**  The SU(2) dominant-mode RG tail flow as
a `CodynCat.BudgetObj`:

  * `degradation` = the REAL renormalized defect `renDefect` (tail-shifted);
  * `budget` = the PROVED tail-sum bound `Aconst · pot 2 k₀` (`= 72/145`);
  * `budget_summable` = DISCHARGED from `renDefect_summable`;
  * `initial_bound` = the EXACT single-link heat-semigroup gap `3/4`
    (`su2CasimirGap`), the gap at the tail start.

Nothing here is posited: the degradation is the proved quadratic defect and the
budget is its proved summability bound. -/
def rgFlowBudget : BudgetObj where
  degradation := tailDegradation
  initial_bound := su2CasimirGap
  budget := tailBudget
  budget_summable := tailDegradation_summable

/-! ## 3. `rgFlowClosure` — the codynamic gap, PROVED

`budget = 72/145 < 3/4 = initial_bound` (genuine quantitative check by `decide`
on the concrete canonical rationals).  Hence `g := initial_bound − budget > 0`
and `budget + g ≤ initial_bound` (`add_sub_cancel_eqv`). -/

/-- `tailBudget < su2CasimirGap` (`72/145 < 3/4`), the genuine quantitative
check `budget < initial_bound` on the concrete canonical rationals. -/
theorem tailBudget_lt_initial : tailBudget < su2CasimirGap := by decide

/-- The surviving gap `g = su2CasimirGap − tailBudget` (`= 3/4 − 72/145`). -/
def survivingGap : Q' := su2CasimirGap - tailBudget

/-- `0 < survivingGap` — the genuine codynamic gap is positive (decide on the
concrete canonical rational). -/
theorem survivingGap_pos : (0 : Q') < survivingGap := by decide

/-- **THE codynamic gap (PROVED closure witness).**  The surviving gap
`g = 3/4 − budget > 0` with `budget + g ≤ 3/4`.  This is a genuine
`ClosureWitness` on `rgFlowBudget`: the gap that survives the entire (proved,
summable) RG tail-flow degradation budget. -/
def rgFlowClosure : ClosureWitness rgFlowBudget :=
  ⟨survivingGap, survivingGap_pos, by
    -- budget + (initial − budget) ≤ initial, by add_sub_cancel_eqv.
    show rgFlowBudget.budget + survivingGap ≤ rgFlowBudget.initial_bound
    show tailBudget + (su2CasimirGap - tailBudget) ≤ su2CasimirGap
    -- su2CasimirGap.eqv (tailBudget + (su2CasimirGap + -tailBudget))
    exact Q'.ge_of_eqv (Q'.add_sub_cancel_eqv su2CasimirGap tailBudget)⟩

/-- **The codynamic gap** as a bare `Q'`. -/
def codynamicGap : Q' := rgFlowClosure.1

/-- The codynamic gap is strictly positive. -/
theorem codynamicGap_pos : (0 : Q') < codynamicGap := rgFlowClosure.2.1

/-- **The codynamic gap as a TRANSPORTED FLOW INVARIANT.**  At every flow
truncation `N`, the accumulated degradation plus the surviving gap stays under
the initial bound:  `∑_{k<N} δ_k + g ≤ Δ_0`.  This is `ClosureWitness.terminal`
— the uniform survival of the gap across the whole flow, not just one scale. -/
theorem codynamicGap_terminal (N : Nat) :
    finSum rgFlowBudget.degradation N + codynamicGap ≤ rgFlowBudget.initial_bound :=
  rgFlowClosure.terminal N

/-! ## 4. The codynamic transport — the categorical payoff

`transportClosure` carries the SAME surviving gap from this object to an EASIER
flow (smaller budget, larger room), realizing "prove the worst case once,
transport to easier scales/groups" as flow-invariance of the gap.  We build a
genuine easier object: budget `0` (no degradation — the trivial limiting flow)
and room `1` (the full margin), then a real `BudgetHom` into `rgFlowBudget`. -/

/-- An **easier** RG tail flow: zero degradation (the limiting/no-loss flow),
budget `0`, full room `1`.  A genuine `BudgetObj` (its `budget_summable` is the
identically-zero partial sum `≤ 0`). -/
def rgFlowBudget' : BudgetObj where
  degradation := fun _ => 0
  initial_bound := 1
  budget := 0
  budget_summable := fun N => by
    -- finSum (fun _ => 0) N = 0 ≤ 0
    rw [YMGap.Constructive.RationalTail.finSum_zero_seq N]
    exact Q'.le_refl' 0

/-- **A genuine `BudgetHom rgFlowBudget' ⟶ rgFlowBudget`.**  `rgFlowBudget'` is
*easier* than `rgFlowBudget`: it degrades no more (`0 ≤ 72/145`) and has at least
as much room (`3/4 ≤ 1`).  Both are real `≤` facts on the concrete rationals
(`decide`), not faked. -/
def rgFlowBudget'_to_rgFlowBudget : BudgetHom rgFlowBudget' rgFlowBudget where
  budget_le := by decide
  init_ge := by decide

/-- **The codynamic gap transports to the easier flow.**  Via `transportClosure`
along the genuine `BudgetHom`, the SAME surviving gap `g` is a closure witness
for the easier flow `rgFlowBudget'` — the flow-invariance of the gap made
categorical (prove once on the harder flow, get it on the easier one for free). -/
def codynamicGap_transported : ClosureWitness rgFlowBudget' :=
  transportClosure rgFlowBudget'_to_rgFlowBudget rgFlowClosure

/-- The transported witness carries the SAME gap value. -/
theorem codynamicGap_transported_eq : codynamicGap_transported.1 = codynamicGap := rfl

/-! ## 5. The OPEN obligation, reframed in FLOW form

The codynamic gap above is positive for the PROVED **approximate** dominant-mode
tail flow.  The remaining obligation is no longer the pathological STATIC margin
— it is a WELL-BEHAVED FLOW quantity: that the approximate per-step defect
`renDefect` (bond-moving, dominant mode) bounds the EXACT physical RG per-scale
gap loss.  This is the Balaban RG-control question, named here and NOT inhabited. -/

/-- **The open flow identification (UNINHABITED).**

Carries the EXACT physical per-scale gap-loss sequence `exactLoss` as data, and
the field `dominates`: the approximate dominant-mode `renDefect` bounds it at
every scale,

    exactLoss k  ≤  renDefect afr pMult (k₀ + k).

NO inhabitant is constructed (this is the RG-control / Balaban question: that the
bond-moving dominant-mode surrogate dominates the exact non-abelian multi-link
per-scale loss along the genuine 4D AF trajectory).  Contrast the STATIC
obligation (`NormExcitedDrift`: the character margin = physical gap), which is
the quantity that crossed ZERO through the weak-coupling middle.  The FLOW
quantity `renDefect ∝ (1 − w)²` is quadratic, summable, and NEVER crosses zero
through the middle — so it is BETTER-POSITIONED, though still open. -/
structure CodynamicExactIdentification : Type where
  /-- The EXACT physical per-scale gap-loss sequence (nonnegative). -/
  exactLoss : Nat → Q'
  /-- Each exact loss is nonnegative (a genuine loss factor). -/
  exactLoss_nonneg : ∀ k, (0 : Q') ≤ exactLoss k
  /-- **THE OPEN CONTENT.**  The approximate dominant-mode `renDefect` dominates
  the exact per-scale loss at every scale.  This is the RG-control / Balaban
  domination — UNPROVED for 4D Yang–Mills. -/
  dominates : ∀ k, exactLoss k ≤ renDefect afr pMult (k0 + k)

/-- The exact-flow budget object built FROM an identification `E`: the exact
per-scale loss as degradation, with the SAME proved tail budget (since
`exactLoss ≤ renDefect`, its partial sums are bounded by the same `tailBudget`),
and the same `3/4` room. -/
def exactFlowBudget (E : CodynamicExactIdentification) : BudgetObj where
  degradation := E.exactLoss
  initial_bound := su2CasimirGap
  budget := tailBudget
  budget_summable := fun N => by
    -- finSum exactLoss N ≤ finSum renDefect-shift N ≤ tailBudget.
    refine Q'.le_trans' _ _ _ ?_ (tailDegradation_summable N)
    -- termwise domination lifts through finSum (monotone in the summand).
    exact YMGap.Constructive.CharacterTail.finSum_le_termwise
      E.exactLoss tailDegradation (fun k => E.dominates k) N

/-- **THE REDUCTION (PROVED, given the open identification).**  GIVEN a
`CodynamicExactIdentification` `E`, the EXACT physical codynamic gap survives:
the surviving gap `g = 3/4 − budget > 0` is a genuine `ClosureWitness` for the
exact-flow budget.  Only `E` is open; the survival is proved by transporting the
proved budget bound through `E`'s domination.  Hence: physical codynamic gap
positivity ⟸ the single FLOW obligation `E`. -/
def codynamic_gap_of_exact (E : CodynamicExactIdentification) :
    ClosureWitness (exactFlowBudget E) :=
  ⟨survivingGap, survivingGap_pos, by
    show (exactFlowBudget E).budget + survivingGap ≤ (exactFlowBudget E).initial_bound
    show tailBudget + (su2CasimirGap - tailBudget) ≤ su2CasimirGap
    exact Q'.ge_of_eqv (Q'.add_sub_cancel_eqv su2CasimirGap tailBudget)⟩

/-- The exact physical codynamic gap (given `E`) is strictly positive. -/
theorem codynamic_gap_of_exact_pos (E : CodynamicExactIdentification) :
    (0 : Q') < (codynamic_gap_of_exact E).1 :=
  (codynamic_gap_of_exact E).2.1

/-! ## 6. The honest ledger (English)

  1. The STATIC lens is WRONG.  The fixed-scale character margin
     `(1 − c₁)²/(1 + c₁²)` CROSSES ZERO at the weak-coupling middle
     (`w ≈ 0.794`).  No fixed-scale spectral quantity survives the trajectory;
     the zero-crossing is a static-endpoint ARTIFACT.

  2. The CODYNAMIC lens is right.  The gap is the surviving floor of the RG
     flow's accumulated degradation BUDGET — a `ClosureWitness` on a `BudgetObj`.
     Its driver is the per-step defect `renDefect ∝ (1 − w)²`: QUADRATIC,
     nonnegative, SUMMABLE, with NO zero-crossing through the middle.

  3. PROVED here: for the canonical dominant-mode tail flow, the codynamic gap is
     POSITIVE (`codynamicGap_pos`, `g = 3/4 − 72/145 > 0`) and survives EVERY
     flow truncation (`codynamicGap_terminal`).  It transports to easier flows
     categorically (`codynamicGap_transported`).

  4. The OPEN obligation is REFRAMED from the pathological static margin to a
     well-behaved FLOW quantity: `CodynamicExactIdentification`, that `renDefect`
     bounds the EXACT physical per-scale loss.  GIVEN it, the physical codynamic
     gap is positive (`codynamic_gap_of_exact`).

  5. SCOPE / what remains open (none hidden):
       * dominant mode → full mode (all `s`);
       * the finite head `k < k₀`;
       * the genuine 4D AF trajectory (canonical inhabitant is non-4D);
       * `CodynamicExactIdentification` itself (the RG-control / Balaban
         domination of the exact loss by the approximate `renDefect`).

The codynamic gap built here is positive for the PROVED approximate
dominant-mode tail flow.  It is NOT a 4D Yang–Mills mass gap.  Nothing is faked:
the degradation is the real `renDefect`, the budget is its proved summability
bound, the closure is genuinely proved, the transport is a real `BudgetHom`, and
`CodynamicExactIdentification` is left UNINHABITED with `codynamic_gap_of_exact`
a real reduction. -/

end YMGap.Continuum.CodynamicGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CodynamicGap.finSum_tailDegradation_eq
#print axioms YMGap.Continuum.CodynamicGap.tailDegradation_summable
#print axioms YMGap.Continuum.CodynamicGap.rgFlowBudget
#print axioms YMGap.Continuum.CodynamicGap.tailBudget_lt_initial
#print axioms YMGap.Continuum.CodynamicGap.survivingGap_pos
#print axioms YMGap.Continuum.CodynamicGap.rgFlowClosure
#print axioms YMGap.Continuum.CodynamicGap.codynamicGap_pos
#print axioms YMGap.Continuum.CodynamicGap.codynamicGap_terminal
#print axioms YMGap.Continuum.CodynamicGap.rgFlowBudget'_to_rgFlowBudget
#print axioms YMGap.Continuum.CodynamicGap.codynamicGap_transported
#print axioms YMGap.Continuum.CodynamicGap.codynamic_gap_of_exact
#print axioms YMGap.Continuum.CodynamicGap.codynamic_gap_of_exact_pos
