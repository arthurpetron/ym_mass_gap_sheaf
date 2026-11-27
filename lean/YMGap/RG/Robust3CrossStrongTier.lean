/-
# Robust3 crossover, strong-coupling tier (schedule T) and `scaleChain_of_twoStepFactor`

**Label: PROVED reductions and exact-rational certificates from explicit OPEN inputs.
NOT gap evidence, NOT chart closure.**  Additive; every existing module is untouched.
Spec: `strong_tier_spec.md` §1 (Nov 26, 2026), `extra_crossover.md` §10.

* (A) Schedule T: head nomes `1/64, 1/8, 7/20, 1/2, 606841/10⁶ (= 0.779²), 779/1000`, then instance
  B shifted by one (`r3NomeT j = r3NomeB (j+1)` for `j ≥ 5`).  The strong-coupling half of
  `DyadicRGStep` holds at every head step (tight at the last); the spec said the AF half fails at steps 3, 4
  — corrected: it fails only at step 4; steps 0–3 pass in full (`strongT_dyadic_head`,
  `strongT_not_dyadic`; `DyadicRGStep` has no consumer).
* (B) Budget `η = (2⁻²⁰, 1/100, 1/128, 1/12, 1/12)`, `k = 5`, AF offset `s = 1`:
  `E = 14508107/78643200`, floor `17411482987/983040000000 ≈ 0.0177119 > 0` (decide).
* (C) Interface over T; the crossover inputs at steps 2, 3, 4 are named OPEN props.  Steps 3
  (w ≈ 0.6068) and 4 (w = 0.779) are OPEN with no method; step 4 is past the matched-U(1)
  transition, so any proof of it would be non-abelian content.  Zero RG map below `k`
  discharges `hupper` on crossover steps.
* (D) Physical-units floor.  The head spacing table `ρ₀…ρ₄` is NOT fixed here (it is under the
  Monte-Carlo recheck and may be false): it is a parameter `rhoHead` with explicit hypotheses
  (`ρ_j ≥ 1` and the spacing on `aHK`); only the tail reuses `r3Rho`/`r3Omega` (shifted by one).
* (E) Floor with an afGap offset `s` separate from the schedule offset.
* (F) Step 2 at w = 1/2: the W558 certificate arithmetic at the lower nome (decide), and the
  bridge-with-decay as an OPEN input.
* (G) `scaleChain_of_twoStepFactor`: one direct two-step-factor hypothesis per step replaces
  `(Φ, D, hupper, hschur)`.  This is a bookkeeping reduction: the hypothesis is itself a direct
  gap bound at each fine nome, so it is not gap evidence.

U(1) note: steps 0–2 are U(1)-true at matched activity (not non-abelian evidence).

Mathlib-free; no sorry/admit/Classical/native_decide/omega/simpa/grind; axioms within
`propext`, `Quot.sound`.
-/

import YMGap.RG.Robust3CrossResplitB
import YMGap.RG.DyadicCrossoverSchedule
import YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime

namespace YMGap.RG.Robust3CrossStrongTier

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner completedInner_nonnegative unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedInner_zero_left completedInner_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate relativeRate_bounds)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf WilsonVacuumSqTwoStepFactor)
open YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery (vacuumSq_explicitRate_of_twoStepFactor)
open YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation
  (relativeFactor relativeFactor_nonnegative relativeFactor_le_one relativeFactor_error)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afGap_pos afGap_lt_one afA)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate timeRate_positive timeRate_lt_one)
open YMGap.RG.RelativeDissipationScaleChain
  (SchurDecomposition inv inv_nonneg scaleChain_contraction relativeRate_side_floor
   explicitRate_congr contraction_congr)
open YMGap.RG.CrossoverScaleChain (crossPart afPart crossover_floor_pos)
open YMGap.RG.DyadicCrossoverSchedule (DyadicRGStep)
open YMGap.RG.StrongCouplingNomeThreshold (uniformRate_of_guards scGuards_of_le_inv55 inv55)
open YMGap.RG.UndershootPhysicalUnits (floor_physical)
open YMGap.RG.Robust3UndershootPhysicalUnits (r3Rho r3Omega r3_weight r3_omega_ge_one)
open YMGap.RG.Robust3UndershootAfScheduleW558 (robust3UndershootScheduleB r3NomeB)
open YMGap.RG.Robust3MarginDischarge (margin_nonneg_of_floor)
open YMGap.RG.Robust3SchurRankOne (SchurBudget schurSlack schur_of_spectral)
open YMGap.RG.Robust3CrossUniformW558 (fineAtB twoStepFactor_congr)
open YMGap.RG.Robust3CrossResplitB (crossover_prefix_budget_k fineAtB_mono schurBudget_self_zero)
open YMGap.RG.Step2Conditional (SphereGasModel)
open YMGap.RG.Step2ConditionalW558 (lamB EB tB)

/-! ## (A) Schedule T -/

/-- Head nomes of the strong-coupling tier. -/
def strongTab : Nat → Q'
  | 0 => Q'.mkPos 1 64 (by decide)
  | 1 => Q'.mkPos 1 8 (by decide)
  | 2 => Q'.mkPos 7 20 (by decide)
  | 3 => Q'.mkPos 1 2 (by decide)
  | 4 => Q'.mkPos 606841 1000000 (by decide)
  | _ => Q'.mkPos 779 1000 (by decide)

/-- Head `j < 6` from `strongTab`; from `j = 6` on, instance B shifted by one. -/
def r3NomeT (j : Nat) : Q' := if j < 6 then strongTab j else r3NomeB (j + 1)

theorem r3NomeT_head : ∀ j, j < 6 → r3NomeT j = strongTab j := by
  intro j h; unfold r3NomeT; rw [if_pos h]

/-- From `j = 5` on, schedule T is instance B shifted by one (`j = 5`: `779/1000 = r3NomeB 6`). -/
theorem r3NomeT_shift (j : Nat) (h : 5 ≤ j) : r3NomeT j = r3NomeB (j + 1) := by
  by_cases h6 : j < 6
  · have e : j = 5 := Nat.le_antisymm (Nat.le_of_lt_succ h6) h
    rw [e]; rfl
  · unfold r3NomeT; rw [if_neg h6]

theorem strongTab_strict : ∀ j, j < 5 → strongTab j < strongTab (j+1) := by decide

theorem strongT_join : strongTab 5 ≤ r3NomeB 7 := by decide

private theorem headT_pos : ∀ j, j < 6 → (0 : Q') < r3NomeT j := by decide
private theorem headT_lt_one : ∀ j, j < 6 → r3NomeT j < (1 : Q') := by decide
private theorem headT_mono : ∀ j, j < 5 → r3NomeT j ≤ r3NomeT (j+1) := by decide

/-- **Schedule T is a `NomeSchedule` (PROVED; head by decide, tail from instance B).** -/
def robust3StrongScheduleT : NomeSchedule where
  nome := r3NomeT
  nome_pos := fun j => by
    by_cases h : j < 6
    · exact headT_pos j h
    · rw [r3NomeT_shift j (Nat.le_of_lt (Nat.not_lt.mp h))]
      exact robust3UndershootScheduleB.nome_pos (j + 1)
  nome_lt_one := fun j => by
    by_cases h : j < 6
    · exact headT_lt_one j h
    · rw [r3NomeT_shift j (Nat.le_of_lt (Nat.not_lt.mp h))]
      exact robust3UndershootScheduleB.nome_lt_one (j + 1)
  nome_mono := fun j => by
    by_cases h : j < 5
    · exact headT_mono j h
    · have h5 : 5 ≤ j := Nat.not_lt.mp h
      rw [r3NomeT_shift j h5, r3NomeT_shift (j+1) (Nat.le_succ_of_le h5)]
      exact robust3UndershootScheduleB.nome_mono (j + 1)
  limitModulus := fun eps => robust3UndershootScheduleB.limitModulus eps
  nome_limit := fun eps he j hj => by
    have h11 : 11 ≤ j := Nat.le_trans (Nat.le_add_right 11 _) hj
    rw [r3NomeT_shift j (Nat.le_trans (by decide : 5 ≤ 11) h11)]
    exact robust3UndershootScheduleB.nome_limit eps he (j + 1) (Nat.le_succ_of_le hj)

/-- Strong-coupling half of `DyadicRGStep` at every head step (decide). -/
theorem strongT_sc : ∀ n, n < 5 → strongTab (n+1) * strongTab (n+1) ≤ strongTab n := by decide

/-- The last head step is tight: `(779/1000)² = 606841/10⁶`. -/
theorem strongT_sc_tight : Q'.eqv (strongTab 5 * strongTab 5) (strongTab 4) := by decide

/-- Full `DyadicRGStep` holds at head steps 0–3 (decide). -/
theorem strongT_dyadic_head : ∀ n, n < 4 → DyadicRGStep (strongTab n) (strongTab (n+1)) := by
  decide

/-- Disclosure: the AF half of `DyadicRGStep` fails at step 4 (`0.6068 → 0.779`); the convention
is not consumed anywhere.  (The spec's claim that it also fails at step 3, `1/2 → 0.6068`, is
false: that step passes, see `strongT_dyadic_head`.) -/
theorem strongT_not_dyadic : ¬ DyadicRGStep (strongTab 4) (strongTab 5) := by
  decide

/-! ## (B) Budget (decide) -/

/-- `η = (2⁻²⁰, 1/100, 1/128, 1/12, 1/12, …)` (only `n < 5` is used). -/
def etaT : Nat → Q'
  | 0 => Q'.mkPos 1 1048576 (by decide)
  | 1 => Q'.mkPos 1 100 (by decide)
  | 2 => Q'.mkPos 1 128 (by decide)
  | _ => Q'.mkPos 1 12 (by decide)

/-- `E = 2⁻²⁰ + 1/100 + 1/128 + 1/12 + 1/12 = 14508107/78643200` (exact). -/
def eT : Q' := Q'.mkPos 14508107 78643200 (by decide)

private theorem tailT : ∀ m, finSum (crossPart 5 etaT) (m+5) ≤ eT
  | 0 => by decide
  | m+1 => by
    have hz : crossPart 5 etaT (m+5) = 0 := by
      unfold crossPart
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left 5 m))]
    show finSum (crossPart 5 etaT) (m+5) + crossPart 5 etaT (m+5) ≤ _
    rw [hz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) (tailT m)

private theorem headT : ∀ n, n < 5 → finSum (crossPart 5 etaT) n ≤ eT := by decide

/-- `eT` is exactly the crossover sum (decide). -/
theorem eT_exact : Q'.eqv (finSum (crossPart 5 etaT) 5) eT := by decide

theorem etaT_budget (n : Nat) : finSum (crossPart 5 etaT) n ≤ eT := by
  by_cases h : n < 5
  · exact headT n h
  · have e : n = (n - 5) + 5 := (Nat.sub_add_cancel (Nat.not_lt.mp h)).symm
    rw [e]; exact tailT (n - 5)

/-- `B = (1/10)·afA²/9 = 942841/22500000` (decide). -/
theorem afTail_T_value :
    Q'.eqv (Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (1 + 5 + 2))
      (Q'.mkPos 942841 22500000 (by decide)) := by decide

theorem budget_T_ok :
    eT + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (1 + 5 + 2) < timeRate := by decide

/-- Floor `(3/4)(1/4 − E − afA²/90) = 17411482987/983040000000 ≈ 0.0177119` (decide). -/
theorem floor_T_value :
    Q'.eqv (((1 : Q') - timeRate) *
        (timeRate - (eT + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (1 + 5 + 2))))
      (Q'.mkPos 17411482987 983040000000 (by decide)) := by decide

theorem floor_T_pos :
    (0 : Q') < ((1 : Q') - timeRate) *
      (timeRate - (eT + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (1 + 5 + 2))) :=
  crossover_floor_pos timeRate _ timeRate_lt_one budget_T_ok

/-! ## (C) Interface over schedule T -/

abbrev VCT (W : Nat → Nat) (j : Nat) :=
  VacuumComplement (robust3StrongScheduleT.nome_pos j) (robust3StrongScheduleT.nome_lt_one j)
    (width := W j)

abbrev PhiFamT := ∀ (W : Nat → Nat) (n : Nat), VCT W (0+n+1) → VCT W (0+n)

def fineAtT (W : Nat → Nat) (n : Nat) (f : Q') : Prop :=
  WilsonVacuumSqTwoStepFactor (robust3StrongScheduleT.nome_pos (0+n+1))
    (robust3StrongScheduleT.nome_lt_one (0+n+1)) (W (0+n+1)) f

def coarseAtT (W : Nat → Nat) (n : Nat) (Phi : VCT W (0+n+1) → VCT W (0+n)) (c : Q') : Prop :=
  ∀ y, RCle (RCscale c (completedInner (robust3StrongScheduleT.nome_pos (0+n+1))
      (robust3StrongScheduleT.nome_lt_one (0+n+1)) y.val y.val))
    (completedInner (robust3StrongScheduleT.nome_pos (0+n))
      (robust3StrongScheduleT.nome_lt_one (0+n))
      (completedTime (robust3StrongScheduleT.nome_pos (0+n))
        (robust3StrongScheduleT.nome_lt_one (0+n)) 1 (Phi y).val)
      (completedTime (robust3StrongScheduleT.nome_pos (0+n))
        (robust3StrongScheduleT.nome_lt_one (0+n)) 1 (Phi y).val))

def hupper_unifT (Phi : PhiFamT) : Prop :=
  ∀ W n (y : VCT W (0+n+1)), RCle
    (completedInner (robust3StrongScheduleT.nome_pos (0+n))
      (robust3StrongScheduleT.nome_lt_one (0+n)) (Phi W n y).val (Phi W n y).val)
    (completedInner (robust3StrongScheduleT.nome_pos (0+n+1))
      (robust3StrongScheduleT.nome_lt_one (0+n+1)) y.val y.val)

/-- Steps 0, 1 have the same nomes as instance B (PROVED). -/
theorem fineAtT_iff_B_low (W : Nat → Nat) (n : Nat) (h : n < 2) (f : Q') :
    fineAtT W n f ↔ fineAtB W n f := by
  match n, h with
  | 0, _ => exact twoStepFactor_congr rfl _ _ _ _ _ _
  | 1, _ => exact twoStepFactor_congr rfl _ _ _ _ _ _

/-- Step 4 (nome `779/1000`) is instance-B step 5 with widths reindexed (PROVED). -/
theorem fineAtT_four_iff_B (W : Nat → Nat) (f : Q') :
    fineAtT W 4 f ↔ fineAtB (fun j => W (j - 1)) 5 f :=
  twoStepFactor_congr (r3NomeT_shift 5 (Nat.le_refl 5)) _ _ _ _ _ _

/-! ### Open crossover inputs (named) -/

/-- Step 2 at w = 1/2: target of the CERT-REL route; OPEN in Lean. -/
def hfine_T2_half_OPEN : Prop := ∀ W, fineAtT W 2 (Q'.mkPos 1 128 (by decide))

/-- Step 3 at w = 606841/10⁶ (u ≈ 0.2235): OPEN, no method. -/
def hfine_T3_6068_OPEN : Prop := ∀ W, fineAtT W 3 (Q'.mkPos 1 12 (by decide))

/-- Step 4 at w = 779/1000 (u ≈ 0.4727): OPEN, no method; past the matched-U(1) transition, so
any proof would be non-abelian content. -/
def hfine_T4_779_OPEN : Prop := ∀ W, fineAtT W 4 (Q'.mkPos 1 12 (by decide))

/-- The old instance-B step-5 hypothesis (`1/64`) implies the new step 4 (`1/12`) (PROVED). -/
theorem hfine_T4_of_old (h : ∀ W, fineAtB W 5 (Q'.mkPos 1 64 (by decide))) :
    hfine_T4_779_OPEN := fun W =>
  (fineAtT_four_iff_B W _).mpr
    (fineAtB_mono _ 5 (by decide : Q'.mkPos 1 64 (by decide) ≤ Q'.mkPos 1 12 (by decide))
      (h (fun j => W (j - 1))))

private theorem RCscale_zeroT (a : RC) : RCscale (0 : Q') a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

/-- Coarse attainment at constant `0` holds for every width, step and map (PROVED). -/
theorem coarseAtT_zero (W : Nat → Nat) (n : Nat) (Phi : VCT W (0 + n + 1) → VCT W (0 + n)) :
    coarseAtT W n Phi 0 := by
  intro y
  let hw0 := robust3StrongScheduleT.nome_pos (0 + n)
  let hw1 := robust3StrongScheduleT.nome_lt_one (0 + n)
  let hw0F := robust3StrongScheduleT.nome_pos (0 + n + 1)
  let hw1F := robust3StrongScheduleT.nome_lt_one (0 + n + 1)
  change RCle
    (RCscale (0 : Q') (completedInner hw0F hw1F y.val y.val))
    (completedInner hw0 hw1
      (completedTime hw0 hw1 1 (Phi y).val)
      (completedTime hw0 hw1 1 (Phi y).val))
  rw [RCscale_zeroT]
  exact completedInner_nonnegative hw0 hw1 (completedTime hw0 hw1 1 (Phi y).val)

/-- **`hcross_unifT` (OPEN).** Crossover hypothesis over T with `k = 5` and `etaT`. -/
def hcross_unifT (Phi : PhiFamT) (f c : Nat → Q') : Prop :=
  (∀ n, n < 5 → SchurBudget (f n) (c n) (etaT n)) ∧
    ∀ W n, n < 5 → fineAtT W n (f n) ∧ coarseAtT W n (Phi W n) (c n)

/-- **Coarse-constant-0 reduction over T (PROVED).** -/
theorem hcross_unifT_of_fine (Phi : PhiFamT)
    (h0 : ∀ W, fineAtT W 0 (etaT 0)) (h1 : ∀ W, fineAtT W 1 (etaT 1))
    (h2 : hfine_T2_half_OPEN) (h3 : hfine_T3_6068_OPEN) (h4 : hfine_T4_779_OPEN) :
    hcross_unifT Phi etaT (fun _ => 0) := by
  refine ⟨fun n _ => schurBudget_self_zero (etaT n), fun W n hn => ⟨?_, coarseAtT_zero W n (Phi W n)⟩⟩
  match n, hn with
  | 0, _ => exact h0 W
  | 1, _ => exact h1 W
  | 2, _ => exact h2 W
  | 3, _ => exact h3 W
  | 4, _ => exact h4 W
  | m+5, h => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 5 m))

/-- **`hafδ_unifT` (OPEN).** AF steps use `afGap (1+n)`: the same allowance at the same nome as
instance B. -/
def hafδ_unifT (Phi : PhiFamT) (f c : Nat → Q') : Prop :=
  (∀ n, 5 ≤ n → SchurBudget (f n) (c n) (Q'.mkPos 1 10 (by decide) * (afGap (1+n) * afGap (1+n)))) ∧
    ∀ W n, 5 ≤ n → fineAtT W n (f n) ∧ coarseAtT W n (Phi W n) (c n)

/-! ### Zero RG map below `k` (discharges `hupper` on crossover steps) -/

/-- The zero vector of the vacuum complement (`⟨U, 0⟩ = 0`). -/
def vcZero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    VacuumComplement hw0 hw1 (width := width) :=
  ⟨completedZero hw0 hw1 width, completedInner_zero_right hw0 hw1 (unitState hw0 hw1 width)⟩

/-- The RG maps replaced by `0` on steps `n < k`. -/
def phiZeroBelow (k : Nat) (Phi : PhiFamT) : PhiFamT :=
  fun W n => if n < k then fun _ => vcZero (robust3StrongScheduleT.nome_pos (0+n))
    (robust3StrongScheduleT.nome_lt_one (0+n)) (W (0+n)) else Phi W n

/-- **`hupper` for the zeroed maps (PROVED):** trivially below `k`, from `h` from `k` on. -/
theorem hupper_phiZeroBelow (k : Nat) (Phi : PhiFamT)
    (h : ∀ W n, k ≤ n → ∀ y : VCT W (0+n+1), RCle
      (completedInner (robust3StrongScheduleT.nome_pos (0+n)) (robust3StrongScheduleT.nome_lt_one (0+n))
        (Phi W n y).val (Phi W n y).val)
      (completedInner (robust3StrongScheduleT.nome_pos (0+n+1)) (robust3StrongScheduleT.nome_lt_one (0+n+1))
        y.val y.val)) :
    hupper_unifT (phiZeroBelow k Phi) := by
  intro W n y
  by_cases hn : n < k
  · have e : phiZeroBelow k Phi W n = fun _ => vcZero (robust3StrongScheduleT.nome_pos (0+n))
        (robust3StrongScheduleT.nome_lt_one (0+n)) (W (0+n)) := by
      unfold phiZeroBelow; rw [if_pos hn]
    rw [e]
    show RCle (completedInner _ _ (completedZero _ _ (W (0+n))) (completedZero _ _ (W (0+n)))) _
    rw [completedInner_zero_left]
    exact completedInner_nonnegative _ _ y.val
  · have e : phiZeroBelow k Phi W n = Phi W n := by
      unfold phiZeroBelow; rw [if_neg hn]
    rw [e]
    exact h W n (Nat.not_lt.mp hn) y

/-! ## (E) AF tail with an afGap offset separate from the schedule offset -/

/-- **`scaleChain_crossover_floor_off` (PROVED from explicit OPEN inputs).** As
`scaleChain_crossover_floor`, with AF steps budgeted by `afGap (s+n)` and the tail from `k`. -/
theorem scaleChain_crossover_floor_off (ns : NomeSchedule) (width : Nat → Nat) (j0 s k : Nat)
    (seed C E : Q') (delta eta : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hE0 : (0 : Q') ≤ E)
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hcross_OPEN : ∀ n, n < k → delta n ≤ eta n)
    (hafδ_OPEN : ∀ n, k ≤ n → delta n ≤ C * (afGap (s+n) * afGap (s+n)))
    (hE : ∀ n, finSum (crossPart k eta) n ≤ E)
    (hbudget : E + C * (afA * afA) * inv (s + k + 2) < seed)
    (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width := width (j0+n+1)) →
      VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
    (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width := width (j0+n+1)) → RC)
    (hupper_OPEN : ∀ n y, RCle
      (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
      (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
    (hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
      (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n))
      (delta n) (Phi n) (D n))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed)
    (n : Nat) :
    WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
        (relativeRate seed delta n) ∧
      ((1 : Q') - seed) * (seed - (E + C * (afA * afA) * inv (s + k + 2))) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate seed delta) n := by
  have hB : (0 : Q') ≤ C * (afA * afA) * inv (s + k + 2) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (by decide) (by decide)))
      (inv_nonneg _)
  exact ⟨scaleChain_contraction ns width j0 seed delta hs0 (Q'.le_of_lt hs1) hd0 hd1 Phi D
      hupper_OPEN hschur_OPEN hseed n,
    relativeRate_side_floor seed _ delta hs0 hs1 (Q'.le_trans' _ _ _ hE0
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv E)) (Q'.add_le_add_left E _ _ hB)))
      hbudget hd0 hd1
      (crossover_prefix_budget_k C E hC s k delta eta hcross_OPEN hafδ_OPEN hE) n⟩

/-! ## (D) Spacing table for T (head as a parameter) and the physical-units floor -/

/-- `ρ_T`: head `ρ₀…ρ₄` is a PARAMETER (pending the MC recheck; not fixed here); tail is
instance B's `r3Rho` shifted by one. -/
def rhoTOf (rhoHead : Nat → Q') (j : Nat) : Q' := if j < 5 then rhoHead j else r3Rho (j + 1)

/-- Telescoping weights for `rhoTOf`: backward products on the head, `r3Omega` shifted on the tail. -/
def omegaTOf (rhoHead : Nat → Q') : Nat → Q'
  | 0 => rhoHead 0 * (rhoHead 1 * (rhoHead 2 * (rhoHead 3 * (rhoHead 4 * r3Omega 6))))
  | 1 => rhoHead 1 * (rhoHead 2 * (rhoHead 3 * (rhoHead 4 * r3Omega 6)))
  | 2 => rhoHead 2 * (rhoHead 3 * (rhoHead 4 * r3Omega 6))
  | 3 => rhoHead 3 * (rhoHead 4 * r3Omega 6)
  | 4 => rhoHead 4 * r3Omega 6
  | j+5 => r3Omega (j + 6)

/-- Weight inequality for any head (PROVED; equality on the head, `r3_weight` on the tail). -/
theorem rhoTOf_weight (rhoHead : Nat → Q') :
    ∀ j, rhoTOf rhoHead j * omegaTOf rhoHead (j+1) ≤ omegaTOf rhoHead j
  | 0 => Q'.le_refl' _
  | 1 => Q'.le_refl' _
  | 2 => Q'.le_refl' _
  | 3 => Q'.le_refl' _
  | 4 => Q'.le_refl' _
  | j+5 => by
    have hn : ¬ j + 5 < 5 := Nat.not_lt.mpr (Nat.le_add_left 5 j)
    unfold rhoTOf; rw [if_neg hn]
    exact r3_weight (j + 6)

private theorem one_le_mul' {a b : Q'} (ha : (1 : Q') ≤ a) (hb : (1 : Q') ≤ b) : (1 : Q') ≤ a * b :=
  Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 1 * 1)
    (Q'.mul_le_mul_of_nonneg ha hb (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) ha) (by decide))

/-- `ω ≥ 1` given `ρ_j ≥ 1` on the head (PROVED). -/
theorem omegaTOf_ge_one (rhoHead : Nat → Q') (h1 : ∀ j, j < 5 → (1 : Q') ≤ rhoHead j) :
    ∀ j, (1 : Q') ≤ omegaTOf rhoHead j
  | 0 => one_le_mul' (h1 0 (by decide)) (one_le_mul' (h1 1 (by decide)) (one_le_mul'
      (h1 2 (by decide)) (one_le_mul' (h1 3 (by decide)) (one_le_mul' (h1 4 (by decide))
        (r3_omega_ge_one 6)))))
  | 1 => one_le_mul' (h1 1 (by decide)) (one_le_mul' (h1 2 (by decide)) (one_le_mul'
      (h1 3 (by decide)) (one_le_mul' (h1 4 (by decide)) (r3_omega_ge_one 6))))
  | 2 => one_le_mul' (h1 2 (by decide)) (one_le_mul' (h1 3 (by decide)) (one_le_mul'
      (h1 4 (by decide)) (r3_omega_ge_one 6)))
  | 3 => one_le_mul' (h1 3 (by decide)) (one_le_mul' (h1 4 (by decide)) (r3_omega_ge_one 6))
  | 4 => one_le_mul' (h1 4 (by decide)) (r3_omega_ge_one 6)
  | j+5 => r3_omega_ge_one (j + 6)

/-- Positivity of `aHK` on the T nomes. -/
def hposHKT (aHK : Q' → Q') : Prop := ∀ j, (0 : Q') < aHK (r3NomeT j)

/-- Spacing on `aHK` at the T nomes for `lo ≤ j ≤ hi`, against a spacing table `rho`. -/
def hspacingHK_winT (aHK : Q' → Q') (rho : Nat → Q') (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → Q'.ofNat 2 * aHK (r3NomeT (j+1)) ≤ rho j * aHK (r3NomeT j)

/-- Spacing on `aHK` at the T nomes off the window; OPEN. -/
def hspacingHK_offT (aHK : Q' → Q') (rho : Nat → Q') (lo hi : Nat) : Prop :=
  ∀ j, (j < lo ∨ hi < j) → Q'.ofNat 2 * aHK (r3NomeT (j+1)) ≤ rho j * aHK (r3NomeT j)

private theorem hspacingT_of_HK (aHK : Q' → Q') (rho : Nat → Q') (lo hi : Nat)
    (hw : hspacingHK_winT aHK rho lo hi) (ho : hspacingHK_offT aHK rho lo hi) :
    ∀ i, Q'.ofNat 2 * (fun j => aHK (r3NomeT j)) (i+1) ≤ rho i * (fun j => aHK (r3NomeT j)) i := by
  intro i
  by_cases h1 : i < lo
  · exact ho i (Or.inl h1)
  · by_cases h2 : hi < i
    · exact ho i (Or.inr h2)
    · exact hw i (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)

/-- Per-step cap: `η_n` for `n < 5`, else `afGap(1+n)²/10`. -/
def capDeltaT (n : Nat) : Q' :=
  if n < 5 then etaT n else Q'.mkPos 1 10 (by decide) * (afGap (1+n) * afGap (1+n))

private theorem etaT_nonneg : ∀ n, (0 : Q') ≤ etaT n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | _+3 => by show (0 : Q') ≤ Q'.mkPos 1 12 (by decide); decide

private theorem etaT_le_one : ∀ n, etaT n ≤ (1 : Q')
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | _+3 => by show Q'.mkPos 1 12 (by decide) ≤ (1 : Q'); decide

theorem capDeltaT_nonneg (n : Nat) : (0 : Q') ≤ capDeltaT n := by
  unfold capDeltaT
  by_cases h : n < 5
  · rw [if_pos h]; exact etaT_nonneg n
  · rw [if_neg h]
    have hg := Q'.le_of_lt (afGap_pos (1+n))
    exact Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hg hg)

theorem capDeltaT_le_one (n : Nat) : capDeltaT n ≤ (1 : Q') := by
  unfold capDeltaT
  by_cases h : n < 5
  · rw [if_pos h]; exact etaT_le_one n
  · rw [if_neg h]
    have hg0 := Q'.le_of_lt (afGap_pos (1+n))
    have hg1 := Q'.le_of_lt (afGap_lt_one (1+n))
    have hsq : afGap (1+n) * afGap (1+n) ≤ (1 : Q') * 1 :=
      Q'.mul_le_mul_of_nonneg hg1 hg1 (by decide) hg0
    have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 10 (by decide)) hsq (by decide)
    exact Q'.le_trans' _ _ _ h2 (by decide)

/-- The seed on schedule T (`w_0 = 1/64 ≤ 1/55`, PROVED as `r3_seed`). -/
theorem r3_seedT (width : Nat) :
    WilsonVacuumSqContraction (robust3StrongScheduleT.nome_pos 0)
      (robust3StrongScheduleT.nome_lt_one 0) width timeRate :=
  uniformRate_of_guards _ _
    (scGuards_of_le_inv55 (Q'.le_of_lt (robust3StrongScheduleT.nome_pos 0))
      (by decide : robust3StrongScheduleT.nome 0 ≤ inv55))
    width

private theorem step_dataT (Phi : PhiFamT) (f c : Nat → Q') (hX : hcross_unifT Phi f c)
    (hA : hafδ_unifT Phi f c) (W : Nat → Nat) (n : Nat) :
    fineAtT W n (f n) ∧ coarseAtT W n (Phi W n) (c n) ∧ SchurBudget (f n) (c n) (capDeltaT n) := by
  by_cases h : n < 5
  · refine ⟨(hX.2 W n h).1, (hX.2 W n h).2, ?_⟩
    unfold capDeltaT; rw [if_pos h]; exact hX.1 n h
  · have h5 : 5 ≤ n := Nat.le_of_not_lt h
    refine ⟨(hA.2 W n h5).1, (hA.2 W n h5).2, ?_⟩
    unfold capDeltaT; rw [if_neg h]; exact hA.1 n h5

private theorem hschurT_of_spectral (Phi : PhiFamT) (f c : Nat → Q') (hX : hcross_unifT Phi f c)
    (hA : hafδ_unifT Phi f c) (W : Nat → Nat) (n : Nat) :
    SchurDecomposition (robust3StrongScheduleT.nome_pos (0+n+1))
      (robust3StrongScheduleT.nome_lt_one (0+n+1))
      (robust3StrongScheduleT.nome_pos (0+n)) (robust3StrongScheduleT.nome_lt_one (0+n))
      (W (0+n+1)) (W (0+n)) (capDeltaT n) (Phi W n)
      (schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDeltaT n) (Phi W n)) :=
  have hd := step_dataT Phi f c hX hA W n
  schur_of_spectral _ _ _ _ _ _ (capDeltaT n) (f n) (c n) (Phi W n) (capDeltaT_le_one n)
    hd.1 hd.2.1 hd.2.2

/-- **Width-uniform floor on schedule T (PROVED reduction from explicit OPEN inputs).**
OPEN: `hupper`, `hX` (`hcross_unifT`: steps 2–4 are OPEN), `hA` (`hafδ_unifT`), and the spacing
inputs.  The head spacing table `rhoHead` is a parameter with `hrhoHead_ge_one`; the spacing of
`aHK` against `rhoTOf rhoHead` enters only as `hwin_MC` / `hoff_OPEN` (not rechecked for T).
`P_T = omegaTOf rhoHead 0`.  Floor `17411482987/983040000000 ≈ 0.0177` (`floor_T_value`).
Not chart closure; not gap evidence. -/
theorem robust3T_floor_width_uniform (Phi : PhiFamT) (f c : Nat → Q')
    (hupper : hupper_unifT Phi) (hX : hcross_unifT Phi f c) (hA : hafδ_unifT Phi f c)
    (rhoHead : Nat → Q') (hrhoHead_ge_one : ∀ j, j < 5 → (1 : Q') ≤ rhoHead j)
    (aHK : Q' → Q') (lo hi : Nat) (hpos : hposHKT aHK)
    (hwin_MC : hspacingHK_winT aHK (rhoTOf rhoHead) lo hi)
    (hoff_OPEN : hspacingHK_offT aHK (rhoTOf rhoHead) lo hi) :
    ∀ (W : Nat → Nat) (n : Nat),
      WilsonVacuumSqContraction (robust3StrongScheduleT.nome_pos (0+n))
          (robust3StrongScheduleT.nome_lt_one (0+n)) (W (0+n))
          (relativeRate timeRate capDeltaT n) ∧
      ((1 : Q') - timeRate) *
          (timeRate - (eT + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (1 + 5 + 2)))
          * aHK (r3NomeT n) ≤
        (omegaTOf rhoHead 0 * aHK (r3NomeT 0)) *
          latticeMarginOf (relativeRate timeRate capDeltaT) n := by
  intro W n
  have hc := scaleChain_crossover_floor_off robust3StrongScheduleT W 0 1 5 timeRate
    (Q'.mkPos 1 10 (by decide)) eT capDeltaT etaT (Q'.le_of_lt timeRate_positive)
    timeRate_lt_one (by decide) (by decide) capDeltaT_nonneg capDeltaT_le_one
    (fun k hk => by unfold capDeltaT; rw [if_pos hk]; exact Q'.le_refl' _)
    (fun k hk => by unfold capDeltaT; rw [if_neg (Nat.not_lt.mpr hk)]; exact Q'.le_refl' _)
    etaT_budget budget_T_ok (Phi W)
    (fun n => schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDeltaT n) (Phi W n))
    (hupper W) (hschurT_of_spectral Phi f c hX hA W) (r3_seedT (W 0)) n
  refine ⟨hc.1, ?_⟩
  have hM := margin_nonneg_of_floor _ _ n floor_T_pos hc.2
  exact floor_physical (fun j => aHK (r3NomeT j)) (rhoTOf rhoHead) (omegaTOf rhoHead)
    (latticeMarginOf (relativeRate timeRate capDeltaT)) _ (fun i => Q'.le_of_lt (hpos i))
    (omegaTOf_ge_one rhoHead hrhoHead_ge_one) (hspacingT_of_HK aHK _ lo hi hwin_MC hoff_OPEN)
    (rhoTOf_weight rhoHead) n hM hc.2

/-! ## (F) Step 2 at w = 1/2: the W558 certificate at a lower nome (decide-level) -/

def wHalf : Q' := Q'.mkPos 1 2 (by decide)

/-- `e^κ` witness, `κ = m/4`: `1.385 ≥ e^{1.213/4} ≈ 1.3543` (the bound itself is not formalised). -/
def kapExpT : Q' := Q'.mkPos 1385 1000 (by decide)

/-- Boosted activity at w = 1/2 fits the W558 row: `0.187302 ≤ tB = 0.187969` (decide). -/
theorem certT2_act : wHalf * wHalf * wHalf * kapExpT * (lamB * EB) ≤ tB := by decide

/-- `1.385¹⁶ ≥ 128` (decide; ≈ 183). -/
theorem certT2_rate : (128 : Q') ≤ kapExpT ^ 16 := by decide

/-- `KPToFineAt_BRIDGE_decay_OPEN` [BRIDGE — OPEN; not in spec; no proof cited].  All-spin KP
convergence with decay weight `kapExpT` (`kpAllSpinDecay`, an extra uninterpreted relation: it is
not a field of `SphereGasModel`, which is left untouched) on the step-2 width ⇒ `fineAtT W 2 (1/128)`.
Small widths `W < 8` stay a separate OPEN input. -/
def KPToFineAt_BRIDGE_decay_OPEN (G : SphereGasModel)
    (kpAllSpinDecay : Nat → Q' → Q' → Q' → Prop) : Prop :=
  ∀ W : Nat → Nat, 8 ≤ W (0 + 2 + 1) → ∀ a P : Q', (6 : Q') * P ≤ a →
    G.kpAllSpin (W (0 + 2 + 1)) a P → kpAllSpinDecay (W (0 + 2 + 1)) a P kapExpT →
      fineAtT W 2 (Q'.mkPos 1 128 (by decide))

/-! ## (G) `scaleChain_of_twoStepFactor` -/

/-- The two-step factor is monotone in a nonnegative scalar (PROVED). -/
theorem twoStepFactor_mono {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)
    {f f' : Q'} (h : f ≤ f') :
    WilsonVacuumSqTwoStepFactor hw0 hw1 width f → WilsonVacuumSqTwoStepFactor hw0 hw1 width f' := by
  intro hf y
  exact RCle_trans (hf y) (RCscale_mono_scalar h (completedInner_nonnegative _ _ y.val))

/-- **`scaleChain_of_twoStepFactor` (PROVED reduction; NOT gap evidence).**  One direct
two-step-factor hypothesis per step, at the factor `δ_n + (1−δ_n)·r_n²` that the relative recursion
produces, replaces `(Φ, D, hupper, hschur)`.  The induction hypothesis is not used: the rate is
pure arithmetic, and `htwo_OPEN` is itself a direct gap bound at each fine nome. -/
theorem scaleChain_of_twoStepFactor (ns : NomeSchedule) (width : Nat → Nat) (j0 : Nat)
    (seed : Q') (delta : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed ≤ (1 : Q'))
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (htwo_OPEN : ∀ n, WilsonVacuumSqTwoStepFactor (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width (j0+n+1)) (relativeFactor (delta n) (relativeRate seed delta n)))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed) :
    ∀ n, WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
      (relativeRate seed delta n)
  | 0 => hseed
  | n+1 => by
    have hr := relativeRate_bounds seed delta hs0 hs1 hd0 hd1 n
    exact contraction_congr _ _ _ (explicitRate_congr (relativeFactor_error _ _))
      (vacuumSq_explicitRate_of_twoStepFactor _
        (relativeFactor_nonnegative _ _ (hd0 n) (hd1 n))
        (relativeFactor_le_one _ _ (hd1 n) hr.1 hr.2) (htwo_OPEN n))

/-- Convenience form: any factor `f n ≤ relativeFactor …` suffices (PROVED). -/
theorem scaleChain_of_twoStepFactor_le (ns : NomeSchedule) (width : Nat → Nat) (j0 : Nat)
    (seed : Q') (delta f : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed ≤ (1 : Q'))
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hf : ∀ n, f n ≤ relativeFactor (delta n) (relativeRate seed delta n))
    (htwo_OPEN : ∀ n, WilsonVacuumSqTwoStepFactor (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width (j0+n+1)) (f n))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed) :
    ∀ n, WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
      (relativeRate seed delta n) :=
  scaleChain_of_twoStepFactor ns width j0 seed delta hs0 hs1 hd0 hd1
    (fun n => twoStepFactor_mono _ _ _ (hf n) (htwo_OPEN n)) hseed

/-- **Floor companion (PROVED reduction):** the floor of `scaleChain_crossover_floor_off`, from
`htwo_OPEN` instead of `(Φ, D, hupper, hschur)`. -/
theorem scaleChain_twoStep_floor_off (ns : NomeSchedule) (width : Nat → Nat) (j0 s k : Nat)
    (seed C E : Q') (delta eta : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hE0 : (0 : Q') ≤ E)
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hcross_OPEN : ∀ n, n < k → delta n ≤ eta n)
    (hafδ_OPEN : ∀ n, k ≤ n → delta n ≤ C * (afGap (s+n) * afGap (s+n)))
    (hE : ∀ n, finSum (crossPart k eta) n ≤ E)
    (hbudget : E + C * (afA * afA) * inv (s + k + 2) < seed)
    (htwo_OPEN : ∀ n, WilsonVacuumSqTwoStepFactor (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width (j0+n+1)) (relativeFactor (delta n) (relativeRate seed delta n)))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed)
    (n : Nat) :
    WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
        (relativeRate seed delta n) ∧
      ((1 : Q') - seed) * (seed - (E + C * (afA * afA) * inv (s + k + 2))) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate seed delta) n := by
  have hB : (0 : Q') ≤ C * (afA * afA) * inv (s + k + 2) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (by decide) (by decide)))
      (inv_nonneg _)
  exact ⟨scaleChain_of_twoStepFactor ns width j0 seed delta hs0 (Q'.le_of_lt hs1) hd0 hd1
      htwo_OPEN hseed n,
    relativeRate_side_floor seed _ delta hs0 hs1 (Q'.le_trans' _ _ _ hE0
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv E)) (Q'.add_le_add_left E _ _ hB)))
      hbudget hd0 hd1
      (crossover_prefix_budget_k C E hC s k delta eta hcross_OPEN hafδ_OPEN hE) n⟩

/-- `η ≤ η + (1−η)·r²` for `η ≤ 1` (PROVED). -/
private theorem le_relativeFactor (e r : Q') (he1 : e ≤ (1 : Q')) : e ≤ relativeFactor e r :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv e))
    (Q'.add_le_add_left e _ _ (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le he1)
      (SumOfSquares.q_mul_self_nonneg r)))

/-- **Crossover use (PROVED):** with `c = 0`, `fineAtT W n (etaT n)` gives the two-step factor at
`relativeFactor (etaT n) r` for any rate `r`, in particular `relativeRate timeRate capDeltaT n`. -/
theorem htwo_of_fine_crossover (W : Nat → Nat) (n : Nat) (h : fineAtT W n (etaT n)) :
    WilsonVacuumSqTwoStepFactor (robust3StrongScheduleT.nome_pos (0+n+1))
      (robust3StrongScheduleT.nome_lt_one (0+n+1)) (W (0+n+1))
      (relativeFactor (etaT n) (relativeRate timeRate capDeltaT n)) :=
  twoStepFactor_mono _ _ _ (le_relativeFactor _ _ (etaT_le_one n)) h

end YMGap.RG.Robust3CrossStrongTier

#print axioms YMGap.RG.Robust3CrossStrongTier.r3NomeT_head
#print axioms YMGap.RG.Robust3CrossStrongTier.r3NomeT_shift
#print axioms YMGap.RG.Robust3CrossStrongTier.strongTab_strict
#print axioms YMGap.RG.Robust3CrossStrongTier.strongT_join
#print axioms YMGap.RG.Robust3CrossStrongTier.robust3StrongScheduleT
#print axioms YMGap.RG.Robust3CrossStrongTier.strongT_sc
#print axioms YMGap.RG.Robust3CrossStrongTier.strongT_sc_tight
#print axioms YMGap.RG.Robust3CrossStrongTier.strongT_dyadic_head
#print axioms YMGap.RG.Robust3CrossStrongTier.strongT_not_dyadic
#print axioms YMGap.RG.Robust3CrossStrongTier.eT_exact
#print axioms YMGap.RG.Robust3CrossStrongTier.etaT_budget
#print axioms YMGap.RG.Robust3CrossStrongTier.afTail_T_value
#print axioms YMGap.RG.Robust3CrossStrongTier.budget_T_ok
#print axioms YMGap.RG.Robust3CrossStrongTier.floor_T_value
#print axioms YMGap.RG.Robust3CrossStrongTier.floor_T_pos
#print axioms YMGap.RG.Robust3CrossStrongTier.fineAtT_iff_B_low
#print axioms YMGap.RG.Robust3CrossStrongTier.fineAtT_four_iff_B
#print axioms YMGap.RG.Robust3CrossStrongTier.hfine_T4_of_old
#print axioms YMGap.RG.Robust3CrossStrongTier.coarseAtT_zero
#print axioms YMGap.RG.Robust3CrossStrongTier.hcross_unifT_of_fine
#print axioms YMGap.RG.Robust3CrossStrongTier.vcZero
#print axioms YMGap.RG.Robust3CrossStrongTier.hupper_phiZeroBelow
#print axioms YMGap.RG.Robust3CrossStrongTier.scaleChain_crossover_floor_off
#print axioms YMGap.RG.Robust3CrossStrongTier.rhoTOf_weight
#print axioms YMGap.RG.Robust3CrossStrongTier.omegaTOf_ge_one
#print axioms YMGap.RG.Robust3CrossStrongTier.capDeltaT_nonneg
#print axioms YMGap.RG.Robust3CrossStrongTier.capDeltaT_le_one
#print axioms YMGap.RG.Robust3CrossStrongTier.r3_seedT
#print axioms YMGap.RG.Robust3CrossStrongTier.robust3T_floor_width_uniform
#print axioms YMGap.RG.Robust3CrossStrongTier.certT2_act
#print axioms YMGap.RG.Robust3CrossStrongTier.certT2_rate
#print axioms YMGap.RG.Robust3CrossStrongTier.twoStepFactor_mono
#print axioms YMGap.RG.Robust3CrossStrongTier.scaleChain_of_twoStepFactor
#print axioms YMGap.RG.Robust3CrossStrongTier.scaleChain_of_twoStepFactor_le
#print axioms YMGap.RG.Robust3CrossStrongTier.scaleChain_twoStep_floor_off
#print axioms YMGap.RG.Robust3CrossStrongTier.htwo_of_fine_crossover
