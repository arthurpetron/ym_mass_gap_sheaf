/-
# The pilot nome `1/1024` is never a nome of an existing `NomeSchedule`

**Label: PROVED no-go for the shortcut + OPEN interpolation input. NOT gap evidence.**

`UniformSeedGap.uniformSeedGap_of_eq_pilot` would hand the strong-coupling seed to the r49 chain
if some schedule had `w_{j0} = existingPilotNome = 1/1024`. It never fires on the repository's
concrete schedules (`rg 'NomeSchedule where'`):

* `dyadicNomeSchedule` (`w_j = 1 - 2^-(j+1)`, the dyadic smoothed trajectory's schedule),
* `afNomeSchedule` (`w_j = 1 - A/D_j`, the schedule of the padded AF trajectory and of
  `afPaddedZeroMomentumExpr`),
* `precisionNomeSchedule` (`w_j = 1 - gap_j`, `gap_j ≤ 1/2`).

Each starts strictly above `1/1024`, and every `NomeSchedule` is nondecreasing, so
`1/1024 < w_j` for EVERY `j` (`pilot_lt_of_start`); shifting `j0` cannot help.

The remaining gap is recorded as the OPEN input `PilotToScheduleSeedInterpolation ns j0 budget`:
transfer of the width-uniform seed from `w = 1/1024` to `w_{j0}`. Because the pilot side is
PROVED, this input is EQUIVALENT to `UniformSeedGap` at `w_{j0}` (`interpolation_iff`): it is a
name for the gap, not a weakening of it.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.UniformSeedGap
import YMGap.Continuum.AFPrecisionNomeSchedule

namespace YMGap.RG.PilotScheduleGap

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA afNomeSchedule)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule dyadicNomeSchedule)
open YMGap.Continuum.AFPrecisionNomeSchedule (precisionNomeSchedule)
open YMGap.RG.RelativeDissipationScaleChain (SchurDecomposition inv)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.Continuum.BF4WilsonStrongCouplingUniformRate (existingPilotNome)
open YMGap.RG.UniformSeedGap
  (UniformSeedGap uniformSeedGap_existingNome scaleChain_afBudget_floor_of_uniformSeedGap)

private theorem q_lt_irrefl (a : Q') : ¬ a < a := fun h => by
  have e : a.num * (a.den : Int) < a.num * (a.den : Int) := h
  exact Int.lt_irrefl _ e

/-- **Monotone schedules stay above the pilot (PROVED).** -/
theorem pilot_lt_of_start (ns : NomeSchedule) (h0 : existingPilotNome < ns.nome 0) :
    ∀ j, existingPilotNome < ns.nome j
  | 0 => h0
  | j+1 => YMGap.Continuum.MatchedRetuneBridge.q_lt_of_lt_of_le
      (pilot_lt_of_start ns h0 j) (ns.nome_mono j)

/-- **No index of such a schedule is the pilot nome (PROVED).** -/
theorem nome_ne_pilot_of_start (ns : NomeSchedule) (h0 : existingPilotNome < ns.nome 0)
    (j : Nat) : ns.nome j ≠ existingPilotNome := fun h => by
  have hl := pilot_lt_of_start ns h0 j
  rw [h] at hl
  exact q_lt_irrefl _ hl

/-- `w_0 = 1/2` for the dyadic schedule (decidable). -/
theorem dyadic_pilot_lt_start : existingPilotNome < dyadicNomeSchedule.nome 0 := by decide

/-- `w_0 = 1 - 234982/484000 ≈ 0.5145` for the AF schedule (decidable). -/
theorem af_pilot_lt_start : existingPilotNome < afNomeSchedule.nome 0 := by decide

/-- `w_0 = 1 - gap_0 ≥ 1/2` for the precision schedule (`gap_le_half`). -/
theorem precision_pilot_lt_start : existingPilotNome < precisionNomeSchedule.nome 0 :=
  YMGap.Continuum.MatchedRetuneBridge.q_lt_of_lt_of_le
    (show existingPilotNome < (1 : Q') - HalfPow.half by decide)
    (Q'.add_le_add_left 1 _ _
      (Q'.neg_le_neg (YMGap.Continuum.AFPrecisionNomeSchedule.gap_le_half 0)))

/-- **`uniformSeedGap_of_eq_pilot` never fires on the dyadic schedule (PROVED).** -/
theorem dyadic_nome_ne_pilot (j : Nat) : dyadicNomeSchedule.nome j ≠ existingPilotNome :=
  nome_ne_pilot_of_start _ dyadic_pilot_lt_start j

/-- **… nor on the AF (padded-trajectory) schedule (PROVED).** -/
theorem af_nome_ne_pilot (j : Nat) : afNomeSchedule.nome j ≠ existingPilotNome :=
  nome_ne_pilot_of_start _ af_pilot_lt_start j

/-- **… nor on the precision AF schedule (PROVED).** -/
theorem precision_nome_ne_pilot (j : Nat) : precisionNomeSchedule.nome j ≠ existingPilotNome :=
  nome_ne_pilot_of_start _ precision_pilot_lt_start j

/-- **OPEN interpolation input.** Transfer of the width-uniform seed from the strong-coupling
pilot nome `1/1024` to the schedule's IR seed nome `w_{j0}` (≥ 1/2 on every existing schedule). -/
def PilotToScheduleSeedInterpolation (ns : NomeSchedule) (j0 : Nat) (budget : Q') : Prop :=
  ∀ (hp0 : (0 : Q') < existingPilotNome) (hp1 : existingPilotNome < (1 : Q')),
    UniformSeedGap hp0 hp1 budget → UniformSeedGap (ns.nome_pos j0) (ns.nome_lt_one j0) budget

/-- **Honesty check (PROVED):** below `timeRate` the interpolation input is equivalent to the
seed at `w_{j0}` itself; it names the gap and does not shrink it. -/
theorem interpolation_iff (ns : NomeSchedule) (j0 : Nat) (budget : Q') (hb : budget < timeRate) :
    PilotToScheduleSeedInterpolation ns j0 budget ↔
      UniformSeedGap (ns.nome_pos j0) (ns.nome_lt_one j0) budget :=
  ⟨fun hI => by
    obtain ⟨hp0, hp1, hU⟩ := uniformSeedGap_existingNome budget hb
    exact hI hp0 hp1 hU,
   fun hU _ _ _ => hU⟩

/-- **What the r49 capstone still needs from the pilot (PROVED reduction).** Given the budget
condition `C·afA²/(j0+2) < timeRate` and the OPEN interpolation, the r49 floor follows, still
conditional on `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN` at every scale `j0+n`. -/
theorem scaleChain_floor_of_pilotInterpolation (ns : NomeSchedule) (j0 : Nat) (C : Q')
    (hC : (0 : Q') ≤ C) (hbudget : C * (afA * afA) * inv (j0+2) < timeRate)
    (hI_OPEN : PilotToScheduleSeedInterpolation ns j0 (C * (afA * afA) * inv (j0+2))) :
    ∃ s : Q', (0 : Q') < ((1 : Q') - s) * (s - C * (afA * afA) * inv (j0+2)) ∧
      ∀ (width : Nat → Nat) (delta : Nat → Q')
        (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
        (_hafδ_OPEN : ∀ k, delta k ≤ C * (afGap (j0+k) * afGap (j0+k)))
        (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
            (width := width (j0+n+1)) →
          VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
        (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
            (width := width (j0+n+1)) → RC)
        (_hupper_OPEN : ∀ n y, RCle
          (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
          (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
        (_hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
          (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n))
          (delta n) (Phi n) (D n))
        (n : Nat),
        WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
            (relativeRate s delta n) ∧
          ((1 : Q') - s) * (s - C * (afA * afA) * inv (j0+2)) ≤
            Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate s delta) n :=
  scaleChain_afBudget_floor_of_uniformSeedGap ns j0 C hC
    ((interpolation_iff ns j0 _ hbudget).mp hI_OPEN)

/-- The budget condition is decidable for concrete data; e.g. `C = 1/10`, `j0 = 8`. -/
theorem budget_lt_timeRate_example :
    Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2) < timeRate := by decide

end YMGap.RG.PilotScheduleGap
