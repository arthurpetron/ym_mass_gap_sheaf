/-
# Every continuum nome schedule exits the thermodynamic strong-coupling guard

The parametric expression thermodynamic limit and its two-nome comparison
require `heatRatio w <= 1/2`.  A repository `NomeSchedule`, however, converges
to one.  Its explicit limit modulus therefore gives a finite index after which
that guard is impossible.

This rules out constructing the continuum functional by applying the guarded
thermodynamic producer directly at every scale.  A same-action RG comparison
through the intermediate/weak-coupling region remains necessary.
-/

import YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicCoupling
import YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory

namespace YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicGuardExit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- The character heat-ratio envelope is monotone in the nonnegative nome. -/
theorem heatRatio_mono {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v) :
    heatRatio u ≤ heatRatio v := by
  unfold heatRatio
  have hp : YMGap.Continuum.RGTransport.qpow u 3 ≤
      YMGap.Continuum.RGTransport.qpow v 3 :=
    YMGap.Continuum.HeatKernelGap.qpow_mono hu0 huv 3
  have hleft : (2 : Q') * YMGap.Continuum.RGTransport.qpow u 3 ≤
      2 * YMGap.Continuum.RGTransport.qpow v 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 hp (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ 16 hleft (by decide)

/-- A concrete index after which the schedule nome is at least `3/4`. -/
def guardExitIndex (schedule : NomeSchedule) : Nat :=
  schedule.limitModulus (HalfPow.half * HalfPow.half)

theorem half_le_nome_of_guardExitIndex (schedule : NomeSchedule) (stage : Nat)
    (hstage : guardExitIndex schedule ≤ stage) :
    HalfPow.half ≤ schedule.nome stage := by
  have hlimit := schedule.nome_limit (HalfPow.half * HalfPow.half)
    (by decide) stage hstage
  exact Q'.le_trans' _ _ _
    (by decide : HalfPow.half ≤ (1 : Q') - HalfPow.half * HalfPow.half)
    hlimit

/-- Every continuum nome schedule eventually violates the exact heat-ratio
guard used by the parametric thermodynamic construction. -/
theorem nomeSchedule_eventually_not_heatRatio_le_half (schedule : NomeSchedule) :
    ∀ stage, guardExitIndex schedule ≤ stage →
      ¬ (heatRatio (schedule.nome stage) ≤ HalfPow.half) := by
  intro stage hstage hguard
  have hmono : heatRatio HalfPow.half ≤ heatRatio (schedule.nome stage) :=
    heatRatio_mono HalfPow.half_nonneg
      (half_le_nome_of_guardExitIndex schedule stage hstage)
  have himpossible : heatRatio HalfPow.half ≤ HalfPow.half :=
    Q'.le_trans' _ _ _ hmono hguard
  have hnot : ¬ (heatRatio HalfPow.half ≤ HalfPow.half) := by
    unfold heatRatio
    decide
  exact hnot himpossible

/-- No `NomeSchedule` can supply the strong-coupling heat-ratio guard at all
scales.  In particular, the guarded thermodynamic producer cannot directly
inhabit a continuum-stage family. -/
theorem no_nomeSchedule_all_heatRatio_guard (schedule : NomeSchedule) :
    ¬ (∀ stage, heatRatio (schedule.nome stage) ≤ HalfPow.half) := by
  intro hall
  exact nomeSchedule_eventually_not_heatRatio_le_half schedule
    (guardExitIndex schedule) (Nat.le_refl _) (hall (guardExitIndex schedule))

end YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicGuardExit

#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicGuardExit.heatRatio_mono
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicGuardExit.guardExitIndex
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicGuardExit.half_le_nome_of_guardExitIndex
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicGuardExit.nomeSchedule_eventually_not_heatRatio_le_half
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicGuardExit.no_nomeSchedule_all_heatRatio_guard
