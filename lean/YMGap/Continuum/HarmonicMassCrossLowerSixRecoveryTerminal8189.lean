/-
Isolated exact terminal check for the finite lower-six recovery bridge.

The closed rational decision is deliberately kept out of the generic
finite-difference module.  Its sole numerical inputs are the derived exact
endpoint `k=8189`, denominator `D=8191`, and square-root center `c=127`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189

set_option maxHeartbeats 24000000
set_option maxRecDepth 200000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

local infix:50 " ≈ " => Q'.eqv

/-- Exact endpoint center: `2*(8189+2)+1 = 16383` lies between
`127^2=16129` and `128^2=16384`. -/
theorem thetaWindowCenter_8189 : thetaWindowCenter 8189 = 127 := by
  unfold thetaWindowCenter thetaWindowLength
  decide

/-- The load-bearing closed-rational endpoint check.  No measured value is
present in the statement or proof. -/
theorem lowerSixFixedCenterSparseSlack_8189_127_nonnegative :
    (0 : Q') ≤ lowerSixFixedCenterSparseSlack 8189 127 := by
  decide

theorem lowerSixCenterSlack_8189_nonnegative :
    (0 : Q') ≤ lowerSixCenterSlack 8189 := by
  have hfixedEq := lowerSixCenterSlack_eqv_fixed 8189
  rw [thetaWindowCenter_8189] at hfixedEq
  have hsparseEq := lowerSixFixedCenterSlack_eqv_sparse 8189 127
  have hfixed : (0 : Q') ≤ lowerSixFixedCenterSlack 8189 127 :=
    Q'.le_trans' _ _ _
      lowerSixFixedCenterSparseSlack_8189_127_nonnegative
      (Q'.le_of_eqv (Q'.eqv_symm hsparseEq))
  exact Q'.le_trans' _ _ _ hfixed
    (Q'.le_of_eqv (Q'.eqv_symm hfixedEq))

theorem lowerSixRecoverySlack_8189_nonnegative :
    (0 : Q') ≤ lowerSixRecoverySlack 8189 := by
  exact Q'.le_trans' _ _ _ lowerSixCenterSlack_8189_nonnegative
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixRecoverySlack_eqv_centerSlack 8189)))

private theorem recovery_slack_as_subtraction (k : Nat) :
    lowerSixRecoverySlack k ≈
      lowerSixRecoveryReserve k + -(-lowerSixWindowPrefix k) := by
  unfold lowerSixRecoverySlack
  refine Q'.eqv_trans _
    (lowerSixRecoveryReserve k + lowerSixWindowPrefix k) _
    (Q'.add_comm_eqv _ _) ?_
  exact Q'.add_eqv_congr_left (lowerSixRecoveryReserve k) _ _
    (Q'.eqv_symm (Q'.neg_neg_eqv (lowerSixWindowPrefix k)))

/-- Exact recovery payment at the terminal finite scale. -/
theorem lowerSixRecoveryPayment_8189 :
    -lowerSixWindowPrefix 8189 ≤ lowerSixRecoveryReserve 8189 := by
  have hsub : (0 : Q') ≤
      lowerSixRecoveryReserve 8189 + -(-lowerSixWindowPrefix 8189) :=
    Q'.le_trans' _ _ _ lowerSixRecoverySlack_8189_nonnegative
      (Q'.le_of_eqv (recovery_slack_as_subtraction 8189))
  exact Q'.le_of_sub_nonneg hsub

/-- The exact physical anchor required by the production tail theorem. -/
theorem lowerSixInteriorPayment_8189_nonnegative :
    (0 : Q') ≤ lowerSixInteriorPayment 8189 := by
  unfold lowerSixInteriorPayment
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual
    (by decide) lowerSixRecoveryPayment_8189

#print axioms thetaWindowCenter_8189
#print axioms lowerSixFixedCenterSparseSlack_8189_127_nonnegative
#print axioms lowerSixCenterSlack_8189_nonnegative
#print axioms lowerSixRecoveryPayment_8189
#print axioms lowerSixInteriorPayment_8189_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189
