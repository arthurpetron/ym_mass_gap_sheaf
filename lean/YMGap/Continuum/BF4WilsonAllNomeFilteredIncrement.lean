/-
# The actual common-window signed source for the filtered response slope

Construct [(e_0-e_2)^2-(e_0-e_1)^2] in ONE original radius-two window.
Its original joint limit is exactly twice the lag-one-minus-lag-two
response of the SAME reflected state. The lag-one term is padded using
the existing original-action stationarity theorem, never finite-stationary
by assumption. Signed cancellation is retained before any estimate.

This computes the source and its existing joint modulus, not a quantitative
bound relative to OWN variance, a scaling family or continuum survival.
-/

import YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement
import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation

namespace YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
  (originalJoint_padding)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement

attribute [local irreducible] originalJointLimit intrinsicForm

/-- One literal signed observable; both terms share radius two and action. -/
def filteredExpression {width : Nat} (e : WindowExpression width) :
    WindowExpression width := difference (squareAt e 2) (squareAt e 1)

theorem filteredExpression_within {width : Nat} {e : WindowExpression width}
    (he : Within 0 e) : Within 2 (filteredExpression e) :=
  difference_within (square_within he 2)
    (within_mono (by decide : 1 ≤ 2) _ (square_within he 1))

/-- Existing constructive joint limit of the literal signed source. -/
def filteredIncrement {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) : CReal :=
  originalJointLimit hw0 hw1 2 (filteredExpression e) (filteredExpression_within he)

private theorem padded_first_increment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) :
    Equiv (originalJointLimit hw0 hw1 2 (squareAt e 1)
      (within_mono (by decide : 1 ≤ 2) _ (square_within he 1)))
      (increment hw0 hw1 e he 1) := by
  have h := originalJoint_padding hw0 hw1 1 0 1 (squareAt e 1) (square_within he 1)
  simpa only [Nat.add_zero, shift_zero, increment] using h

/-- Exact cancellation of the common lag-zero moment. Neither increment
is bounded separately and no centered mean is substituted. -/
theorem filteredIncrement_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) {width : Nat}
    (e : WindowExpression width) (he : Within 0 e) :
    Equiv (filteredIncrement hw0 hw1 e he)
      (mul (ofQ' 2) (sub (lagMomentAt hw0 hw1 e he 1)
        (lagMomentAt hw0 hw1 e he 2))) := by
  have h := joint_difference hw0 hw1 2 (squareAt e 2) (squareAt e 1)
    (square_within he 2) (within_mono (by decide : 1 ≤ 2) _ (square_within he 1))
  have hp : Equiv (filteredIncrement hw0 hw1 e he)
      (sub (increment hw0 hw1 e he 2) (increment hw0 hw1 e he 1)) :=
    h.trans (equiv_sub (Equiv.refl _) (padded_first_increment hw0 hw1 e he))
  exact hp.trans ((equiv_sub (increment_pin hw0 hw1 e he 2)
    (increment_pin hw0 hw1 e he 1)).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.add (.var 0) (.neg (.var 2))))
          (.neg (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))))
        (.mul (.const 2) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun
          | 0 => (lagMomentAt hw0 hw1 e he 0).approx n
          | 1 => (lagMomentAt hw0 hw1 e he 1).approx n
          | _ => (lagMomentAt hw0 hw1 e he 2).approx n))))

/-- Forward original signed source meets the SAME reflected two-lag target. -/
theorem filteredIncrement_reflected_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) {width : Nat}
    (e : WindowExpression width) (he : Within 0 e) :
    Equiv (filteredIncrement hw0 hw1 e he)
      (mul (ofQ' 2) (sub
        (intrinsicForm hw0 hw1 (state e he) (advance 1 (state e he)))
        (intrinsicForm hw0 hw1 (state e he) (advance 2 (state e he))))) := by
  have h1 := time_pairing_lag hw0 hw1 e he 0 1
  have h2 := time_pairing_lag hw0 hw1 e he 0 2
  simp only [YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_zero,
    Nat.zero_add] at h1 h2
  exact (filteredIncrement_pin hw0 hw1 e he).trans
    (Pivot2.mul_congr_right (equiv_sub h1.symm h2.symm))

/-- Exact meeting on the constructed UNIT excitation: its OWN real
normalizer multiplies the original signed source twice. Centering cancels
from the lag difference; no inverse variance or new normalization is assumed. -/
theorem dyadicUnit_filtered_source_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat)
    (hwidth : BF4DyadicWilsonSquare.side scale < width) :
    let s := BF4WilsonAllNomeDyadicUnitExcitation.dyadicNormalizer
      hw0 hw1 scale width hwidth
    Equiv
      (mul s (mul s (filteredIncrement hw0 hw1
        (.loop 0 (BF4DyadicWilsonSquare.paddedSquare scale width hwidth) 1)
        (Nat.le_refl 0))))
      (mul (ofQ' 2) (sub
        (BF4WilsonAllNomeDyadicUnitExcitation.dyadicUnitResponse
          hw0 hw1 scale width hwidth 1)
        (BF4WilsonAllNomeDyadicUnitExcitation.dyadicUnitResponse
          hw0 hw1 scale width hwidth 2))) := by
  let s := BF4WilsonAllNomeDyadicUnitExcitation.dyadicNormalizer hw0 hw1 scale width hwidth
  let x := BF4WilsonAllNomeLoopTimePin.loopState
    (BF4DyadicWilsonSquare.paddedSquare scale width hwidth)
  let A := intrinsicForm hw0 hw1 x (advance 1 x)
  let B := intrinsicForm hw0 hw1 x (advance 2 x)
  let M := mul
    (intrinsicForm hw0 hw1 x (BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit width))
    (intrinsicForm hw0 hw1 (BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit width) x)
  have hp : Equiv
      (filteredIncrement hw0 hw1
        (.loop 0 (BF4DyadicWilsonSquare.paddedSquare scale width hwidth) 1)
        (Nat.le_refl 0)) (mul (ofQ' 2) (sub A B)) :=
    filteredIncrement_reflected_pin hw0 hw1
      (.loop 0 (BF4DyadicWilsonSquare.paddedSquare scale width hwidth) 1) (Nat.le_refl 0)
  have hs : Equiv
      (mul s (mul s (filteredIncrement hw0 hw1
        (.loop 0 (BF4DyadicWilsonSquare.paddedSquare scale width hwidth) 1)
        (Nat.le_refl 0))))
      (mul s (mul s (mul (ofQ' 2) (sub A B)))) :=
    Pivot2.mul_congr_right (Pivot2.mul_congr_right hp)
  apply hs.trans
  change Equiv (mul s (mul s (mul (ofQ' 2) (sub A B))))
    (mul (ofQ' 2) (sub (mul s (mul s (sub A M))) (mul s (mul s (sub B M)))))
  exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 0) (.mul (.const 2) (.add (.var 1) (.neg (.var 2))))))
      (.mul (.const 2) (.add
        (.mul (.var 0) (.mul (.var 0) (.add (.var 1) (.neg (.var 3)))))
        (.neg (.mul (.var 0) (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))))))
      (by decide) (fun
        | 0 => s.approx n | 1 => A.approx n | 2 => B.approx n | _ => M.approx n))

#print axioms filteredExpression
#print axioms filteredExpression_within
#print axioms filteredIncrement
#print axioms filteredIncrement_pin
#print axioms filteredIncrement_reflected_pin
#print axioms dyadicUnit_filtered_source_pin

end YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement
