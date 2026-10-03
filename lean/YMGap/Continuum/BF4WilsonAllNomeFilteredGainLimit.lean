/-
# The original quadratic filtered gain on the SAME completed carrier

The lag-one term is the already constructed centered transfer limit,
not the odd marginal variance. Combine it with the COMPLETE original
filtered source, with its sign intact. The resulting constructive real
is pinned to C2-a*C1 on the existing centered vector and time operator.

The rational a is a reference coefficient, not an asserted centered
eigenvalue. No favorable gain, reserve, changing-family uniformity or
continuum result is assumed or established.
-/

import YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
import YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement
import YMGap.Continuum.BoundedRationalCauchyProduct

namespace YMGap.Continuum.BF4WilsonAllNomeFilteredGainLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
  (singleSlice transferLimit transferCauchy transferLimit_completed_pin)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit (bond_connected_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
  (originalJointCauchy originalJointLimit)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)

attribute [local irreducible] intrinsicForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (e : WindowExpression width) (he : Within 0 e)

/-- Keep the existing original C1 limit and complete signed source F.
Neither term is replaced by an uncentered variance or a raw channel norm. -/
def gainLimit (a : Q') : CReal :=
  sub (mul (ofQ' (1-a)) (transferLimit hw0 hw1 e he))
    (mul (ofQ' HalfPow.half) (filteredIncrement hw0 hw1 e he))

private def constantCauchy (a : Q') : QCauchy (ofQ' a).approx where
  M _ := 0
  bound := fun epsilon hp _ _ _ _ =>
    let h := Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hp)
    ⟨h, h⟩

/-- The approximation modulus is computed from the original joint moduli
and the existing constructive scalar arithmetic. -/
def gainLimitCauchy (a : Q') : QCauchy (gainLimit hw0 hw1 e he a).approx :=
  let C1 := transferLimit hw0 hw1 e he
  let F := filteredIncrement hw0 hw1 e he
  let c1 := BoundedRationalCauchyProduct.representativeCauchy _
    (transferCauchy hw0 hw1 e he)
  let cf := BoundedRationalCauchyProduct.representativeCauchy _
    (originalJointCauchy hw0 hw1 2 (filteredExpression e) (filteredExpression_within he))
  scalarAddCauchy (mul (ofQ' (1-a)) C1) (neg (mul (ofQ' HalfPow.half) F))
    (scalarMulCauchy _ _ (constantCauchy (1-a)) c1)
    (scalarNegCauchy _ (scalarMulCauchy _ _ (constantCauchy HalfPow.half) cf))

private theorem transfer_centered_pin :
    Equiv (transferLimit hw0 hw1 e he)
      (centeredTimeMoment hw0 hw1 1 (state e he) (state e he)) := by
  have h := transferLimit_completed_pin hw0 hw1 e he
  rw [bond_connected_time_pairing, centeredVector_time_pairing] at h
  exact Quotient.exact h

private theorem filtered_centered_pin :
    Equiv (filteredIncrement hw0 hw1 e he)
      (mul (ofQ' 2) (sub
        (centeredTimeMoment hw0 hw1 1 (state e he) (state e he))
        (centeredTimeMoment hw0 hw1 2 (state e he) (state e he)))) := by
  apply (filteredIncrement_reflected_pin hw0 hw1 e he).trans
  let x := state e he
  let A := intrinsicForm hw0 hw1 x (advance 1 x)
  let B := intrinsicForm hw0 hw1 x (advance 2 x)
  let M := mul (intrinsicForm hw0 hw1 x (unit width))
    (intrinsicForm hw0 hw1 (unit width) x)
  exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
      (.mul (.const 2) (.add (.add (.var 0) (.neg (.var 2)))
        (.neg (.add (.var 1) (.neg (.var 2))))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => M.approx n))

/-- Exact SAME-object quadratic gain; no reference-eigenmode hypothesis. -/
theorem gainLimit_centered_pin (a : Q') :
    Equiv (gainLimit hw0 hw1 e he a)
      (sub (centeredTimeMoment hw0 hw1 2 (state e he) (state e he))
        (mul (ofQ' a) (centeredTimeMoment hw0 hw1 1 (state e he) (state e he)))) := by
  have h : Equiv (gainLimit hw0 hw1 e he a)
      (sub (mul (ofQ' (1-a))
        (centeredTimeMoment hw0 hw1 1 (state e he) (state e he)))
        (mul (ofQ' HalfPow.half) (mul (ofQ' 2) (sub
          (centeredTimeMoment hw0 hw1 1 (state e he) (state e he))
          (centeredTimeMoment hw0 hw1 2 (state e he) (state e he)))))) := equiv_sub
    (Pivot2.mul_congr_right (transfer_centered_pin hw0 hw1 e he))
    (Pivot2.mul_congr_right (filtered_centered_pin hw0 hw1 e he))
  apply h.trans
  let C1 := centeredTimeMoment hw0 hw1 1 (state e he) (state e he)
  let C2 := centeredTimeMoment hw0 hw1 2 (state e he) (state e he)
  have hh : Equiv (mul (ofQ' HalfPow.half) (mul (ofQ' 2) (sub C1 C2)))
      (sub C1 C2) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv HalfPow.half 2 _).symm
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (by decide : Q'.eqv (HalfPow.half*2) 1)) (Q'.one_mul_eqv _)))
  apply (equiv_sub (Equiv.refl _) hh).trans
  exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 2) (.neg (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => a | 1 => C1.approx n | _ => C2.approx n))

/-- The original completion and its existing centered vector and T occur
on both sides. This is a gain identity, not a favorable-gain bound. -/
theorem gainLimit_completed_pin (a : Q') :
    Quotient.mk crealSetoid (gainLimit hw0 hw1 e he a) =
      RCsub
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (completedTime hw0 hw1 2 (centeredVector hw0 hw1 (state e he))))
        (RCscale a
          (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
            (completedTime hw0 hw1 1 (centeredVector hw0 hw1 (state e he))))) := by
  rw [centeredVector_time_pairing, centeredVector_time_pairing]
  exact Quotient.sound (gainLimit_centered_pin hw0 hw1 e he a)

/-- The SAME normalizer twice converts the original gain to the existing
unit response. There is no new inverse or normalized carrier. -/
theorem dyadicUnit_gain_pin (scale width : Nat)
    (hwidth : BF4DyadicWilsonSquare.side scale < width) (a : Q') :
    let e := WindowExpression.loop 0
      (BF4DyadicWilsonSquare.paddedSquare scale width hwidth) 1
    let s := BF4WilsonAllNomeDyadicUnitExcitation.dyadicNormalizer
      hw0 hw1 scale width hwidth
    Equiv (mul s (mul s (gainLimit hw0 hw1 e (Nat.le_refl 0) a)))
      (sub (BF4WilsonAllNomeDyadicUnitExcitation.dyadicUnitResponse
        hw0 hw1 scale width hwidth 2)
        (mul (ofQ' a) (BF4WilsonAllNomeDyadicUnitExcitation.dyadicUnitResponse
          hw0 hw1 scale width hwidth 1))) := by
  let e := WindowExpression.loop 0
    (BF4DyadicWilsonSquare.paddedSquare scale width hwidth) 1
  let s := BF4WilsonAllNomeDyadicUnitExcitation.dyadicNormalizer
    hw0 hw1 scale width hwidth
  let C1 := centeredTimeMoment hw0 hw1 1 (state e (Nat.le_refl 0)) (state e (Nat.le_refl 0))
  let C2 := centeredTimeMoment hw0 hw1 2 (state e (Nat.le_refl 0)) (state e (Nat.le_refl 0))
  have h : Equiv (mul s (mul s (gainLimit hw0 hw1 e (Nat.le_refl 0) a)))
      (mul s (mul s (sub C2 (mul (ofQ' a) C1)))) :=
    Pivot2.mul_congr_right
      (Pivot2.mul_congr_right (gainLimit_centered_pin hw0 hw1 e (Nat.le_refl 0) a))
  apply h.trans
  exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 0) (.add (.var 2) (.neg (.mul (.var 3) (.var 1))))))
      (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
        (.neg (.mul (.var 3) (.mul (.var 0) (.mul (.var 0) (.var 1))))))
      (by decide) (fun | 0 => s.approx n | 1 => C1.approx n | 2 => C2.approx n | _ => a))

#print axioms gainLimit
#print axioms gainLimitCauchy
#print axioms gainLimit_centered_pin
#print axioms gainLimit_completed_pin
#print axioms dyadicUnit_gain_pin

end YMGap.Continuum.BF4WilsonAllNomeFilteredGainLimit
