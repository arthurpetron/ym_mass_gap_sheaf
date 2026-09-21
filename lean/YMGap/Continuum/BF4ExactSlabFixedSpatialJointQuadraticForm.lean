/-
# Quadratic positivity on the actual fixed-spatial joint completion

Reflection positivity of the dense original joint pairing is applied to the
literal physical presentation `x - rho*y`.  Its exact four-term expansion is
then passed through the existing scalar limits and quotient descent.  Thus the
result concerns the already constructed `JointCompletion` and
`completedInner`; it does not add completed linear operations, a spectral
calculus, or any analytic hypothesis.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
import YMGap.Continuum.RCScaleClose
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointQuadraticForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner

private theorem sub_congr {a b c d : CReal} (hab : Equiv a b) (hcd : Equiv c d) :
    Equiv (sub a c) (sub b d) :=
  Equiv_add hab (neg_congr hcd)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width

/-- Positivity of the literal dense presentation `x - rho*y`, written without
introducing a new dense-vector operation in the conclusion. -/
theorem jointPairing_scaledDifference_nonnegative
    (x y : PhysicalSpan width) (rho : Q') :
    leEv czero
      (sub
        (sub (jointPairing hw0 hw1 width x x)
          (mul (ofQ' rho) (jointPairing hw0 hw1 width x y)))
        (mul (ofQ' rho)
          (sub (jointPairing hw0 hw1 width y x)
            (mul (ofQ' rho) (jointPairing hw0 hw1 width y y))))) := by
  let ry := smulSpan rho y
  let d := differenceSpan x ry
  have hxy : Equiv (jointPairing hw0 hw1 width x ry)
      (mul (ofQ' rho) (jointPairing hw0 hw1 width x y)) :=
    jointPairing_smul_right hw0 hw1 width rho x y
  have hyx : Equiv (jointPairing hw0 hw1 width ry x)
      (mul (ofQ' rho) (jointPairing hw0 hw1 width y x)) :=
    jointPairing_smul_left hw0 hw1 width rho y x
  have hyyInner : Equiv (jointPairing hw0 hw1 width y ry)
      (mul (ofQ' rho) (jointPairing hw0 hw1 width y y)) :=
    jointPairing_smul_right hw0 hw1 width rho y y
  have hyy : Equiv (jointPairing hw0 hw1 width ry ry)
      (mul (ofQ' rho) (mul (ofQ' rho) (jointPairing hw0 hw1 width y y))) :=
    (jointPairing_smul_left hw0 hw1 width rho y ry).trans
      (TrigSignedAdd.mul_congr_right hyyInner)
  have hexpand : Equiv (jointPairing hw0 hw1 width d d)
      (sub
        (sub (jointPairing hw0 hw1 width x x)
          (mul (ofQ' rho) (jointPairing hw0 hw1 width x y)))
        (sub
          (mul (ofQ' rho) (jointPairing hw0 hw1 width y x))
          (mul (ofQ' rho) (mul (ofQ' rho) (jointPairing hw0 hw1 width y y))))) :=
    (jointPairing_difference_diagonal hw0 hw1 width x ry).trans
      (sub_congr (sub_congr (Equiv.refl _) hxy) (sub_congr hyx hyy))
  have hfactor : Equiv
      (sub
        (mul (ofQ' rho) (jointPairing hw0 hw1 width y x))
        (mul (ofQ' rho) (mul (ofQ' rho) (jointPairing hw0 hw1 width y y))))
      (mul (ofQ' rho)
        (sub (jointPairing hw0 hw1 width y x)
          (mul (ofQ' rho) (jointPairing hw0 hw1 width y y)))) :=
    (CReal.mul_sub (ofQ' rho) (jointPairing hw0 hw1 width y x)
      (mul (ofQ' rho) (jointPairing hw0 hw1 width y y))).symm
  exact leEv_trans (jointPairing_nonnegative hw0 hw1 width d)
    (leEv_of_equiv (hexpand.trans (sub_congr (Equiv.refl _) hfactor)))

/-- The same quadratic positivity for arbitrary supplied Cauchy
representatives of the actual joint completion. -/
theorem representativeInner_scaledDifference_nonnegative
    (X Y : (D).Cauchy) (rho : Q') :
    leEv czero
      (sub
        (sub (representativeInner hw0 hw1 width X X)
          (mul (ofQ' rho) (representativeInner hw0 hw1 width X Y)))
        (mul (ofQ' rho)
          (sub (representativeInner hw0 hw1 width Y X)
            (mul (ofQ' rho) (representativeInner hw0 hw1 width Y Y))))) := by
  have hXX := pairSequence_converges hw0 hw1 width X X
  have hXY := pairSequence_converges hw0 hw1 width X Y
  have hYX := pairSequence_converges hw0 hw1 width Y X
  have hYY := pairSequence_converges hw0 hw1 width Y Y
  apply leEv_of_convergesTo_le (convergesTo_const czero)
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add hXX
        (TrigAddCReal.convergesTo_neg (convergesTo_const_mul (ofQ' rho) hXY)))
      (TrigAddCReal.convergesTo_neg
        (convergesTo_const_mul (ofQ' rho)
          (TrigAddCReal.convergesTo_add hYX
            (TrigAddCReal.convergesTo_neg (convergesTo_const_mul (ofQ' rho) hYY))))))
  intro n
  exact jointPairing_scaledDifference_nonnegative hw0 hw1 width (X.seq n) (Y.seq n) rho

/-- Positivity of `x - rho*y` expressed solely through the existing completed
pairing.  No completed subtraction or scalar action is required. -/
theorem completedInner_scaledDifference_nonnegative
    (x y : JointCompletion hw0 hw1 width) (rho : Q') :
    RCnonneg
      (RCsub
        (RCsub (B x x) (RCscale rho (B x y)))
        (RCscale rho (RCsub (B y x) (RCscale rho (B y y))))) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  change leEv czero
    (sub
      (sub (representativeInner hw0 hw1 width X X)
        (mul (ofQ' rho) (representativeInner hw0 hw1 width X Y)))
      (mul (ofQ' rho)
        (sub (representativeInner hw0 hw1 width Y X)
          (mul (ofQ' rho) (representativeInner hw0 hw1 width Y Y)))))
  exact representativeInner_scaledDifference_nonnegative hw0 hw1 width X Y rho

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointQuadraticForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointQuadraticForm.jointPairing_scaledDifference_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointQuadraticForm.representativeInner_scaledDifference_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointQuadraticForm.completedInner_scaledDifference_nonnegative
