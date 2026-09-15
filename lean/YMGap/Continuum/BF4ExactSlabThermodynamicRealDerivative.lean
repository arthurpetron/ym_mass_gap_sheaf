/-
# Real-time derivative on the ORIGINAL transfer range

The dyadic Taylor remainders form actual original Cauchy rows: constant
transfer rows minus the existing time rows minus explicit scalar rows of
the previously constructed derivative. Their limit is the SAME real-time
remainder, using the OLD real-scalar operation. Eventual dyadic estimates
therefore pass to this limit, with the time coefficient retained.

For every supplied original representative and positive rational epsilon,
one computed positive radius controls EVERY supplied positive real time
below it: ||T2y-A_t(T2y)-t*J(y)||^2 <= epsilon*t^2. No inverse time or
quotient representative is selected. This is a real-time derivative in
T2 units, not yet a self-adjoint generator identification, a physical-scale
Hamiltonian, or a continuum/all-group Clay theorem. The original fixed
SU(2), nome 1/1024 and spacing restrictions remain unchanged.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows
import YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry (completedSub)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (timeCauchy twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (action_embed)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative
open YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal (convergesTo_mul_general)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def realRemainder (D : PositiveTime) (x : Completion) : Completion :=
  completedSub (completedSub (twoStepTransfer x) (realTimeAction (timeValue D) (twoStepTransfer x)))
    (completedRealSmul D.real D.cauchy (derivativeAction x))

def remainderRows (D : PositiveTime) (X : seminorm.Cauchy) : CauchyRows :=
  differenceRows
    (differenceRows (constantRows (timeCauchy 2 X)) (timeRows D (timeCauchy 2 X)))
    (scalarRows (approximationReal D) (approximationCauchy D) (derivativeRepresentative X))

theorem remainderRows_pin (D : PositiveTime) (X : seminorm.Cauchy) (n : Nat) :
    rowPoint (remainderRows D X) n=
      meshRemainder (approximation D n).depth (approximation D n).steps (point X) := by
  unfold remainderRows
  rw [differenceRows_pin,differenceRows_pin,constantRows_pin,timeRows_pin,scalarRows_pin,
    action_embed,derivativeRepresentative_pin]
  rfl

theorem remainderRows_limit (D : PositiveTime) (X : seminorm.Cauchy) :
    rowLimit (remainderRows D X)=realRemainder D (point X) := by
  unfold remainderRows
  rw [rowLimit_difference,rowLimit_difference,rowLimit_constant,scalarRows_limit,
    derivativeRepresentative_pin,
    completedRealSmul_congr _ _ _ D.cauchy (approximationReal_equiv D)]
  rfl

def realRadius (X : seminorm.Cauchy) (epsilon : Q') : Q' := HalfPow.half*meshRadius X epsilon

theorem realRadius_positive (X : seminorm.Cauchy) (epsilon : Q') : (0 : Q')<realRadius X epsilon :=
  ExpNeg.half_mul_pos _ (meshRadius_positive X epsilon)

/-- A computed radius for ALL supplied positive real increments, in the original norm. -/
theorem real_taylor_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (D : PositiveTime) (ht : RCle (realValue (timeValue D)) (rat (realRadius X epsilon))) :
    RCle (B (realRemainder D (point X)) (realRemainder D (point X)))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon)) := by
  have htime : Quotient.mk crealSetoid (approximationReal D)=realValue (timeValue D) :=
    Quotient.sound (approximationReal_equiv D)
  have hap : RCle (Quotient.mk crealSetoid (approximationReal D)) (rat (realRadius X epsilon)) := by
    rw [htime]
    exact ht
  change leEv (approximationReal D) (ofQ' (realRadius X epsilon)) at hap
  obtain ⟨N,hN⟩ := hap (realRadius X epsilon) (realRadius_positive X epsilon)
  have hsmall (n : Nat) (hn : N≤n) : value (approximation D n)≤meshRadius X epsilon :=
    Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (ExpNeg.two_halves (meshRadius X epsilon)))
  let R := remainderRows D X
  have hleft := pairing_converges R R
  have hright : ConvergesTo
      (fun n => CReal.mul (CReal.mul (ofQ' (value (approximation D n))) (ofQ' (value (approximation D n)))) (ofQ' epsilon))
      (CReal.mul (CReal.mul (approximationReal D) (approximationReal D)) (ofQ' epsilon)) :=
    convergesTo_mul_general
      (convergesTo_mul_general (convergesTo_self (approximationReal D)) (convergesTo_self (approximationReal D)))
      (convergesTo_const _)
  have h := limit_le_of_eventual hleft hright N (by
    intro n hn
    change RCle (B (rowPoint R n) (rowPoint R n))
      (rat ((value (approximation D n)*value (approximation D n))*epsilon))
    rw [show R=remainderRows D X from rfl,remainderRows_pin]
    exact mesh_taylor_bound X epsilon he (approximation D n).depth (approximation D n).steps (hsmall n hn))
  change RCle (B (rowLimit R) (rowLimit R))
    (RCmul (RCmul (Quotient.mk crealSetoid (approximationReal D))
      (Quotient.mk crealSetoid (approximationReal D))) (rat epsilon)) at h
  rw [show R=remainderRows D X from rfl,remainderRows_limit,htime] at h
  exact h

/-- The radius remains usable data; the derivative output was constructed previously. -/
def realTaylorCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' radius : Q', ((0 : Q')<radius) ×'
      (∀ D : PositiveTime, RCle (realValue (timeValue D)) (rat radius) →
        RCle (B (realRemainder D (point X)) (realRemainder D (point X)))
          (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon))) :=
  ⟨realRadius X epsilon,realRadius_positive X epsilon,fun D ht => real_taylor_bound X epsilon he D ht⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.realRemainder
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.remainderRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.remainderRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.remainderRows_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.realRadius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.realRadius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.real_taylor_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative.realTaylorCertificate
