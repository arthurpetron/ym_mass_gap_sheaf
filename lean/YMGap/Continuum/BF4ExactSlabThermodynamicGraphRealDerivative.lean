/-
# The ORIGINAL real-time action differentiates on the WHOLE closed graph

For supplied original representatives U,V with J u=T2 v, return one
computed positive radius for every positive real time below it:
  ||u-A_t u-t*v||^2 <= epsilon*t^2.
The original mesh remainder rows converge to this SAME real remainder,
using the old completedRealSmul and realTimeAction. The previously
proved whole-graph dyadic bound passes with its time coefficient intact.

This proves differentiation on every represented graph point; it does
not yet prove the converse maximal differentiability-domain statement,
or inhabit a canonical physical Hamiltonian/spectral interface. No
logarithmic candidate is substituted for the actual image v. Fixed
SU(2), nome 1/1024, fixed spacing and T2-time units remain; physical
calibration, continuum QFT and all-group Clay stay open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry (completedSub)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (action_embed)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal (convergesTo_mul_general)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def remainder (D : PositiveTime) (u v : Completion) : Completion :=
  completedSub (completedSub u (realTimeAction (timeValue D) u)) (completedRealSmul D.real D.cauchy v)

def remainderRows (D : PositiveTime) (U V : seminorm.Cauchy) : CauchyRows :=
  differenceRows (differenceRows (constantRows U) (timeRows D U))
    (scalarRows (approximationReal D) (approximationCauchy D) V)

theorem remainderRows_pin (D : PositiveTime) (U V : seminorm.Cauchy) (n : Nat) :
    rowPoint (remainderRows D U V) n=
      BF4ExactSlabThermodynamicGraphMeshDerivative.remainder
        (approximation D n).depth (approximation D n).steps (point U) (point V) := by
  unfold remainderRows
  rw [differenceRows_pin,differenceRows_pin,constantRows_pin,timeRows_pin,scalarRows_pin,action_embed]
  rfl

theorem remainderRows_limit (D : PositiveTime) (U V : seminorm.Cauchy) :
    rowLimit (remainderRows D U V)=remainder D (point U) (point V) := by
  unfold remainderRows
  rw [rowLimit_difference,rowLimit_difference,rowLimit_constant,scalarRows_limit,
    completedRealSmul_congr _ _ _ D.cauchy (approximationReal_equiv D)]
  rfl

def radius (U V : seminorm.Cauchy) (epsilon : Q') : Q' :=
  HalfPow.half*BF4ExactSlabThermodynamicGraphMeshDerivative.radius U V epsilon

theorem radius_positive (U V : seminorm.Cauchy) (epsilon : Q') : (0 : Q')<radius U V epsilon :=
  ExpNeg.half_mul_pos _ (BF4ExactSlabThermodynamicGraphMeshDerivative.radius_positive U V epsilon)

/-- Actual differentiation of the original time action at EVERY original graph point. -/
theorem real_taylor_bound (U V : seminorm.Cauchy)
    (hgraph : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) (D : PositiveTime)
    (ht : RCle (realValue (timeValue D)) (rat (radius U V epsilon))) :
    RCle (B (remainder D (point U) (point V)) (remainder D (point U) (point V)))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon)) := by
  have htime : Quotient.mk crealSetoid (approximationReal D)=realValue (timeValue D) :=
    Quotient.sound (approximationReal_equiv D)
  have hap : RCle (Quotient.mk crealSetoid (approximationReal D)) (rat (radius U V epsilon)) := by
    rw [htime]
    exact ht
  change leEv (approximationReal D) (ofQ' (radius U V epsilon)) at hap
  obtain ⟨N,hN⟩ := hap (radius U V epsilon) (radius_positive U V epsilon)
  have hsmall (n : Nat) (hn : N≤n) :
      value (approximation D n)≤BF4ExactSlabThermodynamicGraphMeshDerivative.radius U V epsilon :=
    Q'.le_trans' _ _ _ (hN n hn)
      (Q'.le_of_eqv (ExpNeg.two_halves (BF4ExactSlabThermodynamicGraphMeshDerivative.radius U V epsilon)))
  let R := remainderRows D U V
  have hright : ConvergesTo
      (fun n => CReal.mul (CReal.mul (ofQ' (value (approximation D n))) (ofQ' (value (approximation D n)))) (ofQ' epsilon))
      (CReal.mul (CReal.mul (approximationReal D) (approximationReal D)) (ofQ' epsilon)) :=
    convergesTo_mul_general
      (convergesTo_mul_general (convergesTo_self (approximationReal D)) (convergesTo_self (approximationReal D)))
      (convergesTo_const _)
  have hb := limit_le_of_eventual (pairing_converges R R) hright N (by
    intro n hn
    change RCle (B (rowPoint R n) (rowPoint R n))
      (rat ((value (approximation D n)*value (approximation D n))*epsilon))
    rw [show R=remainderRows D U V from rfl,remainderRows_pin]
    exact BF4ExactSlabThermodynamicGraphMeshDerivative.mesh_taylor_bound U V hgraph epsilon he
      (approximation D n).depth (approximation D n).steps (hsmall n hn))
  change RCle (B (rowLimit R) (rowLimit R))
    (RCmul (RCmul (Quotient.mk crealSetoid (approximationReal D))
      (Quotient.mk crealSetoid (approximationReal D))) (rat epsilon)) at hb
  rw [show R=remainderRows D U V from rfl,remainderRows_limit,htime] at hb
  exact hb

/-- The radius is data computed from the original state AND image representatives. -/
def realTaylorCertificate (U V : seminorm.Cauchy)
    (hgraph : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' r : Q', ((0 : Q')<r) ×'
      (∀ D : PositiveTime,RCle (realValue (timeValue D)) (rat r) →
        RCle (B (remainder D (point U) (point V)) (remainder D (point U) (point V)))
          (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon))) :=
  ⟨radius U V epsilon,radius_positive U V epsilon,real_taylor_bound U V hgraph epsilon he⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.remainder
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.remainderRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.remainderRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.remainderRows_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.radius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.radius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.real_taylor_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative.realTaylorCertificate
