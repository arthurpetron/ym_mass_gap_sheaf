/-
# Original time increments on the entire closed derivative graph

For every ORIGINAL graph point (u,v), J u=T2 v, and every supplied
positive real time t, prove ||u-A_t u||^2 <= t^2 ||v||^2.
The image-norm estimate on the old dense domain passes through the
constructed two-coordinate graph rows. Finite-mesh actions preserve
the original Cauchy-row modulus by contraction. The existing time rows
then give the real-time bound, retaining the actual time coefficient.

There is no preimage convergence assumption and no new time action.
The consumer is the full-graph Taylor estimate: small graph-image error
now controls the time increment uniformly as t tends to zero.
This module does NOT yet prove that Taylor estimate or a physical
Hamiltonian identification. Fixed SU(2), nome 1/1024, fixed spacing and
T2-time units; physical scaling, continuum and all-group Clay stay open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit (representativeInner)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator (operator_constant)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (time_distance_contraction)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (action_embed)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound (mesh_increment_image_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows (pairing_converges)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal (convergesTo_mul_general)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X

/-- The actual mesh action preserves the supplied row modulus. -/
def meshRows (depth steps : Nat) (R : CauchyRows) : CauchyRows where
  row := fun n => timeRepresentative depth steps (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist (point (timeRepresentative depth steps (R.row m)))
      (point (timeRepresentative depth steps (R.row n)))) _
    rw [timeRepresentative_pin,timeRepresentative_pin]
    exact RCle_trans (time_distance_contraction depth steps _ _) (R.isCauchy epsilon he m n hm hn)

theorem meshRows_pin (depth steps : Nat) (R : CauchyRows) (n : Nat) :
    rowPoint (meshRows depth steps R) n=time depth steps (rowPoint R n) :=
  timeRepresentative_pin depth steps (R.row n)

theorem meshRows_limit (depth steps : Nat) (R : CauchyRows) :
    rowLimit (meshRows depth steps R)=time depth steps (rowLimit R) := by
  apply rowLimit_eq_of_bound _ _ (rowLimitRate R)
  intro epsilon he n hn
  rw [meshRows_pin]
  exact RCle_trans (time_distance_contraction depth steps _ _) (rowLimit_bound R epsilon he n hn)

theorem graph_mesh_increment_bound (depth steps : Nat) (u v : Completion)
    (h : derivativeAction u=twoStepTransfer v) :
    RCle (completedDist u (time depth steps u))
      (RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (B v v)) := by
  revert h
  refine Quotient.inductionOn₂ u v ?_
  intro U V h
  let R := differenceRows (stateRows U V) (meshRows depth steps (stateRows U V))
  let S := operatorRows [value ⟨depth,steps⟩] (imageRows U V h)
  have hr : ∀ n,RCle (B (rowPoint R n) (rowPoint R n)) (B (rowPoint S n) (rowPoint S n)) := by
    intro n
    dsimp only [R,S]
    rw [differenceRows_pin,meshRows_pin,operatorRows_pin,operator_constant,smul_norm,
      stateRows_pin,imageRows_pin]
    exact mesh_increment_image_bound depth steps (point (preimage U V (HalfPow.half^n)))
  have hb := rowLimit_pairing_le R R S S hr
  dsimp only [R,S] at hb
  rw [rowLimit_difference,meshRows_limit,stateRows_limit,operator_rowLimit,
    imageRows_limit,operator_constant,smul_norm] at hb
  exact hb

theorem GraphPoint.mesh_increment_bound (p : GraphPoint) (depth steps : Nat) :
    RCle (completedDist p.state (time depth steps p.state))
      (RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (B p.image p.image)) :=
  graph_mesh_increment_bound depth steps p.state p.image p.equation

/-- Every supplied positive real increment, with the SAME old action and time value. -/
theorem graph_real_increment_bound (D : PositiveTime) (u v : Completion)
    (h : derivativeAction u=twoStepTransfer v) :
    RCle (completedDist u (realTimeAction (timeValue D) u))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (B v v)) := by
  revert h
  refine Quotient.inductionOn₂ u v ?_
  intro U V h
  let R := differenceRows (constantRows U) (timeRows D U)
  have hright : ConvergesTo
      (fun n => CReal.mul (CReal.mul (ofQ' (value (approximation D n))) (ofQ' (value (approximation D n))))
        (representativeInner V V))
      (CReal.mul (CReal.mul (approximationReal D) (approximationReal D)) (representativeInner V V)) :=
    convergesTo_mul_general
      (convergesTo_mul_general (convergesTo_self (approximationReal D)) (convergesTo_self (approximationReal D)))
      (convergesTo_const _)
  have hb := leEv_of_convergesTo_le (pairing_converges R R) hright (by
    intro n
    change RCle (B (rowPoint R n) (rowPoint R n))
      (RCscale (value (approximation D n)*value (approximation D n)) (B (point V) (point V)))
    dsimp only [R]
    rw [differenceRows_pin,constantRows_pin,timeRows_pin,action_embed]
    exact graph_mesh_increment_bound (approximation D n).depth (approximation D n).steps (point U) (point V) h)
  change RCle (B (rowLimit R) (rowLimit R))
    (RCmul (RCmul (Quotient.mk crealSetoid (approximationReal D))
      (Quotient.mk crealSetoid (approximationReal D))) (B (point V) (point V))) at hb
  have htime : Quotient.mk crealSetoid (approximationReal D)=realValue (timeValue D) :=
    Quotient.sound (approximationReal_equiv D)
  dsimp only [R] at hb
  rw [rowLimit_difference,rowLimit_constant,htime] at hb
  exact hb

theorem GraphPoint.real_increment_bound (p : GraphPoint) (D : PositiveTime) :
    RCle (completedDist p.state (realTimeAction (timeValue D) p.state))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (B p.image p.image)) :=
  graph_real_increment_bound D p.state p.image p.equation

end YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound.meshRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound.meshRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound.meshRows_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound.graph_mesh_increment_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound.GraphPoint.mesh_increment_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound.graph_real_increment_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound.GraphPoint.real_increment_bound
