/-
# The concrete two-step transfer operator on the completed strict OS carrier

The one-step carrier has a genuine parity obstruction, but the even-time
subsemigroup already supplies a physical transfer operator with time spacing
`2a`.  This file names its first step `S = T^2` and collects only properties
that have now been proved on the actual completed carrier: rational linearity,
self-adjointness, positivity, norm contraction, vacuum stationarity, and
vacuum-complement invariance.

The strict `rho < 1` bound on the vacuum complement remains separate.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveTimeTranslation
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionLinearTimeTranslation

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedEvenTimeInterval
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTimeSelfAdjoint
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionLinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- The first physical step of the even subsemigroup, corresponding to
Euclidean time spacing `2a`. -/
def strictJointCylinderCompletedTwoStepTransfer
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointCylinderOSCompletion hcoupling hle ->
      StrictJointCylinderOSCompletion hcoupling hle :=
  strictJointCylinderCompletedTimeTranslate hcoupling hle (1 + 1)

theorem strictJointCylinderCompletedTwoStepTransfer_add
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepTransfer hcoupling hle
        (strictJointCylinderCompletedAdd hcoupling hle left right) =
      strictJointCylinderCompletedAdd hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle left)
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle right) :=
  strictJointCylinderCompletedTimeTranslate_additive
    hcoupling hle (1 + 1) left right

theorem strictJointCylinderCompletedTwoStepTransfer_smul
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q')
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepTransfer hcoupling hle
        (strictJointCylinderCompletedSmul hcoupling hle scalar vector) =
      strictJointCylinderCompletedSmul hcoupling hle scalar
        (strictJointCylinderCompletedTwoStepTransfer
          hcoupling hle vector) :=
  strictJointCylinderCompletedTimeTranslate_smul
    hcoupling hle (1 + 1) scalar vector

theorem strictJointCylinderCompletedTwoStepTransfer_self_adjoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer
          hcoupling hle left) right =
      strictJointCylinderCompletedInner hcoupling hle left
        (strictJointCylinderCompletedTwoStepTransfer
          hcoupling hle right) :=
  strictJointCylinderCompletedEvenTimeTranslate_self_adjoint
    hcoupling hle 1 left right

theorem strictJointCylinderCompletedTwoStepTransfer_positive
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCnonneg
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer
          hcoupling hle vector) vector) :=
  strictJointCylinderCompletedEvenTimeTransferForm_nonneg
    hcoupling hle 1 vector

theorem strictJointCylinderCompletedTwoStepTransfer_form_le_identity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer
          hcoupling hle vector) vector)
      (strictJointCylinderCompletedInner hcoupling hle vector vector) :=
  strictJointCylinderCompletedEvenTimeTransferForm_le_identity
    hcoupling hle 1 vector

theorem strictJointCylinderCompletedTwoStepTransfer_normSq_le
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector)
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector))
      (strictJointCylinderCompletedInner hcoupling hle vector vector) :=
  strictJointCylinderCompletedEvenTimeTranslate_normSq_le
    hcoupling hle 1 vector

theorem strictJointCylinderCompletedTwoStepTransfer_vacuum
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    strictJointCylinderCompletedTwoStepTransfer hcoupling hle
        (strictJointCylinderCompletionVacuum hcoupling hle) =
      strictJointCylinderCompletionVacuum hcoupling hle :=
  strictJointCylinderCompletedTimeTranslate_vacuum hcoupling hle (1 + 1)

theorem strictJointCylinderCompletedTwoStepTransfer_preserves_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    StrictJointCylinderCompletionVacuumOrthogonal hcoupling hle
      (strictJointCylinderCompletedTwoStepTransfer
        hcoupling hle vector) :=
  strictJointCylinderCompletedEvenTimeTranslate_preserves_vacuumOrthogonal
    hcoupling hle 1 vector horthogonal

/-- The one remaining transfer-matrix estimate, stated on the exact completed
operator and its exact invariant vacuum complement. -/
def StrictJointCylinderCompletedTwoStepVacuumFormGap
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) (separator : Q') : Prop :=
  (0 : Q') <= separator ∧ separator < (1 : Q') ∧
    forall vector : StrictJointCylinderOSCompletion hcoupling hle,
      StrictJointCylinderCompletionVacuumOrthogonal hcoupling hle vector ->
        CReal.RCle
          (strictJointCylinderCompletedInner hcoupling hle
            (strictJointCylinderCompletedTwoStepTransfer
              hcoupling hle vector) vector)
          (CReal.RCscale separator
            (strictJointCylinderCompletedInner hcoupling hle vector vector))

#print axioms strictJointCylinderCompletedTwoStepTransfer
#print axioms strictJointCylinderCompletedTwoStepTransfer_add
#print axioms strictJointCylinderCompletedTwoStepTransfer_smul
#print axioms strictJointCylinderCompletedTwoStepTransfer_self_adjoint
#print axioms strictJointCylinderCompletedTwoStepTransfer_positive
#print axioms strictJointCylinderCompletedTwoStepTransfer_form_le_identity
#print axioms strictJointCylinderCompletedTwoStepTransfer_normSq_le
#print axioms strictJointCylinderCompletedTwoStepTransfer_vacuum
#print axioms strictJointCylinderCompletedTwoStepTransfer_preserves_vacuumOrthogonal
#print axioms StrictJointCylinderCompletedTwoStepVacuumFormGap

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
