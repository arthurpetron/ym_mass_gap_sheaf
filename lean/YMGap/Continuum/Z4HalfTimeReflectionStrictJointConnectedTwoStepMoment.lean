/-
# The connected dense form is the completed same-object two-step moment

The geometric cluster expansion controls a connected two-block covariance,
whereas the OS transfer construction naturally presents an uncentered mixed
matrix coefficient.  This file isolates that algebraic difference on the
literal strict-cylinder carrier.

For a source vector `v` and doubled-time separation `2 * shift`, the connected
form is

  `B(source, target) - B(source, vacuum) * B(vacuum, target)`.

On the dense vacuum complement both one-point factors vanish.  The connected
form is therefore exactly the mixed OS bilinear.  After embedding the same
dense vector into the choice-free completion, it is also exactly the concrete
completed autocorrelation `<S^shift v, v>`, where `S = T^2`.

This is the same-object algebraic bridge.  It does not yet identify the
connected form with the thermodynamic limit of the arbitrary-cutoff geometric
covariance, and it asserts no uniform strict contraction or continuum gap.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The literal connected form -/

/-- The lower-block one-point function in the common doubled-time box. -/
def strictJointDoubledTimeLowerMean
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle
    (strictJointDoubledTimeMixedSource shift vector)
    (strictJointCylinderVacuum (base + (shift + shift)))

/-- The upper-block one-point function in the common doubled-time box. -/
def strictJointDoubledTimeUpperMean
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle
    (strictJointCylinderVacuum (base + (shift + shift)))
    (strictJointDoubledTimeMixedTarget shift vector)

/-- The unshifted vacuum coefficient of a strict cylinder.  This is the one
constructive real whose rational approximants can be used to center the
literal rational-linear carrier. -/
def strictJointVacuumMean
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle vector
    (strictJointCylinderVacuum base)

/-- Canonical box enlargement does not change the lower one-point function. -/
theorem strictJointDoubledTimeLowerMean_equiv_vacuumMean
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointDoubledTimeLowerMean hcoupling hle shift vector)
      (strictJointVacuumMean hcoupling hle vector) := by
  have htransport :=
    boxTransportStrictJointCylinderVector_reflectionBilinear_equiv
      hcoupling hle (shift + shift) vector
      (strictJointCylinderVacuum base)
  rw [boxTransportStrictJointCylinderVacuum] at htransport
  simpa only [strictJointDoubledTimeLowerMean,
    strictJointDoubledTimeMixedSource, strictJointVacuumMean] using htransport

/-- Even-time covariance and vacuum stationarity identify the upper
one-point function with the same unshifted vacuum coefficient. -/
theorem strictJointDoubledTimeUpperMean_equiv_vacuumMean
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointDoubledTimeUpperMean hcoupling hle shift vector)
      (strictJointVacuumMean hcoupling hle vector) := by
  let vacuum := strictJointCylinderVacuum base
  have hcovariance := strictJointEvenOneSidedTimeCovariance_derived
    hcoupling hle shift vacuum vector
  change CReal.Equiv
    (strictJointCylinderReflectionBilinear hcoupling hle
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base (shift + shift)) vacuum)
      (timeTranslateStrictJointCylinderVector (shift + shift) vector))
    (strictJointCylinderReflectionBilinear hcoupling hle
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base (shift + shift)) vector)
      (timeTranslateStrictJointCylinderVector (shift + shift) vacuum))
      at hcovariance
  rw [boxTransportStrictJointCylinderVacuum,
    timeTranslateStrictJointCylinderVacuum] at hcovariance
  have htransport :=
    boxTransportStrictJointCylinderVector_reflectionBilinear_equiv
      hcoupling hle (shift + shift) vector vacuum
  rw [boxTransportStrictJointCylinderVacuum] at htransport
  exact CReal.Equiv.trans hcovariance htransport

/-- The connected doubled-time form whose finite-volume approximants are the
signed two-block covariances controlled by the geometric cluster expansion. -/
def strictJointDoubledTimeConnectedForm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  CReal.sub
    (strictJointDoubledTimeMixedOSBilinear hcoupling hle shift vector)
    (CReal.mul
      (strictJointDoubledTimeLowerMean hcoupling hle shift vector)
      (strictJointDoubledTimeUpperMean hcoupling hle shift vector))

private theorem creal_mul_equiv_zero_of_right
    (left right : CReal) (hright : CReal.Equiv right CReal.czero) :
    CReal.Equiv (CReal.mul left right) CReal.czero := by
  refine CReal.Equiv.trans
    ((CRealAlg.cmul_comm left right).trans
      (CReal.mul_congr_left hright)) ?_
  exact YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.zero_mul_eqv _)

private theorem creal_sub_equiv_left_of_right_zero
    (left right : CReal) (hright : CReal.Equiv right CReal.czero) :
    CReal.Equiv (CReal.sub left right) left := by
  unfold CReal.sub
  refine CReal.Equiv.trans
    (CReal.add_congr_right (CReal.neg_congr hright)) ?_
  exact YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun _ => by
      have hnegZero : (-(0 : Q')).eqv 0 := by decide
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ hnegZero)
        (Q'.eqv_of_eq (Q'.add_zero' _)))

/-! ## 2. Vacuum orthogonality removes the disconnected part -/

theorem strictJointDoubledTimeLowerMean_equiv_zero_of_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    CReal.Equiv
      (strictJointDoubledTimeLowerMean hcoupling hle shift vector)
      CReal.czero := by
  have htransport :=
    boxTransportStrictJointCylinderVector_reflectionBilinear_equiv
      hcoupling hle (shift + shift) vector
      (strictJointCylinderVacuum base)
  rw [boxTransportStrictJointCylinderVacuum] at htransport
  exact CReal.Equiv.trans htransport horthogonal

theorem strictJointDoubledTimeUpperMean_equiv_zero_of_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    CReal.Equiv
      (strictJointDoubledTimeUpperMean hcoupling hle shift vector)
      CReal.czero := by
  have htarget := evenTimeTranslate_preserves_vacuumOrthogonal
    hcoupling hle shift vector horthogonal
  have hsymmetry := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle
    (strictJointCylinderVacuum (base + (shift + shift)))
    (strictJointDoubledTimeMixedTarget shift vector)
  exact CReal.Equiv.trans hsymmetry htarget

/-- On the dense vacuum complement the connected covariance is exactly the
uncentered mixed OS matrix coefficient. -/
theorem strictJointDoubledTimeConnectedForm_equiv_OSBilinear_of_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    CReal.Equiv
      (strictJointDoubledTimeConnectedForm hcoupling hle shift vector)
      (strictJointDoubledTimeMixedOSBilinear
        hcoupling hle shift vector) := by
  apply creal_sub_equiv_left_of_right_zero
  exact creal_mul_equiv_zero_of_right _ _
    (strictJointDoubledTimeUpperMean_equiv_zero_of_vacuumOrthogonal
      hcoupling hle shift vector horthogonal)

/-! ## 3. Exact descent to the completed same-object autocorrelation -/

/-- Completed time translation acts on a dense constant representative by
the literal staged time translation. -/
theorem strictJointCylinderCompletedTimeTranslate_embedRep
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (shift : Nat) (stage : StrictJointCylinderStage) :
    strictJointCylinderCompletedTimeTranslate hcoupling hle shift
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep stage) =
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (stage.timeTranslate shift) := by
  rfl

/-- The completed same-object two-step moment of a dense vector is represented
by the literal mixed OS bilinear at the same separation. -/
theorem strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderCompletedTwoStepAutocorrelation hcoupling hle
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
          (StrictJointCylinderStage.mk base vector)) shift =
      Quotient.mk CReal.crealSetoid
        (strictJointDoubledTimeMixedOSBilinear
          hcoupling hle shift vector) := by
  unfold strictJointCylinderCompletedTwoStepAutocorrelation
    strictJointCylinderCompletedTwoStepPower
  rw [strictJointCylinderCompletedTimeTranslate_embedRep,
    strictJointCylinderCompletedInner_embedRep]
  apply Quotient.sound
  let sourceStage : StrictJointCylinderStage :=
    StrictJointCylinderStage.mk base vector
  let targetStage := sourceStage.timeTranslate (shift + shift)
  have hstage := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle targetStage sourceStage
    (Nat.le_refl (base + (shift + shift)))
    (Nat.le_add_right base (shift + shift))
  have hstageClean : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (strictJointDoubledTimeMixedTarget shift vector)
        (strictJointDoubledTimeMixedSource shift vector))
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle targetStage sourceStage) := by
    simpa only [sourceStage, targetStage,
      StrictJointCylinderStage.timeTranslate,
      strictJointDoubledTimeMixedSource,
      strictJointDoubledTimeMixedTarget,
      boxTransportStrictJointCylinderVector_refl] using hstage
  have hsymmetry := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle
    (strictJointDoubledTimeMixedSource shift vector)
    (strictJointDoubledTimeMixedTarget shift vector)
  exact CReal.Equiv.trans
    (CReal.Equiv.symm hstageClean)
    (CReal.Equiv.symm hsymmetry)

/-- Terminal same-object bridge on the dense vacuum complement: the connected
form and the completed autocorrelation determine the same quotient real. -/
theorem strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    strictJointCylinderCompletedTwoStepAutocorrelation hcoupling hle
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
          (StrictJointCylinderStage.mk base vector)) shift =
      Quotient.mk CReal.crealSetoid
        (strictJointDoubledTimeConnectedForm
          hcoupling hle shift vector) := by
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS]
  apply Quotient.sound
  exact CReal.Equiv.symm
    (strictJointDoubledTimeConnectedForm_equiv_OSBilinear_of_vacuumOrthogonal
      hcoupling hle shift vector horthogonal)

#print axioms strictJointDoubledTimeLowerMean_equiv_zero_of_vacuumOrthogonal
#print axioms strictJointDoubledTimeUpperMean_equiv_zero_of_vacuumOrthogonal
#print axioms strictJointDoubledTimeLowerMean_equiv_vacuumMean
#print axioms strictJointDoubledTimeUpperMean_equiv_vacuumMean
#print axioms strictJointDoubledTimeConnectedForm_equiv_OSBilinear_of_vacuumOrthogonal
#print axioms strictJointCylinderCompletedTimeTranslate_embedRep
#print axioms strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
#print axioms strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_connected

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
