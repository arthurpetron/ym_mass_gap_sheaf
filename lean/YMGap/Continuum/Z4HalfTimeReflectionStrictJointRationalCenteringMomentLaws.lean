/-
# Rational centering transfers raw Gram laws to connected moments

The strict-cylinder carrier is only rational-linear, while its vacuum
coefficient is a constructive real.  Consequently exact subtraction of the
vacuum coefficient need not remain in the dense carrier.  This file uses the
canonical rational approximants of that coefficient instead.

For a strict cylinder `v`, stage `k` uses the literal carrier element

  `v - (vacuumMean v).approx k * vacuum`.

Its completed two-step autocorrelations obey positivity, contraction to time
zero, and dyadic log-convexity.  Bilinearity, vacuum stationarity, and
`CReal.convergesTo_self` identify their limits with the already-constructed
thermodynamic central connected moments of `v`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredDyadicGap
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointRationalCenteringMomentLaws

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredDyadicGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem creal_mul_congr_right
    {left right scalar : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

private theorem creal_mul_czero (value : CReal) :
    CReal.Equiv (CReal.mul value CReal.czero) CReal.czero :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_zero_eqv (value.approx n))

private theorem creal_add_czero (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (value.approx n)))

/-- The legal rational-linear centering of a strict cylinder at approximation
stage `stage`. -/
def strictJointRationalCenteredVector
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (stage : Nat) : StrictJointCylinderVector base :=
  vector.add ((strictJointCylinderVacuum base).smul
    (-(strictJointVacuumMean hcoupling hle vector).approx stage))

/-- The raw mixed two-step moment of the rationally centered presentation. -/
def strictJointRationalCenteredMixedMoment
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift stage : Nat) : CReal :=
  strictJointDoubledTimeMixedOSBilinear hcoupling hle shift
    (strictJointRationalCenteredVector hcoupling hle vector stage)

/-- The explicit scalar polynomial produced by expanding the rationally
centered mixed moment. -/
def strictJointRationalCenteringExpansion
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift stage : Nat) : CReal :=
  let scalar := -(strictJointVacuumMean hcoupling hle vector).approx stage
  CReal.add
    (CReal.add
      (strictJointDoubledTimeMixedOSBilinear hcoupling hle shift vector)
      (CReal.mul (CReal.ofQ' scalar)
        (strictJointDoubledTimeLowerMean hcoupling hle shift vector)))
    (CReal.mul (CReal.ofQ' scalar)
      (CReal.add
        (strictJointDoubledTimeUpperMean hcoupling hle shift vector)
        (CReal.mul (CReal.ofQ' scalar) CReal.cone)))

/-- The explicit four-term bilinear expansion of one rationally centered
mixed moment.  Both one-point coefficients and the unit vacuum term remain
visible so the subsequent limit proof does not hide any scalar extension. -/
theorem strictJointRationalCenteredMixedMoment_equiv_expansion
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift stage : Nat) :
    CReal.Equiv
      (strictJointRationalCenteredMixedMoment
        hcoupling hle vector shift stage)
      (strictJointRationalCenteringExpansion
        hcoupling hle vector shift stage) := by
  let scalar := -(strictJointVacuumMean hcoupling hle vector).approx stage
  let source := strictJointDoubledTimeMixedSource shift vector
  let target := strictJointDoubledTimeMixedTarget shift vector
  let vacuum := strictJointCylinderVacuum (base + (shift + shift))
  have hsource :
      strictJointDoubledTimeMixedSource shift
          (strictJointRationalCenteredVector hcoupling hle vector stage) =
        source.add (vacuum.smul scalar) := by
    unfold strictJointRationalCenteredVector
      strictJointDoubledTimeMixedSource source vacuum scalar
    rw [boxTransportStrictJointCylinderVector_add,
      boxTransportStrictJointCylinderVector_smul,
      boxTransportStrictJointCylinderVacuum]
    rfl
  have htarget :
      strictJointDoubledTimeMixedTarget shift
          (strictJointRationalCenteredVector hcoupling hle vector stage) =
        target.add (vacuum.smul scalar) := by
    unfold strictJointRationalCenteredVector
      strictJointDoubledTimeMixedTarget target vacuum scalar
    rw [timeTranslateStrictJointCylinderVector_add,
      timeTranslateStrictJointCylinderVector_smul,
      timeTranslateStrictJointCylinderVacuum]
    rfl
  have hvacuum : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle vacuum vacuum)
      CReal.cone :=
    CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_self
        hcoupling hle vacuum)
      (strictJointCylinderVacuum_reflectionQuadratic_equiv_cone
        hcoupling hle (base + (shift + shift)))
  have hfirst : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle source
        (target.add (vacuum.smul scalar)))
      (CReal.add
        (strictJointDoubledTimeMixedOSBilinear
          hcoupling hle shift vector)
        (CReal.mul (CReal.ofQ' scalar)
          (strictJointDoubledTimeLowerMean
            hcoupling hle shift vector))) := by
    refine CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_add_right
        hcoupling hle source target (vacuum.smul scalar)) ?_
    apply CReal.add_congr_right
    exact strictJointCylinderReflectionBilinear_smul_right
      hcoupling hle scalar source vacuum
  have hvacuumScaled : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle vacuum
        (vacuum.smul scalar))
      (CReal.mul (CReal.ofQ' scalar) CReal.cone) :=
    CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_smul_right
        hcoupling hle scalar vacuum vacuum)
      (creal_mul_congr_right hvacuum)
  have hinside : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle vacuum
        (target.add (vacuum.smul scalar)))
      (CReal.add
        (strictJointDoubledTimeUpperMean hcoupling hle shift vector)
        (CReal.mul (CReal.ofQ' scalar) CReal.cone)) := by
    refine CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_add_right
        hcoupling hle vacuum target (vacuum.smul scalar)) ?_
    exact CReal.add_congr_right hvacuumScaled
  have hsecond : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (vacuum.smul scalar) (target.add (vacuum.smul scalar)))
      (CReal.mul (CReal.ofQ' scalar)
        (CReal.add
          (strictJointDoubledTimeUpperMean hcoupling hle shift vector)
          (CReal.mul (CReal.ofQ' scalar) CReal.cone))) :=
    CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_smul_left
        hcoupling hle scalar vacuum (target.add (vacuum.smul scalar)))
      (creal_mul_congr_right hinside)
  unfold strictJointRationalCenteredMixedMoment
    strictJointRationalCenteringExpansion
    strictJointDoubledTimeMixedOSBilinear
  rw [hsource, htarget]
  exact CReal.Equiv.trans
    (strictJointCylinderReflectionBilinear_add_left
      hcoupling hle source (vacuum.smul scalar)
        (target.add (vacuum.smul scalar)))
    (CReal.Equiv.trans
      (CReal.add_congr_left hfirst)
      (CReal.add_congr_right hsecond))

private theorem creal_rational_centering_limit_algebra
    (mixed mean : CReal) :
    CReal.Equiv
      (CReal.add
        (CReal.add mixed
          (CReal.mul (CReal.neg mean) mean))
        (CReal.mul (CReal.neg mean)
          (CReal.add mean
            (CReal.mul (CReal.neg mean) CReal.cone))))
      (CReal.sub mixed (CReal.mul mean mean)) := by
  have hinside : CReal.Equiv
      (CReal.add mean (CReal.mul (CReal.neg mean) CReal.cone))
      CReal.czero :=
    CReal.Equiv.trans
      (CReal.add_congr_right (CRealAlg.cmul_cone (CReal.neg mean)))
      (CReal.sub_self_eqv_zero mean)
  have hsecond : CReal.Equiv
      (CReal.mul (CReal.neg mean)
        (CReal.add mean (CReal.mul (CReal.neg mean) CReal.cone)))
      CReal.czero :=
    CReal.Equiv.trans (creal_mul_congr_right hinside)
      (creal_mul_czero (CReal.neg mean))
  refine CReal.Equiv.trans (CReal.add_congr_right hsecond) ?_
  refine CReal.Equiv.trans
    (creal_add_czero
      (CReal.add mixed (CReal.mul (CReal.neg mean) mean))) ?_
  unfold CReal.sub
  exact CReal.add_congr_right
    (YMGap.Constructive.TrigSignedAdd.neg_mul mean mean)

/-- The scalar expansion converges to the literal connected form.  The limit
uses only the canonical approximation sequence of the vacuum coefficient. -/
theorem strictJointRationalCenteringExpansion_converges_connected
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift : Nat) :
    CReal.ConvergesTo
      (fun stage => strictJointRationalCenteringExpansion
        hcoupling hle vector shift stage)
      (strictJointDoubledTimeConnectedForm
        hcoupling hle shift vector) := by
  let mean := strictJointVacuumMean hcoupling hle vector
  let mixed := strictJointDoubledTimeMixedOSBilinear
    hcoupling hle shift vector
  let lower := strictJointDoubledTimeLowerMean hcoupling hle shift vector
  let upper := strictJointDoubledTimeUpperMean hcoupling hle shift vector
  have hscalar : CReal.ConvergesTo
      (fun stage => CReal.ofQ' (-(mean.approx stage)))
      (CReal.neg mean) := by
    simpa only [CReal.ofQ'_neg] using
      (CReal.convergesTo_neg (CReal.convergesTo_self mean))
  have hlowerProduct := CReal.convergesTo_mul_general hscalar
    (CReal.convergesTo_const lower)
  have hvacuumProduct := CReal.convergesTo_mul_general hscalar
    (CReal.convergesTo_const CReal.cone)
  have hinside := CReal.convergesTo_add
    (CReal.convergesTo_const upper) hvacuumProduct
  have hupperProduct := CReal.convergesTo_mul_general hscalar hinside
  have hfirst := CReal.convergesTo_add
    (CReal.convergesTo_const mixed) hlowerProduct
  have hexpansion := CReal.convergesTo_add hfirst hupperProduct
  have hexpansionClean : CReal.ConvergesTo
      (fun stage => strictJointRationalCenteringExpansion
        hcoupling hle vector shift stage)
      (CReal.add
        (CReal.add mixed (CReal.mul (CReal.neg mean) lower))
        (CReal.mul (CReal.neg mean)
          (CReal.add upper
            (CReal.mul (CReal.neg mean) CReal.cone)))) := by
    simpa only [strictJointRationalCenteringExpansion,
      mean, mixed, lower, upper] using hexpansion
  have hlower := strictJointDoubledTimeLowerMean_equiv_vacuumMean
    hcoupling hle shift vector
  have hupper := strictJointDoubledTimeUpperMean_equiv_vacuumMean
    hcoupling hle shift vector
  have hfirstReplace : CReal.Equiv
      (CReal.add mixed (CReal.mul (CReal.neg mean) lower))
      (CReal.add mixed (CReal.mul (CReal.neg mean) mean)) :=
    CReal.add_congr_right (creal_mul_congr_right hlower)
  have hinsideReplace : CReal.Equiv
      (CReal.add upper
        (CReal.mul (CReal.neg mean) CReal.cone))
      (CReal.add mean
        (CReal.mul (CReal.neg mean) CReal.cone)) :=
    CReal.add_congr_left hupper
  have hlimitReplace : CReal.Equiv
      (CReal.add
        (CReal.add mixed (CReal.mul (CReal.neg mean) lower))
        (CReal.mul (CReal.neg mean)
          (CReal.add upper
            (CReal.mul (CReal.neg mean) CReal.cone))))
      (CReal.add
        (CReal.add mixed (CReal.mul (CReal.neg mean) mean))
        (CReal.mul (CReal.neg mean)
          (CReal.add mean
            (CReal.mul (CReal.neg mean) CReal.cone)))) :=
    CReal.Equiv.trans
      (CReal.add_congr_left hfirstReplace)
      (CReal.add_congr_right
        (creal_mul_congr_right hinsideReplace))
  have hmeanProduct : CReal.Equiv
      (CReal.mul lower upper) (CReal.mul mean mean) :=
    CReal.Equiv.trans (CReal.mul_congr_left hlower)
      (creal_mul_congr_right hupper)
  have hlimitConnected : CReal.Equiv
      (CReal.add
        (CReal.add mixed (CReal.mul (CReal.neg mean) lower))
        (CReal.mul (CReal.neg mean)
          (CReal.add upper
            (CReal.mul (CReal.neg mean) CReal.cone))))
      (strictJointDoubledTimeConnectedForm
        hcoupling hle shift vector) := by
    refine CReal.Equiv.trans hlimitReplace ?_
    refine CReal.Equiv.trans
      (creal_rational_centering_limit_algebra mixed mean) ?_
    change CReal.Equiv
      (CReal.sub mixed (CReal.mul mean mean))
      (CReal.sub mixed (CReal.mul lower upper))
    exact CReal.Equiv.symm (CReal.sub_congr_right hmeanProduct)
  exact CReal.convergesTo_limit_congr
    hexpansionClean hlimitConnected

/-- The literal mixed moments of the rationally centered carrier vectors
converge to the thermodynamic central connected moment of the original
vector. -/
theorem strictJointRationalCenteredMixedMoment_converges_central
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift : Nat) :
    CReal.ConvergesTo
      (fun stage => strictJointRationalCenteredMixedMoment
        hcoupling hle vector shift stage)
      (strictJointDenseCentralMoment hcoupling hle vector shift) := by
  have hconnected := strictJointRationalCenteringExpansion_converges_connected
    hcoupling hle vector shift
  have hcentral : CReal.ConvergesTo
      (fun stage => strictJointRationalCenteringExpansion
        hcoupling hle vector shift stage)
      (strictJointDenseCentralMoment hcoupling hle vector shift) :=
    CReal.convergesTo_limit_congr hconnected
      (CReal.Equiv.symm
        (orientedDoubledTimeCentralConnectedLimit_equiv_connected
          hcoupling hle shift vector))
  exact YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (fun stage => CReal.Equiv.symm
      (strictJointRationalCenteredMixedMoment_equiv_expansion
        hcoupling hle vector shift stage)) hcentral

/-! ## Raw Gram laws at every rational-centering stage -/

theorem strictJointRationalCenteredMixedMoment_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift stage : Nat) :
    CReal.leEv CReal.czero
      (strictJointRationalCenteredMixedMoment
        hcoupling hle vector shift stage) := by
  let centered := strictJointRationalCenteredVector
    hcoupling hle vector stage
  have h := strictJointCylinderCompletedTwoStepAutocorrelation_nonnegative
    hcoupling hle
    ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
      (StrictJointCylinderStage.mk base centered)) shift
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
    hcoupling hle shift centered] at h
  exact h

theorem strictJointRationalCenteredMixedMoment_le_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift stage : Nat) :
    CReal.leEv
      (strictJointRationalCenteredMixedMoment
        hcoupling hle vector shift stage)
      (strictJointRationalCenteredMixedMoment
        hcoupling hle vector 0 stage) := by
  let centered := strictJointRationalCenteredVector
    hcoupling hle vector stage
  have h := strictJointCylinderCompletedTwoStepAutocorrelation_le_zero
    hcoupling hle
    ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
      (StrictJointCylinderStage.mk base centered)) shift
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
      hcoupling hle shift centered,
    strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
      hcoupling hle 0 centered] at h
  exact h

theorem strictJointRationalCenteredMixedMoment_dyadic
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift stage : Nat) :
    CReal.leEv
      (CReal.mul
        (strictJointRationalCenteredMixedMoment
          hcoupling hle vector shift stage)
        (strictJointRationalCenteredMixedMoment
          hcoupling hle vector shift stage))
      (CReal.mul
        (strictJointRationalCenteredMixedMoment
          hcoupling hle vector (shift + shift) stage)
        (strictJointRationalCenteredMixedMoment
          hcoupling hle vector 0 stage)) := by
  let centered := strictJointRationalCenteredVector
    hcoupling hle vector stage
  have h := strictJointCylinderCompletedTwoStepAutocorrelation_dyadic
    hcoupling hle
    ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
      (StrictJointCylinderStage.mk base centered)) shift
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
      hcoupling hle shift centered,
    strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
      hcoupling hle (shift + shift) centered,
    strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_mixedOS
      hcoupling hle 0 centered,
    CReal.RCmul_mk, CReal.RCmul_mk] at h
  exact h

/-! ## Contraction of the stagewise laws to central moments -/

/-- Rational centering proves all three centered moment laws for every strict
cylinder.  This discharges the scalar-safe dense moment-law frontier without
assuming exact dense vacuum-kernel closure. -/
def strictJointAllDenseCentralMomentLaws_holds
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointAllDenseCentralMomentLaws hcoupling hle := by
  intro base vector
  refine
    { nonnegative := ?_
      leZero := ?_
      dyadic := ?_ }
  · intro shift
    apply CReal.leEv_of_convergesTo_le
      (CReal.convergesTo_const CReal.czero)
      (strictJointRationalCenteredMixedMoment_converges_central
        hcoupling hle vector shift)
    intro stage
    exact strictJointRationalCenteredMixedMoment_nonnegative
      hcoupling hle vector shift stage
  · intro shift
    apply CReal.leEv_of_convergesTo_le
      (strictJointRationalCenteredMixedMoment_converges_central
        hcoupling hle vector shift)
      (strictJointRationalCenteredMixedMoment_converges_central
        hcoupling hle vector 0)
    intro stage
    exact strictJointRationalCenteredMixedMoment_le_zero
      hcoupling hle vector shift stage
  · intro shift
    apply CReal.leEv_of_convergesTo_le
      (CReal.convergesTo_mul_general
        (strictJointRationalCenteredMixedMoment_converges_central
          hcoupling hle vector shift)
        (strictJointRationalCenteredMixedMoment_converges_central
          hcoupling hle vector shift))
      (CReal.convergesTo_mul_general
        (strictJointRationalCenteredMixedMoment_converges_central
          hcoupling hle vector (shift + shift))
        (strictJointRationalCenteredMixedMoment_converges_central
          hcoupling hle vector 0))
    intro stage
    exact strictJointRationalCenteredMixedMoment_dyadic
      hcoupling hle vector shift stage

/-- The unconditional scalar-safe dense one-step form bound.  The common
factor is the already-proved geometric rate `1/16`; no exact rational vacuum
kernel hypothesis remains. -/
theorem strictJointDenseCentralMoment_le_rate
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) :
    CReal.leEv
      (strictJointDenseCentralMoment hcoupling hle vector 1)
      (CReal.mul (CReal.ofQ'
          YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering.anchorDecoratedDoubledTimeRate)
        (strictJointDenseCentralMoment hcoupling hle vector 0)) :=
  strictJointDenseCentralMoment_le_rate_of_laws
    hcoupling hle vector
    (strictJointAllDenseCentralMomentLaws_holds
      hcoupling hle base vector)

#print axioms strictJointRationalCenteredMixedMoment_equiv_expansion
#print axioms strictJointRationalCenteringExpansion_converges_connected
#print axioms strictJointRationalCenteredMixedMoment_converges_central
#print axioms strictJointRationalCenteredMixedMoment_nonnegative
#print axioms strictJointRationalCenteredMixedMoment_le_zero
#print axioms strictJointRationalCenteredMixedMoment_dyadic
#print axioms strictJointAllDenseCentralMomentLaws_holds
#print axioms strictJointDenseCentralMoment_le_rate

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointRationalCenteringMomentLaws
