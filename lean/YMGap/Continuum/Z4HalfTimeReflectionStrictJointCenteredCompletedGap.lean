/-
# The centered dense gap passes to the full completed vacuum complement

Rational centering gives the uniform `1/16` estimate for the thermodynamic
central moments of every strict cylinder.  An arbitrary Cauchy representative
of a completed vacuum-orthogonal vector need not have vacuum-orthogonal stages.
Instead, its stagewise vacuum coefficients converge to zero.  This file proves
that the stagewise central moments therefore converge to the raw completed
two-step form, and passes the dense centered estimate through that limit.

No exact dense-kernel replacement and no real scalar action on the carrier is
used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointRationalCenteringMomentLaws

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredCompletedGap

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRationalCenteringMomentLaws
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

private theorem creal_neg_czero :
    CReal.Equiv (CReal.neg CReal.czero) CReal.czero :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun _ => by
      change (-(0 : Q')).eqv 0
      decide)

private theorem creal_add_czero (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (value.approx n)))

/-! ## Stagewise identifications -/

/-- A stage's unshifted vacuum mean is the same constructive real as its
pairing with the canonical staged vacuum. -/
theorem strictJointStageVacuumMean_equiv_pairing
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointVacuumMean hcoupling hle stage.vector)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle stage strictJointCylinderVacuumStage) := by
  have hstage := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle stage strictJointCylinderVacuumStage
      (Nat.le_refl stage.base) (Nat.zero_le stage.base)
  simpa only [strictJointVacuumMean, strictJointCylinderVacuumStage,
    boxTransportStrictJointCylinderVector_refl,
    boxTransportStrictJointCylinderVacuum] using hstage

/-- The staged `2 * shift` pairing is the literal dense mixed OS moment of
the stage's cylinder vector. -/
theorem strictJointStageTwoStepPairing_equiv_mixedOS
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (stage.timeTranslate (shift + shift)) stage)
      (strictJointDoubledTimeMixedOSBilinear
        hcoupling hle shift stage.vector) := by
  have hstage := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (stage.timeTranslate (shift + shift)) stage
      (Nat.le_refl (stage.base + (shift + shift)))
      (Nat.le_add_right stage.base (shift + shift))
  have hstageClean : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (strictJointDoubledTimeMixedTarget shift stage.vector)
        (strictJointDoubledTimeMixedSource shift stage.vector))
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (stage.timeTranslate (shift + shift)) stage) := by
    simpa only [StrictJointCylinderStage.timeTranslate,
      strictJointDoubledTimeMixedSource,
      strictJointDoubledTimeMixedTarget,
      boxTransportStrictJointCylinderVector_refl] using hstage
  have hsymmetry := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle
    (strictJointDoubledTimeMixedSource shift stage.vector)
    (strictJointDoubledTimeMixedTarget shift stage.vector)
  exact CReal.Equiv.trans (CReal.Equiv.symm hstageClean)
    (CReal.Equiv.symm hsymmetry)

/-! ## Central moments of one Cauchy representative -/

/-- The central moment sequence obtained by applying the thermodynamic dense
construction to each stage of one explicit completion representative. -/
def strictJointCauchyCentralMomentSeq
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (shift stage : Nat) : CReal :=
  strictJointDenseCentralMoment hcoupling hle (X.seq stage).vector shift

/-- The representative's pairing with the constant vacuum at each stage. -/
def strictJointCauchyVacuumPairingSeq
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (stage : Nat) : CReal :=
  cauchyPairingSeq hcoupling hle X
    ((strictJointCylinderStageSquaredSeminorm hcoupling hle).constant
      strictJointCylinderVacuumStage) stage

/-- The raw staged two-step pairing of a representative. -/
def strictJointCauchyTwoStepPairingSeq
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (shift stage : Nat) : CReal :=
  cauchyPairingSeq hcoupling hle
    ((strictJointCylinderStageTimeTranslateNonexpansive
      hcoupling hle (shift + shift)).mapCauchy X) X stage

/-- The staged vacuum-pairing sequence is exactly the stage vector's vacuum
mean, up to the constructive-real setoid. -/
theorem strictJointCauchyVacuumPairingSeq_equiv_mean
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (stage : Nat) :
    CReal.Equiv
      (strictJointCauchyVacuumPairingSeq hcoupling hle X stage)
      (strictJointVacuumMean hcoupling hle (X.seq stage).vector) := by
  exact CReal.Equiv.symm
    (strictJointStageVacuumMean_equiv_pairing
      hcoupling hle (X.seq stage))

/-- The raw Cauchy pairing term is the dense mixed OS moment of the same stage
vector. -/
theorem strictJointCauchyTwoStepPairingSeq_equiv_mixedOS
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (shift stage : Nat) :
    CReal.Equiv
      (strictJointCauchyTwoStepPairingSeq
        hcoupling hle X shift stage)
      (strictJointDoubledTimeMixedOSBilinear
        hcoupling hle shift (X.seq stage).vector) := by
  exact strictJointStageTwoStepPairing_equiv_mixedOS
    hcoupling hle shift (X.seq stage)

/-- Each dense central moment is the raw staged pairing minus the square of
the corresponding staged vacuum pairing. -/
theorem strictJointCauchyCentralMomentSeq_equiv_centeredPairing
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (shift stage : Nat) :
    CReal.Equiv
      (strictJointCauchyCentralMomentSeq hcoupling hle X shift stage)
      (CReal.sub
        (strictJointCauchyTwoStepPairingSeq
          hcoupling hle X shift stage)
        (CReal.mul
          (strictJointCauchyVacuumPairingSeq hcoupling hle X stage)
          (strictJointCauchyVacuumPairingSeq hcoupling hle X stage))) := by
  let vector := (X.seq stage).vector
  let mean := strictJointVacuumMean hcoupling hle vector
  let lower := strictJointDoubledTimeLowerMean hcoupling hle shift vector
  let upper := strictJointDoubledTimeUpperMean hcoupling hle shift vector
  let mixed := strictJointDoubledTimeMixedOSBilinear
    hcoupling hle shift vector
  have hcentral :=
    orientedDoubledTimeCentralConnectedLimit_equiv_connected
      hcoupling hle shift vector
  have hlower := strictJointDoubledTimeLowerMean_equiv_vacuumMean
    hcoupling hle shift vector
  have hupper := strictJointDoubledTimeUpperMean_equiv_vacuumMean
    hcoupling hle shift vector
  have hmeanProduct : CReal.Equiv
      (CReal.mul lower upper) (CReal.mul mean mean) :=
    CReal.Equiv.trans (CReal.mul_congr_left hlower)
      (creal_mul_congr_right hupper)
  have hconnected : CReal.Equiv
      (strictJointDoubledTimeConnectedForm hcoupling hle shift vector)
      (CReal.sub mixed (CReal.mul mean mean)) := by
    change CReal.Equiv
      (CReal.sub mixed (CReal.mul lower upper))
      (CReal.sub mixed (CReal.mul mean mean))
    exact CReal.sub_congr_right hmeanProduct
  have hraw : CReal.Equiv mixed
      (strictJointCauchyTwoStepPairingSeq
        hcoupling hle X shift stage) :=
    CReal.Equiv.symm
      (strictJointCauchyTwoStepPairingSeq_equiv_mixedOS
        hcoupling hle X shift stage)
  have hpairMean : CReal.Equiv mean
      (strictJointCauchyVacuumPairingSeq hcoupling hle X stage) :=
    CReal.Equiv.symm
      (strictJointCauchyVacuumPairingSeq_equiv_mean
        hcoupling hle X stage)
  have hpairProduct : CReal.Equiv
      (CReal.mul mean mean)
      (CReal.mul
        (strictJointCauchyVacuumPairingSeq hcoupling hle X stage)
        (strictJointCauchyVacuumPairingSeq hcoupling hle X stage)) :=
    CReal.Equiv.trans (CReal.mul_congr_left hpairMean)
      (creal_mul_congr_right hpairMean)
  exact CReal.Equiv.trans hcentral
    (CReal.Equiv.trans hconnected
      (CReal.Equiv.trans (CReal.sub_congr_left hraw)
        (CReal.sub_congr_right hpairProduct)))

/-! ## Vacuum orthogonality makes the centering correction vanish -/

/-- For a completed vacuum-orthogonal vector, the vacuum-pairing sequence of
every representative converges to zero. -/
theorem strictJointCauchyVacuumPairingSeq_converges_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle
      (Quotient.mk
        (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
        X)) :
    CReal.ConvergesTo
      (strictJointCauchyVacuumPairingSeq hcoupling hle X)
      CReal.czero := by
  let vacuumRep :=
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).constant
      strictJointCylinderVacuumStage
  have hpair := cauchyPairingSeq_converges
    hcoupling hle X vacuumRep
  have hpairClean : CReal.ConvergesTo
      (strictJointCauchyVacuumPairingSeq hcoupling hle X)
      (cauchyPairingLimit hcoupling hle X vacuumRep) := by
    simpa only [strictJointCauchyVacuumPairingSeq, vacuumRep] using hpair
  have hquotient :
      Quotient.mk CReal.crealSetoid
          (cauchyPairingLimit hcoupling hle X vacuumRep) =
        Quotient.mk CReal.crealSetoid CReal.czero := by
    exact horthogonal
  exact CReal.convergesTo_limit_congr hpairClean
    (Quotient.exact hquotient)

/-- On a completed vacuum-orthogonal vector, the stagewise thermodynamic
central moments converge to the raw completed `2 * shift` pairing. -/
theorem strictJointCauchyCentralMomentSeq_converges_pairingLimit
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle
      (Quotient.mk
        (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
        X))
    (shift : Nat) :
    CReal.ConvergesTo
      (strictJointCauchyCentralMomentSeq hcoupling hle X shift)
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle (shift + shift)).mapCauchy X) X) := by
  let TX := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle (shift + shift)).mapCauchy X
  let rawLimit := cauchyPairingLimit hcoupling hle TX X
  let vacuumSeq := strictJointCauchyVacuumPairingSeq hcoupling hle X
  have hraw : CReal.ConvergesTo
      (strictJointCauchyTwoStepPairingSeq hcoupling hle X shift)
      rawLimit := by
    simpa only [strictJointCauchyTwoStepPairingSeq, TX, rawLimit] using
      (cauchyPairingSeq_converges hcoupling hle TX X)
  have hvacuum : CReal.ConvergesTo vacuumSeq CReal.czero := by
    simpa only [vacuumSeq] using
      (strictJointCauchyVacuumPairingSeq_converges_zero
        hcoupling hle X horthogonal)
  have hsquare := CReal.convergesTo_mul_general hvacuum hvacuum
  have hsquareZero : CReal.ConvergesTo
      (fun stage => CReal.mul (vacuumSeq stage) (vacuumSeq stage))
      CReal.czero :=
    CReal.convergesTo_limit_congr hsquare
      (creal_mul_czero CReal.czero)
  have hcenteredRaw := CReal.convergesTo_add hraw
    (CReal.convergesTo_neg hsquareZero)
  have hcenteredClean : CReal.ConvergesTo
      (fun stage => CReal.sub
        (strictJointCauchyTwoStepPairingSeq
          hcoupling hle X shift stage)
        (CReal.mul (vacuumSeq stage) (vacuumSeq stage)))
      (CReal.add rawLimit (CReal.neg CReal.czero)) := by
    simpa only [CReal.sub] using hcenteredRaw
  have hcenteredLimit : CReal.ConvergesTo
      (fun stage => CReal.sub
        (strictJointCauchyTwoStepPairingSeq
          hcoupling hle X shift stage)
        (CReal.mul (vacuumSeq stage) (vacuumSeq stage)))
      rawLimit :=
    CReal.convergesTo_limit_congr hcenteredClean
      (CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
        (creal_add_czero rawLimit))
  have hcentral :=
    YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (fun stage => CReal.Equiv.symm
        (strictJointCauchyCentralMomentSeq_equiv_centeredPairing
          hcoupling hle X shift stage)) hcenteredLimit
  simpa only [TX, rawLimit, vacuumSeq] using hcentral

/-- At shift zero the target pairing limit is the representative's ordinary
self-pairing limit. -/
theorem strictJointCauchyCentralMomentSeq_zero_converges_selfPairingLimit
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle
      (Quotient.mk
        (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
        X)) :
    CReal.ConvergesTo
      (strictJointCauchyCentralMomentSeq hcoupling hle X 0)
      (cauchyPairingLimit hcoupling hle X X) := by
  let T0X := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle (0 + 0)).mapCauchy X
  have hcentral := strictJointCauchyCentralMomentSeq_converges_pairingLimit
    hcoupling hle X horthogonal 0
  have hlimit : CReal.Equiv
      (cauchyPairingLimit hcoupling hle T0X X)
      (cauchyPairingLimit hcoupling hle X X) := by
    apply CReal.Equiv_of_limit_of_equal
      (aSeq := cauchyPairingSeq hcoupling hle T0X X)
      (bSeq := cauchyPairingSeq hcoupling hle X X)
    · intro stage
      exact strictJointCylinderStageReflectionBilinear_congr
        hcoupling hle
        (strictJointCylinderStage_timeTranslate_zero (X.seq stage))
        (strictJointCylinderStageEquivalent_refl (X.seq stage))
    · exact cauchyPairingSeq_converges hcoupling hle T0X X
    · exact cauchyPairingSeq_converges hcoupling hle X X
  exact CReal.convergesTo_limit_congr hcentral hlimit

/-! ## The unconditional completed gap -/

/-- Representative-level passage of the centered dense `1/16` estimate. -/
theorem cauchyPairingLimit_twoStep_form_gap_centered
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle
      (Quotient.mk
        (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
        X)) :
    CReal.leEv
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle (1 + 1)).mapCauchy X) X)
      (CReal.mul (CReal.ofQ' anchorDecoratedDoubledTimeRate)
        (cauchyPairingLimit hcoupling hle X X)) := by
  have htargetConverges :=
    strictJointCauchyCentralMomentSeq_converges_pairingLimit
      hcoupling hle X horthogonal 1
  have hsourceConverges := CReal.convergesTo_constMul
    anchorDecoratedDoubledTimeRate
    (strictJointCauchyCentralMomentSeq_zero_converges_selfPairingLimit
      hcoupling hle X horthogonal)
  apply CReal.leEv_of_convergesTo_le htargetConverges hsourceConverges
  intro stage
  exact strictJointDenseCentralMoment_le_rate
    hcoupling hle (X.seq stage).vector

/-- The concrete completed two-step transfer has the uniform strict form gap
`1/16` on its entire completed vacuum complement.  This removes the earlier
exact dense-kernel density hypothesis. -/
theorem anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointCylinderCompletedTwoStepVacuumFormGap
      hcoupling hle anchorDecoratedDoubledTimeRate := by
  refine ⟨anchorDecoratedDoubledTimeRate_nonnegative,
    anchorDecoratedDoubledTimeRate_lt_one, ?_⟩
  intro vector horthogonal
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  exact cauchyPairingLimit_twoStep_form_gap_centered
    hcoupling hle X horthogonal

#print axioms strictJointStageVacuumMean_equiv_pairing
#print axioms strictJointStageTwoStepPairing_equiv_mixedOS
#print axioms strictJointCauchyVacuumPairingSeq_equiv_mean
#print axioms strictJointCauchyTwoStepPairingSeq_equiv_mixedOS
#print axioms strictJointCauchyCentralMomentSeq_equiv_centeredPairing
#print axioms strictJointCauchyVacuumPairingSeq_converges_zero
#print axioms strictJointCauchyCentralMomentSeq_converges_pairingLimit
#print axioms strictJointCauchyCentralMomentSeq_zero_converges_selfPairingLimit
#print axioms cauchyPairingLimit_twoStep_form_gap_centered
#print axioms anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredCompletedGap
