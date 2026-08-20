/-
# Positive contraction interval for the completed even-time transfer form

The fixed-base strict-cylinder theory already proves

  0 <= <T^(2s)x,x> <= <x,x>.

This file transports that interval to arbitrary staged vectors, passes the
termwise order through the choice-free pairing limits, and descends it to the
actual strict OS completion.  Together with completed even-time
self-adjointness, this makes the even subsemigroup the natural transfer route;
no one-step parity reconstruction is needed here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTimeSelfAdjoint
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedEvenTimeInterval

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInnerLaws
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTimeSelfAdjoint
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The staged positive-contraction interval -/

/-- The even-time transfer form of any staged vector is nonnegative and
bounded by its source diagonal form. -/
theorem strictJointCylinderStageEvenTimeTransferForm_interval
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (stage : StrictJointCylinderStage) :
    CReal.leEv CReal.czero
        (strictJointCylinderStageReflectionBilinear hcoupling hle
          (stage.timeTranslate (shift + shift)) stage) ∧
      CReal.leEv
        (strictJointCylinderStageReflectionBilinear hcoupling hle
          (stage.timeTranslate (shift + shift)) stage)
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle stage stage) := by
  let evenShift := shift + shift
  have hbaseFinal : stage.base <= stage.base + evenShift :=
    Nat.le_add_right _ _
  have htarget := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (stage.timeTranslate evenShift) stage
      (Nat.le_refl _) hbaseFinal
  dsimp only [StrictJointCylinderStage.timeTranslate] at htarget
  rw [boxTransportStrictJointCylinderVector_refl] at htarget
  have hsource := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle stage stage (Nat.le_refl _) (Nat.le_refl _)
  have hsourceClean : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle stage.vector stage.vector)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle stage stage) := by
    simpa only [boxTransportStrictJointCylinderVector_refl] using hsource
  have hsourceFromQuadratic : CReal.Equiv
      (stage.vector.reflectionQuadratic hcoupling hle)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle stage stage) :=
    CReal.Equiv.trans
      (CReal.Equiv.symm
        (strictJointCylinderReflectionBilinear_self
          hcoupling hle stage.vector))
      hsourceClean
  have hfixed :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement.evenTimeStrictJointTransferForm_interval
      hcoupling hle shift stage.vector
  exact
    ⟨(CReal.leEv_congr (CReal.Equiv.refl _) htarget).mp hfixed.1,
      (CReal.leEv_congr htarget hsourceFromQuadratic).mp hfixed.2⟩

/-! ## 2. Passage through the representative pairing limits -/

/-- The even-time positive-contraction interval survives the explicit-modulus
Cauchy completion at representative level. -/
theorem cauchyPairingLimit_evenTimeTransferForm_interval
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.leEv CReal.czero
        (cauchyPairingLimit hcoupling hle
          ((strictJointCylinderStageTimeTranslateNonexpansive
            hcoupling hle (shift + shift)).mapCauchy X) X) ∧
      CReal.leEv
        (cauchyPairingLimit hcoupling hle
          ((strictJointCylinderStageTimeTranslateNonexpansive
            hcoupling hle (shift + shift)).mapCauchy X) X)
        (cauchyPairingLimit hcoupling hle X X) := by
  let TX := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle (shift + shift)).mapCauchy X
  have hzeroConverges : CReal.ConvergesTo (fun _ => CReal.czero) CReal.czero :=
    CReal.convergesTo_const CReal.czero
  have htargetConverges := cauchyPairingSeq_converges
    hcoupling hle TX X
  have hsourceConverges := cauchyPairingSeq_converges
    hcoupling hle X X
  constructor
  · apply CReal.leEv_of_convergesTo_le hzeroConverges htargetConverges
    intro n
    exact (strictJointCylinderStageEvenTimeTransferForm_interval
      hcoupling hle shift (X.seq n)).1
  · apply CReal.leEv_of_convergesTo_le
      htargetConverges hsourceConverges
    intro n
    exact (strictJointCylinderStageEvenTimeTransferForm_interval
      hcoupling hle shift (X.seq n)).2

/-! ## 3. The completed even-time transfer interval -/

/-- On every vector in the actual strict OS completion, the even-time transfer
form is positive and bounded above by the identity form. -/
theorem strictJointCylinderCompletedEvenTimeTransferForm_interval
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCnonneg
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle (shift + shift) vector) vector) ∧
      CReal.RCle
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle (shift + shift) vector) vector)
        (strictJointCylinderCompletedInner
          hcoupling hle vector vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  exact cauchyPairingLimit_evenTimeTransferForm_interval
    hcoupling hle shift X

theorem strictJointCylinderCompletedEvenTimeTransferForm_nonneg
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCnonneg
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) vector) vector) :=
  (strictJointCylinderCompletedEvenTimeTransferForm_interval
    hcoupling hle shift vector).1

theorem strictJointCylinderCompletedEvenTimeTransferForm_le_identity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) vector) vector)
      (strictJointCylinderCompletedInner hcoupling hle vector vector) :=
  (strictJointCylinderCompletedEvenTimeTransferForm_interval
    hcoupling hle shift vector).2

/-- The even-time operator is also a norm contraction for the constructed
completed inner form.  Self-adjointness turns its squared norm into the
`4 * shift` transfer form, to which the identity upper bound applies. -/
theorem strictJointCylinderCompletedEvenTimeTranslate_normSq_le
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) vector)
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) vector))
      (strictJointCylinderCompletedInner hcoupling hle vector vector) := by
  let evenShift := shift + shift
  have hadjoint :=
    strictJointCylinderCompletedEvenTimeTranslate_self_adjoint
      hcoupling hle shift vector
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle evenShift vector)
  have hcompose := strictJointCylinderCompletedTimeTranslate_add
    hcoupling hle evenShift evenShift vector
  have hrewrite :
      strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle evenShift vector)
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle evenShift vector) =
        strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle (evenShift + evenShift) vector) vector := by
    calc
      strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle evenShift vector)
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle evenShift vector) =
        strictJointCylinderCompletedInner hcoupling hle vector
          (strictJointCylinderCompletedTimeTranslate hcoupling hle evenShift
            (strictJointCylinderCompletedTimeTranslate
              hcoupling hle evenShift vector)) := hadjoint
      _ = strictJointCylinderCompletedInner hcoupling hle vector
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle (evenShift + evenShift) vector) := by
        rw [hcompose]
      _ = strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTimeTranslate
            hcoupling hle (evenShift + evenShift) vector) vector :=
        strictJointCylinderCompletedInner_symm hcoupling hle _ _
  rw [hrewrite]
  exact strictJointCylinderCompletedEvenTimeTransferForm_le_identity
    hcoupling hle evenShift vector

#print axioms strictJointCylinderStageEvenTimeTransferForm_interval
#print axioms cauchyPairingLimit_evenTimeTransferForm_interval
#print axioms strictJointCylinderCompletedEvenTimeTransferForm_interval
#print axioms strictJointCylinderCompletedEvenTimeTransferForm_nonneg
#print axioms strictJointCylinderCompletedEvenTimeTransferForm_le_identity
#print axioms strictJointCylinderCompletedEvenTimeTranslate_normSq_le

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedEvenTimeInterval
