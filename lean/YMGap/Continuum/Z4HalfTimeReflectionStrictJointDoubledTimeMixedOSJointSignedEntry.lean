/-
# The projected joint centered limit equals the mixed signed entry

The fixed-stage event equality survives every centered receding re-encoding,
because both root lists are mapped by the same canonical re-encoder.  Hence
the two receding exact-rational sequences agree stage by stage.  Composing
this exact descent with the existing cofinal strict-joint theorem identifies
the projected ordinary joint centered limit with the mixed signed
presentation value.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointSignedEntry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderPresentationColimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredFiniteColimitDescent
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

/-- The standard joint fixed base at the reduced outer stage is exactly the
diagonal base of the mixed signed chart. -/
theorem strictJointDoubledTimeMixedJointFixedBase_eq_signed
    (base shift fixedStage : Nat)
    (hstage : shift + shift ≤ fixedStage) :
    strictJointSignedFixedBase
        (base + (shift + shift))
        (fixedStage - (shift + shift)) =
      centeredBoxBase (strictQueryBase base + fixedStage) := by
  unfold strictJointSignedFixedBase
  rw [strictJointDoubledTime_mixedRadius_eq hstage]

/-- Every later centered receding event of the projected ordinary joint
presentation is literally the corresponding mixed signed receding event. -/
theorem strictJointDoubledTimeMixedJointRecedingEvent_eq_signedMixed
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) (stage : Nat) :
    centeredRecedingCylinderEvent
        (strictJointSignedFixedBase
          (base + (shift + shift))
          (fixedStage - (shift + shift)))
        stage
        (centralStrictJointCenteredStageRoots
          (base + (shift + shift))
          (fixedStage - (shift + shift))
          (strictJointDoubledTimeMixedJointRoots shift vector))
        (strictJointDoubledTimeMixedJointPredicate
          vector.roots.length left right) =
      centeredRecedingCylinderEvent
        (centeredBoxBase (strictQueryBase base + fixedStage))
        stage
        (strictJointDoubledTimeMixedCenteredRoots
          base shift fixedStage vector.roots)
        (centralStrictJointPairPredicate
          vector.roots.length left right) := by
  let fixedBase := centeredBoxBase (strictQueryBase base + fixedStage)
  have hbase := strictJointDoubledTimeMixedJointFixedBase_eq_signed
    base shift fixedStage hstage
  have hfixed :=
    strictJointDoubledTimeMixedJointCenteredEvent_eq_signedMixed
      hstage vector left right
  have hmapped := cylinderEvent_eq_map_common hfixed
    (centeredOffsetCanonicalRoot (fixedBase + stage) fixedBase)
  rw [hbase]
  simpa only [centeredRecedingCylinderEvent,
    centeredRecedingStageRoots, centeredRecedingStageRadius,
    centeredOffsetCylinderRoots, sourceCylinderEvent, fixedBase]
    using hmapped

/-- The receding value based at the aligned ordinary joint stage is exactly
the existing mixed signed-presentation value. -/
theorem couplingParametricMixedJointSignedReceding_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) :
    CReal.Equiv
      (couplingParametricCenteredRecedingCylinderLimitAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedJointPredicate
          vector.roots.length left right)
        (centralStrictJointCenteredStageRoots_canonical
          (stage := fixedStage - (shift + shift))
          (strictJointDoubledTimeMixedJointRoots_canonical shift vector)))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedSignedPresentation
          base shift fixedStage vector.roots
          (centralStrictJointPairPredicate
            vector.roots.length left right)
          hstage vector.rootsCanonical)) := by
  apply CReal.Equiv_of_lifted_approx_equal
  intro stage
  apply YMGap.Constructive.TrigAdd.equiv_ofQ'_of_eqv
  apply Q'.eqv_of_eq
  change couplingParametricCenteredRecedingCylinderSequence
      coupling hcoupling
      (strictJointSignedFixedBase
        (base + (shift + shift))
        (fixedStage - (shift + shift)))
      (centralStrictJointCenteredStageRoots
        (base + (shift + shift))
        (fixedStage - (shift + shift))
        (strictJointDoubledTimeMixedJointRoots shift vector))
      (strictJointDoubledTimeMixedJointPredicate
        vector.roots.length left right) stage =
    couplingParametricCenteredRecedingCylinderSequence
      coupling hcoupling
      (centeredBoxBase (strictQueryBase base + fixedStage))
      (strictJointDoubledTimeMixedCenteredRoots
        base shift fixedStage vector.roots)
      (centralStrictJointPairPredicate
        vector.roots.length left right) stage
  unfold couplingParametricCenteredRecedingCylinderSequence
  rw [strictJointDoubledTimeMixedJointRecedingEvent_eq_signedMixed
      hstage vector left right stage,
    strictJointDoubledTimeMixedJointFixedBase_eq_signed
      base shift fixedStage hstage]

/-- Entrywise terminal centered identity: the projected ordinary joint
centered limit is the mixed signed entry used by the translated quadratic.
-/
theorem couplingParametricMixedJointCenteredLimit_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) :
    CReal.Equiv
      (couplingParametricStrictJointCenteredLimit
        coupling hcoupling hle
        (strictJointDoubledTimeMixedJointPredicate
          vector.roots.length left right)
        (strictJointDoubledTimeMixedJointRoots_canonical shift vector))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedSignedPresentation
          base shift fixedStage vector.roots
          (centralStrictJointPairPredicate
            vector.roots.length left right)
          hstage vector.rootsCanonical)) := by
  exact CReal.Equiv.trans
    (couplingParametricStrictJointCenteredLimit_equiv_signedRecedingStage
      hcoupling hle
      (strictJointDoubledTimeMixedJointRoots_canonical shift vector)
      (strictJointDoubledTimeMixedJointPredicate
        vector.roots.length left right)
      (fixedStage := fixedStage - (shift + shift)))
    (couplingParametricMixedJointSignedReceding_equiv_mixedSigned
      hcoupling hle hstage vector left right)

#print axioms strictJointDoubledTimeMixedJointFixedBase_eq_signed
#print axioms strictJointDoubledTimeMixedJointRecedingEvent_eq_signedMixed
#print axioms couplingParametricMixedJointSignedReceding_equiv_mixedSigned
#print axioms couplingParametricMixedJointCenteredLimit_equiv_mixedSigned

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointSignedEntry
