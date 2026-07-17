/-
# Signed-entry descent for the heterogeneous oriented doubled-time form

The ordinary joint centered chart used for an oriented left/right pair has
four Boolean blocks.  Its predicate retains the lower block of the left
presentation and the upper block of the right presentation.  The finite
recoding theorem therefore identifies every later receding centered event
with the corresponding heterogeneous mixed signed event.  This file lifts
that exact event identity to constructive-real entries and then assembles the
entries with separate left and right coefficient tables.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointSignedEntry

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeSignedEntry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderPresentationColimit
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointSignedEntry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedSignedSpatialComparison
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredFiniteColimitDescent
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

/-! ## 1. Exact receding-event descent -/

theorem orientedDoubledTimeJointRecedingEvent_eq_signedMixed
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) (stage : Nat) :
    centeredRecedingCylinderEvent
        (strictJointSignedFixedBase
          (base + (shift + shift))
          (fixedStage - (shift + shift)))
        stage
        (centralStrictJointCenteredStageRoots
          (base + (shift + shift))
          (fixedStage - (shift + shift))
          (orientedDoubledTimeJointRoots shift left right))
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) =
      centeredRecedingCylinderEvent
        (centeredBoxBase (strictQueryBase base + fixedStage))
        stage
        (orientedDoubledTimeMixedCenteredRoots
          base shift fixedStage left.roots right.roots)
        (centralStrictJointPairPredicate
          left.roots.length leftBits rightBits) := by
  let fixedBase := centeredBoxBase (strictQueryBase base + fixedStage)
  have hbase := strictJointDoubledTimeMixedJointFixedBase_eq_signed
    base shift fixedStage hstage
  have hfixed := orientedDoubledTimeJointCenteredEvent_eq_signedMixed
    hstage left right leftBits rightBits
  have hmapped := cylinderEvent_eq_map_common hfixed
    (centeredOffsetCanonicalRoot (fixedBase + stage) fixedBase)
  rw [hbase]
  simpa only [centeredRecedingCylinderEvent,
    centeredRecedingStageRoots, centeredRecedingStageRadius,
    centeredOffsetCylinderRoots, sourceCylinderEvent, fixedBase]
    using hmapped

theorem couplingParametricOrientedJointSignedReceding_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) :
    CReal.Equiv
      (couplingParametricCenteredRecedingCylinderLimitAtAnchor
        coupling hcoupling hle
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits)
        (centralStrictJointCenteredStageRoots_canonical
          (stage := fixedStage - (shift + shift))
          (orientedDoubledTimeJointRoots_canonical shift left right)))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (orientedDoubledTimeMixedSignedPresentation
          base shift fixedStage left.roots right.roots
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits)
          hstage left.rootsCanonical right.rootsCanonical)) := by
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
        (orientedDoubledTimeJointRoots shift left right))
      (orientedDoubledTimeJointPredicate
        left.roots.length right.roots.length leftBits rightBits) stage =
    couplingParametricCenteredRecedingCylinderSequence
      coupling hcoupling
      (centeredBoxBase (strictQueryBase base + fixedStage))
      (orientedDoubledTimeMixedCenteredRoots
        base shift fixedStage left.roots right.roots)
      (centralStrictJointPairPredicate
        left.roots.length leftBits rightBits) stage
  unfold couplingParametricCenteredRecedingCylinderSequence
  rw [orientedDoubledTimeJointRecedingEvent_eq_signedMixed
      hstage left right leftBits rightBits stage,
    strictJointDoubledTimeMixedJointFixedBase_eq_signed
      base shift fixedStage hstage]

/-- Each projected ordinary-joint centered limit is the heterogeneous mixed
signed entry with the same two selected fingerprints. -/
theorem couplingParametricOrientedJointCenteredLimit_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) :
    CReal.Equiv
      (couplingParametricStrictJointCenteredLimit
        coupling hcoupling hle
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits)
        (orientedDoubledTimeJointRoots_canonical shift left right))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (orientedDoubledTimeMixedSignedPresentation
          base shift fixedStage left.roots right.roots
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits)
          hstage left.rootsCanonical right.rootsCanonical)) := by
  exact CReal.Equiv.trans
    (couplingParametricStrictJointCenteredLimit_equiv_signedRecedingStage
      hcoupling hle
      (orientedDoubledTimeJointRoots_canonical shift left right)
      (orientedDoubledTimeJointPredicate
        left.roots.length right.roots.length leftBits rightBits)
      (fixedStage := fixedStage - (shift + shift)))
    (couplingParametricOrientedJointSignedReceding_equiv_mixedSigned
      hcoupling hle hstage left right leftBits rightBits)

/-! ## 2. Finite signed assembly -/

def orientedDoubledTimeMixedSignedBilinear
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base) : CReal :=
  listCRealSum
    (fun leftBits => listCRealSum
      (fun rightBits => CReal.mul
        (CReal.ofQ' (left.coefficient leftBits * right.coefficient rightBits))
        (couplingParametricSignedCenteredPresentationValueAtAnchor
          coupling hcoupling hle
          (orientedDoubledTimeMixedSignedPresentation
            base shift fixedStage left.roots right.roots
            (centralStrictJointPairPredicate
              left.roots.length leftBits rightBits)
            hstage left.rootsCanonical right.rootsCanonical)))
      (strictJointFingerprintSpace right.roots.length))
    (strictJointFingerprintSpace left.roots.length)

private theorem creal_equiv_refl_local (value : CReal) :
    CReal.Equiv value value := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have hnonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨Q'.add_le_self_of_nonneg _ _ hnonnegative,
    Q'.add_le_self_of_nonneg _ _ hnonnegative⟩

private theorem creal_mul_congr_right_local
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  (CRealAlg.cmul_comm scalar left).trans
    ((CReal.mul_congr_left h).trans (CRealAlg.cmul_comm right scalar))

private theorem listCRealSum_congr_on_local
    {State : Type} {left right : State → CReal} :
    ∀ states : List State,
      (∀ state, state ∈ states → CReal.Equiv (left state) (right state)) →
      CReal.Equiv (listCRealSum left states) (listCRealSum right states)
  | [], _ => creal_equiv_refl_local CReal.czero
  | head :: tail, h => by
      have hhead : CReal.Equiv (left head) (right head) :=
        h head List.mem_cons_self
      have htail : CReal.Equiv
          (listCRealSum left tail) (listCRealSum right tail) :=
        listCRealSum_congr_on_local tail
          (fun state hstate => h state (List.mem_cons_of_mem head hstate))
      exact CReal.Equiv.trans
        (CReal.add_congr_left hhead)
        (CReal.add_congr_right htail)

theorem orientedDoubledTimeJointCenteredBilinear_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedDoubledTimeJointCenteredBilinear
        coupling hcoupling hle shift left right)
      (orientedDoubledTimeMixedSignedBilinear
        coupling hcoupling hle hstage left right) := by
  unfold orientedDoubledTimeJointCenteredBilinear
    orientedDoubledTimeMixedSignedBilinear
  apply listCRealSum_congr_on_local
  intro leftBits hleftBits
  apply listCRealSum_congr_on_local
  intro rightBits hrightBits
  apply creal_mul_congr_right_local
  exact couplingParametricOrientedJointCenteredLimit_equiv_mixedSigned
    hcoupling hle hstage left right leftBits rightBits

/-- The direct oriented common-box reflection bilinear is exactly its mixed
signed finite assembly. -/
theorem orientedDoubledTimeReflectionBilinear_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedDoubledTimeReflectionBilinear
        hcoupling hle shift left right)
      (orientedDoubledTimeMixedSignedBilinear
        coupling hcoupling hle hstage left right) :=
  CReal.Equiv.trans
    (orientedDoubledTimeReflectionBilinear_equiv_jointCentered
      hcoupling hle shift left right)
    (orientedDoubledTimeJointCenteredBilinear_equiv_mixedSigned
      hcoupling hle hstage left right)

#print axioms orientedDoubledTimeJointRecedingEvent_eq_signedMixed
#print axioms couplingParametricOrientedJointSignedReceding_equiv_mixedSigned
#print axioms couplingParametricOrientedJointCenteredLimit_equiv_mixedSigned
#print axioms orientedDoubledTimeJointCenteredBilinear_equiv_mixedSigned
#print axioms orientedDoubledTimeReflectionBilinear_equiv_mixedSigned

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeSignedEntry
