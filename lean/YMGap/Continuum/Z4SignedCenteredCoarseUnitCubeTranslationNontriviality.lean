/-
# Positive coarse-cube occurrence throughout the signed translation orbit

The base-three centered coarse cube defines a genuine signed cylinder
presentation of radius one.  Translating its chart by any signed Z4 vector
literally translates every represented plaquette support while retaining the
same canonical coordinates and Boolean predicate.

The signed common-refinement interface identifies every translate with the
base presentation, and the exact rational approximants are in fact
definitionally unchanged.  The uniform `2^150` occurrence floor can therefore
be lifted directly at every translated presentation, giving constructive-real
strict positivity over the full `Int^4` orbit without a choice principle.
-/

import YMGap.Continuum.Z4CenteredCoarseUnitCubeStateNontriviality
import YMGap.Continuum.Z4SignedCenteredPresentationCommonRefinement

namespace YMGap.Continuum.Z4SignedCenteredCoarseUnitCubeTranslationNontriviality

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity
open YMGap.Continuum.Z4CenteredCoarseUnitCubeStateNontriviality
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredPresentationCommonRefinement
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

/-! ## 1. A genuine signed presentation and its translated support -/

def centeredCoarseUnitCubeSignedChart : SignedCenteredCylinderChart where
  center := signedZero
  radius := 1
  roots := centeredCoarseUnitCubeCylinderRootsAtThree
  rootsCanonical := by
    simpa [centeredBoxBase] using
      centeredCoarseUnitCubeCylinderRootsAtThree_allCanonical

def centeredCoarseUnitCubeSignedPresentation :
    SignedCenteredCylinderPresentation where
  chart := centeredCoarseUnitCubeSignedChart
  predicate := unitCubeSingleOccurrencePredicate

theorem centeredCoarseUnitCubeSignedChart_root_mem :
    centeredCoarseUnitCubeRootAtThree ∈
      centeredCoarseUnitCubeSignedChart.roots :=
  List.mem_singleton.mpr rfl

/-- The marked six-face support is not merely relabelled: its signed
plaquette list is translated pointwise by the requested `Int^4` vector. -/
theorem centeredCoarseUnitCubeSigned_rootSupport_translate
    (shift : SignedZ4Vector) :
    (centeredCoarseUnitCubeSignedChart.rootSupport
        centeredCoarseUnitCubeRootAtThree).map
        (signedTranslatePlaquette shift) =
      (centeredCoarseUnitCubeSignedChart.translate shift).rootSupport
        centeredCoarseUnitCubeRootAtThree :=
  SignedCenteredCylinderChart.rootSupport_translate
    shift centeredCoarseUnitCubeSignedChart
      centeredCoarseUnitCubeRootAtThree

/-! ## 2. Common-refinement covariance and literal approximants -/

theorem centeredCoarseUnitCubeSignedPresentation_translate_aligned
    (shift : SignedZ4Vector) :
    SignedCenteredPresentationAlignedEquivalent
      (centeredCoarseUnitCubeSignedPresentation.translate shift)
      centeredCoarseUnitCubeSignedPresentation :=
  signedCenteredPresentationAlignedEquivalent_translate
    shift centeredCoarseUnitCubeSignedPresentation

def centeredCoarseUnitCubeSignedStateOccurrence : CReal :=
  couplingParametricSignedCenteredPresentationValueAtAnchor
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le
    centeredCoarseUnitCubeSignedPresentation

def centeredCoarseUnitCubeTranslatedStateOccurrence
    (shift : SignedZ4Vector) : CReal :=
  couplingParametricSignedCenteredPresentationValueAtAnchor
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le
    (centeredCoarseUnitCubeSignedPresentation.translate shift)

theorem centeredCoarseUnitCubeTranslatedStateOccurrence_equiv_base
    (shift : SignedZ4Vector) :
    CReal.Equiv
      (centeredCoarseUnitCubeTranslatedStateOccurrence shift)
      centeredCoarseUnitCubeSignedStateOccurrence := by
  exact couplingParametricSignedCenteredPresentationValueAtAnchor_respects
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le
    (centeredCoarseUnitCubeSignedPresentation_translate_aligned shift)

@[simp] theorem centeredCoarseUnitCubeTranslatedStateOccurrence_approx
    (shift : SignedZ4Vector) (stage : Nat) :
    (centeredCoarseUnitCubeTranslatedStateOccurrence shift).approx stage =
      couplingParametricCenteredRecedingCylinderSequence
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) 3
        centeredCoarseUnitCubeCylinderRootsAtThree
        unitCubeSingleOccurrencePredicate stage := by
  rfl

/-! ## 3. Strict positivity at every signed translate -/

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_translatedState
    (shift : SignedZ4Vector) :
    CReal.ofQ' activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      centeredCoarseUnitCubeTranslatedStateOccurrence shift := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [centeredCoarseUnitCubeTranslatedStateOccurrence_approx]
  exact
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_centeredStage stage

/-- One theorem exposing non-vacuity over the full signed lattice orbit. -/
theorem centeredCoarseUnitCubeTranslatedStateOccurrence_pos
    (shift : SignedZ4Vector) :
    CReal.IsPositive
      (centeredCoarseUnitCubeTranslatedStateOccurrence shift) :=
  ⟨activityMatchedCoarseUnitCubeUniformOccurrenceFloor,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_translatedState
      shift⟩

#print axioms centeredCoarseUnitCubeSignedChart_root_mem
#print axioms centeredCoarseUnitCubeSigned_rootSupport_translate
#print axioms centeredCoarseUnitCubeSignedPresentation_translate_aligned
#print axioms centeredCoarseUnitCubeTranslatedStateOccurrence_equiv_base
#print axioms centeredCoarseUnitCubeTranslatedStateOccurrence_approx
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_translatedState
#print axioms centeredCoarseUnitCubeTranslatedStateOccurrence_pos

end YMGap.Continuum.Z4SignedCenteredCoarseUnitCubeTranslationNontriviality
