/-
# Thermodynamic CReal for the truncated central face cylinder

The fixed chart for truncation floor `m` lives in the box of side `2*m+1`,
which is exactly the natural-coordinate box of a signed-centered chart of
radius `m`.  This file packages that chart at signed center zero and feeds it
to the already proved unconditional strong-coupling receding-volume compiler.

The result is an explicit Bishop real for the size-truncated central face
observable, with the existing dyadic finite-volume modulus.  The full face
observable still requires passing `m` to infinity using the pinned tail, and
the relation to an OS same-object autocorrelation remains open here.
-/

import YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder
import YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

namespace YMGap.Continuum.Z4CanonicalCentralFaceThermodynamicCylinder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

/-! ## 1. The fixed chart as a signed local observable -/

theorem pinnedFaceSourceBase_eq_centeredBoxBase (sizeFloor : Nat) :
    pinnedFaceSourceBase sizeFloor = centeredBoxBase sizeFloor := by
  unfold pinnedFaceSourceBase centeredBoxBase
  omega

def pinnedFaceSignedChart (sizeFloor : Nat) :
    SignedCenteredCylinderChart where
  center := signedZero
  radius := sizeFloor
  roots := pinnedFaceFixedRoots sizeFloor
  rootsCanonical := by
    intro root hroot
    have hcanonical :=
      (mem_canonicalPinnedBelowSizePolymers_iff.mp hroot).1
    rw [← pinnedFaceSourceBase_eq_centeredBoxBase]
    exact hcanonical

def pinnedFaceSignedPresentation (sizeFloor : Nat) :
    SignedCenteredCylinderPresentation where
  chart := pinnedFaceSignedChart sizeFloor
  predicate := canonicalFaceCylinderPredicate

/-- The central natural plaquette of the chart is the signed plaquette at the
origin. -/
theorem pinnedFacePlaquette_to_signed_origin (sizeFloor : Nat) :
    signedTranslatePlaquette signedZero
        (natPlaquetteToCenteredSigned sizeFloor
          (pinnedFacePlaquette sizeFloor 0)) =
      signedAbsoluteProbe := by
  simp [pinnedFacePlaquette, signedAbsoluteProbe,
    natPlaquetteToCenteredSigned, natVertexToCenteredSigned,
    natCoordinateToCenteredSigned, signedTranslatePlaquette,
    signedTranslateVertex, signedAdd, signedZero]

/-- The finite event carried by the signed chart is exactly the source-box
size-truncated central-face event. -/
theorem pinnedFaceSignedChart_event_eq_truncated
    (sizeFloor : Nat) (family : List (List Nat)) :
    cylinderEvent (pinnedFaceSignedChart sizeFloor).roots
        canonicalFaceCylinderPredicate family =
      canonicalFaceTruncatedCylinderEvent
        (pinnedFaceSourceBase sizeFloor)
        (pinnedFaceId sizeFloor 0) sizeFloor family := by
  rfl

/-! ## 2. The unconditional anchor-coupling thermodynamic value -/

theorem anchorCoupling_nonnegative : (0 : Q') ≤ anchorCoupling := by
  decide

theorem pinnedFaceSignedPresentationVolumeModulus
    (sizeFloor : Nat) :
    SignedCenteredPresentationVolumeModulus anchorCoupling
      anchorCoupling_nonnegative
      (pinnedFaceSignedPresentation sizeFloor) :=
  signedCenteredPresentationVolumeModulus_of_anchor
    anchorCoupling_nonnegative (Q'.le_refl' anchorCoupling)
    (pinnedFaceSignedPresentation sizeFloor)

/-- The constructive thermodynamic value of the size-truncated central face
observable at the proved anchor coupling. -/
def anchorPinnedFaceTruncatedThermodynamicValue
    (sizeFloor : Nat) : CReal :=
  couplingParametricSignedCenteredPresentationValueAtAnchor
    anchorCoupling anchorCoupling_nonnegative
    (Q'.le_refl' anchorCoupling)
    (pinnedFaceSignedPresentation sizeFloor)

@[simp] theorem anchorPinnedFaceTruncatedThermodynamicValue_approx
    (sizeFloor stage : Nat) :
    (anchorPinnedFaceTruncatedThermodynamicValue sizeFloor).approx stage =
      couplingParametricSignedCenteredPresentationSequence
        anchorCoupling anchorCoupling_nonnegative
        (pinnedFaceSignedPresentation sizeFloor) stage := rfl

theorem anchorPinnedFaceTruncatedThermodynamicValue_nonnegative
    (sizeFloor : Nat) :
    CReal.ofQ' 0 ≤ anchorPinnedFaceTruncatedThermodynamicValue sizeFloor := by
  exact couplingParametricSignedCenteredPresentationValueAtAnchor_nonnegative
    anchorCoupling_nonnegative (Q'.le_refl' anchorCoupling)
    (pinnedFaceSignedPresentation sizeFloor)

theorem anchorPinnedFaceTruncatedThermodynamicValue_le_one
    (sizeFloor : Nat) :
    anchorPinnedFaceTruncatedThermodynamicValue sizeFloor ≤ CReal.ofQ' 1 := by
  exact couplingParametricSignedCenteredPresentationValueAtAnchor_le_one
    anchorCoupling_nonnegative (Q'.le_refl' anchorCoupling)
    (pinnedFaceSignedPresentation sizeFloor)

#print axioms pinnedFaceSourceBase_eq_centeredBoxBase
#print axioms pinnedFacePlaquette_to_signed_origin
#print axioms pinnedFaceSignedChart_event_eq_truncated
#print axioms pinnedFaceSignedPresentationVolumeModulus
#print axioms anchorPinnedFaceTruncatedThermodynamicValue
#print axioms anchorPinnedFaceTruncatedThermodynamicValue_nonnegative
#print axioms anchorPinnedFaceTruncatedThermodynamicValue_le_one

end YMGap.Continuum.Z4CanonicalCentralFaceThermodynamicCylinder
