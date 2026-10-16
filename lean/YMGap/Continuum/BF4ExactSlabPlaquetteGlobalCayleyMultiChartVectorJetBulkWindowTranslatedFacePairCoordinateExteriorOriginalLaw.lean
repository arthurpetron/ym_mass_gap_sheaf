/-
# Canonical full-action comparison with the original selected source law

The translated selected covariance in the exterior telescope is exactly the
placement image of the original selected vector-jet covariance.  Composing
that existing equality with the canonical full-action exterior estimate gives
a direct fixed-volume comparison against the original source law, both with
the exact geometric tail and with an explicit epsilon collar condition.

No thermodynamic or continuum limit is taken.  In particular the computed
collar condition is not asserted to hold along a physical scaling family.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay (blockLength)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- The actual selected source covariance before placement into a larger
target slab. -/
def originalSelectedFacePairCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s n L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) : CReal :=
  covariance w hw0 hw1 (originalBulkVectorQuadraticJetExtent s n L)
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical s n L)
    (originalBulkVectorQuadraticJetFacePlaced s n leftOffset L leftFace)
    (originalBulkVectorQuadraticJetFacePlaced s n rightOffset L rightFace)

/-- The canonical full target covariance of the two literal placed factors. -/
def canonicalFullFacePairCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftOffset rightOffset : Nat) (leftFace rightFace : Z4Plaq) : CReal :=
  covariance w hw0 hw1 target
    (slabPhysicalFaceEdges target) (fun _ hid => hid)
    (translatedOriginalBulkVectorQuadraticJetFacePlaced
      (zeroPlacement s n L target hroom) n leftOffset leftFace)
    (translatedOriginalBulkVectorQuadraticJetFacePlaced
      (zeroPlacement s n L target hroom) n rightOffset rightFace)

/-- The translated selected endpoint of the exterior telescope is exactly the
original selected source covariance. -/
theorem zeroPlacement_selected_covariance_source_pin
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s) :
    Equiv
      (covariance w hw0 hw1 target
        (selectedIds (zeroPlacement s n L target hroom)
          (originalBulkVectorQuadraticJetIds s n L))
        (zeroPlacementSelectedPhysical s n L target hroom)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (zeroPlacement s n L target hroom) n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (zeroPlacement s n L target hroom) n rightOffset rightFace))
      (originalSelectedFacePairCovariance hw0 hw1 s n L leftOffset
        rightOffset leftFace rightFace) := by
  simpa only [originalSelectedFacePairCovariance, zeroPlacementSelectedPhysical]
    using covariance_translatedFacePair_pin
      (zeroPlacement s n L target hroom) hw0 hw1 s n L leftOffset rightOffset
      rfl hleftOffset hrightOffset leftFace rightFace hleftFace hrightFace

/-- Direct comparison of the canonical full target law with the original
selected source law, retaining the exact volume-free tail coefficient. -/
theorem canonicalFull_source_tail_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs (CReal.sub
        (canonicalFullFacePairCovariance hw0 hw1 s n L target hroom
          leftOffset rightOffset leftFace rightFace)
        (originalSelectedFacePairCovariance hw0 hw1 s n L leftOffset
          rightOffset leftFace rightFace)))
      (ofQ' (coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace)) := by
  have hpin := zeroPlacement_selected_covariance_source_pin
    hw0 hw1 s n L target hroom leftOffset rightOffset hleftOffset hrightOffset
    leftFace rightFace hleftFace hrightFace
  exact leEv_trans
    (leEv_of_equiv (abs_equiv_congr (CReal.sub_congr_right hpin.symm)))
    (by
      simpa only [canonicalFullFacePairCovariance] using
        (covariance_zeroPlacement_full_action_tail_bound
          hw0 hw1 hsmall hd hs s n leftOffset rightOffset L target hroom
          leftFace rightFace hleftFace hrightFace hleftOffset hrightOffset))

/-- Under the computed collar condition, the canonical full target covariance
is within `epsilon` of the actual original selected source covariance. -/
theorem canonicalFull_source_small
    {w epsilon : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon)
    (hcollar :
      5 * s + 3 * L + 5 +
          blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4 *
            coordinateExteriorCovarianceBlockCutoff hw0 hd hs s n leftOffset
              rightOffset L target hroom leftFace rightFace epsilon ≤
        Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s)) :
    leEv
      (CReal.abs (CReal.sub
        (canonicalFullFacePairCovariance hw0 hw1 s n L target hroom
          leftOffset rightOffset leftFace rightFace)
        (originalSelectedFacePairCovariance hw0 hw1 s n L leftOffset
          rightOffset leftFace rightFace)))
      (ofQ' epsilon) := by
  have hpin := zeroPlacement_selected_covariance_source_pin
    hw0 hw1 s n L target hroom leftOffset rightOffset hleftOffset hrightOffset
    leftFace rightFace hleftFace hrightFace
  exact leEv_trans
    (leEv_of_equiv (abs_equiv_congr (CReal.sub_congr_right hpin.symm)))
    (by
      simpa only [canonicalFullFacePairCovariance] using
        (covariance_zeroPlacement_full_action_small
          hw0 hw1 hsmall hd hs s n leftOffset rightOffset L target hroom
          leftFace rightFace hleftFace hrightFace hleftOffset hrightOffset
          hepsilon hcollar))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw.originalSelectedFacePairCovariance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw.canonicalFullFacePairCovariance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw.zeroPlacement_selected_covariance_source_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw.canonicalFull_source_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw.canonicalFull_source_small
