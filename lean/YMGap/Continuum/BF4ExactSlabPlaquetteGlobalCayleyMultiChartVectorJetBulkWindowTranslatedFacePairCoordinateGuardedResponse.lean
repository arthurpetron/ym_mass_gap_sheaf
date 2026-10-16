/-
# Guarded response for the explicit translated-face coordinate carrier

The concrete coordinate corridor removes the abstract adjacency-path input from
the finite and fixed-volume cutoff-removed insertion estimates.  The resulting
right-hand side uses a common carrier with the separately checked linear support
bound `5 * s + 3 * L + 5`.

This module still does not prove that an exterior-face order leaves a positive
distance exponent, sum the insertion budgets, identify the complete selected
law with the full target law, take a thermodynamic or continuum limit, or prove
a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateGuardedResponse

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private theorem appendedPhysical {extent : Nat} {ids : List Nat} {id : Nat}
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    ∀ j, j ∈ ids ++ [id] → j ∈ slabPhysicalFaceEdges extent := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hi j hj
  · have heq := List.mem_singleton.mp hj
    subst j
    exact hid

/-- One physical action-face insertion changes the finite covariance by the
guarded budget of the explicit coordinate carrier. -/
theorem finite_covariance_insertion_bound_translatedFacePairCoordinateCarrier
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges P.target)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges P.target)
    (stage : Nat) :
    Q'.abs
      (finiteCovariance w hw0 hw1 P.target (ids ++ [id])
          (appendedPhysical hi hid)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n rightOffset rightFace) stage +
        -(finiteCovariance w hw0 hw1 P.target ids hi
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n rightOffset rightFace) stage)) ≤
      covarianceBudget hd hs
        (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
          P n leftOffset rightOffset leftFace rightFace)
        (slabPlaquetteAt P.target id)
        (translatedOriginalBulkVectorQuadraticJetFacePairCap
          n leftOffset rightOffset leftFace rightFace) := by
  simpa only [translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier]
    using finite_covariance_insertion_bound_translatedFacePair
      P hw0 hw1 hsmall hd hs s n leftOffset rightOffset L
      leftFace rightFace hsource hleftFace hrightFace hleftOffset hrightOffset
      (translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
        P n leftOffset rightOffset leftFace rightFace)
      ids hn hi id hid stage

/-- The same concrete-carrier response after the existing fixed-volume
heat-cutoff removal.  No thermodynamic or continuum limit is taken. -/
theorem covariance_insertion_bound_translatedFacePairCoordinateCarrier
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges P.target)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges P.target) :
    CReal.leEv
      (CReal.abs (CReal.sub
        (covariance w hw0 hw1 P.target (ids ++ [id])
          (appendedPhysical hi hid)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n rightOffset rightFace))
        (covariance w hw0 hw1 P.target ids hi
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n rightOffset rightFace))))
      (CReal.ofQ' (covarianceBudget hd hs
        (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
          P n leftOffset rightOffset leftFace rightFace)
        (slabPlaquetteAt P.target id)
        (translatedOriginalBulkVectorQuadraticJetFacePairCap
          n leftOffset rightOffset leftFace rightFace))) := by
  simpa only [translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier]
    using covariance_insertion_bound_translatedFacePair
      P hw0 hw1 hsmall hd hs s n leftOffset rightOffset L
      leftFace rightFace hsource hleftFace hrightFace hleftOffset hrightOffset
      (translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
        P n leftOffset rightOffset leftFace rightFace)
      ids hn hi id hid

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateGuardedResponse

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateGuardedResponse.finite_covariance_insertion_bound_translatedFacePairCoordinateCarrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateGuardedResponse.covariance_insertion_bound_translatedFacePairCoordinateCarrier
