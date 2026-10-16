/-
# Guarded action response for one translated vector-jet face pair

Given an explicit adjacency corridor between the two literal translated target
faces, the common path carrier now enters the existing guarded covariance
insertion theorem.  The two factor caps are raised to their explicit sum, so
the finite response to one additional physical action face and its fixed-volume
cutoff-removed counterpart inherit the established geometric budget.

The adjacency path and its quantitative length remain input data.  This module
does not construct that corridor, sum omitted target faces, identify the
translated selected law with the full target law, take a thermodynamic or
continuum limit, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier
import YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Common interval cap used by the two translated local factors. -/
def translatedOriginalBulkVectorQuadraticJetFacePairCap
    (n leftOffset rightOffset : Nat) (leftFace rightFace : Z4Plaq) : Q' :=
  originalBulkVectorQuadraticJetFaceCap n leftOffset leftFace +
    originalBulkVectorQuadraticJetFaceCap n rightOffset rightFace

/-- The left translated factor raised to the common pair cap. -/
def translatedOriginalBulkVectorQuadraticJetFacePair_left_interval
    (P : Placement) (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    Interval (boundaryCompleteSlabLinks P.target).length
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        P n leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetFacePairCap
        n leftOffset rightOffset leftFace rightFace) :=
  let left := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n leftOffset L leftFace hsource hleftFace hleftOffset
  let right := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n rightOffset L rightFace hsource hrightFace hrightOffset
  left.raise (originalBulkVectorQuadraticJetFaceCap n rightOffset rightFace)
    right.nonnegative

/-- The right translated factor raised to the same ordered pair cap. -/
def translatedOriginalBulkVectorQuadraticJetFacePair_right_interval
    (P : Placement) (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    Interval (boundaryCompleteSlabLinks P.target).length
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        P n rightOffset rightFace)
      (translatedOriginalBulkVectorQuadraticJetFacePairCap
        n leftOffset rightOffset leftFace rightFace) :=
  let left := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n leftOffset L leftFace hsource hleftFace hleftOffset
  let right := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n rightOffset L rightFace hsource hrightFace hrightOffset
  (right.raise (originalBulkVectorQuadraticJetFaceCap n leftOffset leftFace)
    left.nonnegative).changeCap
      (Q'.add_comm_eqv
        (originalBulkVectorQuadraticJetFaceCap n rightOffset rightFace)
        (originalBulkVectorQuadraticJetFaceCap n leftOffset leftFace))

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
existing guarded budget of the explicit common path carrier. -/
theorem finite_covariance_insertion_bound_translatedFacePair
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
    (path : AdjPath z4SepLinf
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n rightOffset rightFace))
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
        (translatedOriginalBulkVectorQuadraticJetFacePairCarrier
          P n leftOffset rightOffset leftFace rightFace path)
        (slabPlaquetteAt P.target id)
        (translatedOriginalBulkVectorQuadraticJetFacePairCap
          n leftOffset rightOffset leftFace rightFace) := by
  exact finite_covariance_insertion_bound hw0 hw1 hsmall hd hs
    P.target ids hn hi id hid
    (translatedOriginalBulkVectorQuadraticJetFacePair_left_interval
      P s n leftOffset rightOffset L leftFace rightFace hsource
      hleftFace hrightFace hleftOffset hrightOffset)
    (translatedOriginalBulkVectorQuadraticJetFacePair_right_interval
      P s n leftOffset rightOffset L leftFace rightFace hsource
      hleftFace hrightFace hleftOffset hrightOffset)
    (translatedOriginalBulkVectorQuadraticJetFacePairLinks
      P n leftOffset rightOffset leftFace rightFace)
    (translatedOriginalBulkVectorQuadraticJetFacePairCarrier
      P n leftOffset rightOffset leftFace rightFace path)
    (translatedOriginalBulkVectorQuadraticJetFacePair_left_local
      P n leftOffset rightOffset leftFace rightFace)
    (translatedOriginalBulkVectorQuadraticJetFacePair_right_local
      P n leftOffset rightOffset leftFace rightFace)
    stage

/-- The same one-face response after the existing fixed-volume heat-cutoff
removal.  No thermodynamic or continuum limit is taken. -/
theorem covariance_insertion_bound_translatedFacePair
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
    (path : AdjPath z4SepLinf
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n rightOffset rightFace))
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
        (translatedOriginalBulkVectorQuadraticJetFacePairCarrier
          P n leftOffset rightOffset leftFace rightFace path)
        (slabPlaquetteAt P.target id)
        (translatedOriginalBulkVectorQuadraticJetFacePairCap
          n leftOffset rightOffset leftFace rightFace))) := by
  exact covariance_insertion_bound hw0 hw1 hsmall hd hs
    P.target ids hn hi id hid
    (translatedOriginalBulkVectorQuadraticJetFacePair_left_interval
      P s n leftOffset rightOffset L leftFace rightFace hsource
      hleftFace hrightFace hleftOffset hrightOffset)
    (translatedOriginalBulkVectorQuadraticJetFacePair_right_interval
      P s n leftOffset rightOffset L leftFace rightFace hsource
      hleftFace hrightFace hleftOffset hrightOffset)
    (translatedOriginalBulkVectorQuadraticJetFacePairLinks
      P n leftOffset rightOffset leftFace rightFace)
    (translatedOriginalBulkVectorQuadraticJetFacePairCarrier
      P n leftOffset rightOffset leftFace rightFace path)
    (translatedOriginalBulkVectorQuadraticJetFacePair_left_local
      P n leftOffset rightOffset leftFace rightFace)
    (translatedOriginalBulkVectorQuadraticJetFacePair_right_local
      P n leftOffset rightOffset leftFace rightFace)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse.translatedOriginalBulkVectorQuadraticJetFacePairCap
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse.translatedOriginalBulkVectorQuadraticJetFacePair_left_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse.translatedOriginalBulkVectorQuadraticJetFacePair_right_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse.finite_covariance_insertion_bound_translatedFacePair
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse.covariance_insertion_bound_translatedFacePair
