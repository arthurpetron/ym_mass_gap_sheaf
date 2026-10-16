/-
# Pairwise expansion of the selected-window cross covariance

The actual left-time/right-time vector-jet covariance from the selected
window is expanded into the exact double sum of local face-factor
covariances.  The two placements remain distinct: the left factor is at
offset zero and the right factor is at offset `L`.

This is the local form needed for a later selected-action/full-action face
insertion telescope.  It does not compare those actions, remove a cutoff,
pay a strict margin, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariancePairwise

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance
  (finiteCovariance_twoWeightedSums_pairwise)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource (bulkSourceFaces)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

local infix:50 " ≈ " => Q'.eqv

/-- Exact coefficient-product double sum for the left-time/right-time vector
jet covariance under the unchanged selected ORIGINAL action. -/
def originalBulkVectorQuadraticJetSelectedCrossPairwiseCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  listQSum
    (fun leftFace => listQSum
      (fun rightFace =>
        (originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
          originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
        finiteCovariance w hw0 hw1
          (originalBulkVectorQuadraticJetExtent s n L)
          (originalBulkVectorQuadraticJetIds s n L)
          (originalBulkVectorQuadraticJetIds_physical s n L)
          (originalBulkVectorQuadraticJetFacePlaced s n 0 L leftFace)
          (originalBulkVectorQuadraticJetFacePlaced s n L L rightFace)
          stage)
      (bulkSourceFaces s))
    (bulkSourceFaces s)

/-- The selected cross-time covariance is exactly its weighted local
face-pair expansion; no absolute values or independent-law bounds enter. -/
theorem originalBulkVectorQuadraticJetSelectedCrossCovariance_pairwise
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    originalBulkVectorQuadraticJetSelectedCrossCovariance
        hw0 hw1 s hs stage n L ≈
      originalBulkVectorQuadraticJetSelectedCrossPairwiseCovariance
        hw0 hw1 s hs stage n L := by
  let extent := originalBulkVectorQuadraticJetExtent s n L
  let ids := originalBulkVectorQuadraticJetIds s n L
  let hids := originalBulkVectorQuadraticJetIds_physical s n L
  let weight := originalBulkVectorQuadraticJetFaceWeight s hs
  let leftFactor := originalBulkVectorQuadraticJetFacePlaced s n 0 L
  let rightFactor := originalBulkVectorQuadraticJetFacePlaced s n L L
  have hleft : originalBulkVectorQuadraticJetPlaced s hs n 0 L =
      finitePolySum
        (fun face => polySmul (weight face) (leftFactor face))
        (bulkSourceFaces s) := by
    simpa only [weight, leftFactor] using
      (originalBulkVectorQuadraticJetPlaced_face_sum s hs n 0 L)
  have hright : originalBulkVectorQuadraticJetPlaced s hs n L L =
      finitePolySum
        (fun face => polySmul (weight face) (rightFactor face))
        (bulkSourceFaces s) := by
    simpa only [weight, rightFactor] using
      (originalBulkVectorQuadraticJetPlaced_face_sum s hs n L L)
  unfold originalBulkVectorQuadraticJetSelectedCrossCovariance
    originalBulkVectorQuadraticJetSelectedCrossPairwiseCovariance
  rw [hleft, hright]
  simpa only [extent, ids, hids, weight, leftFactor, rightFactor] using
    (finiteCovariance_twoWeightedSums_pairwise hw0 hw1 extent ids hids stage
      weight leftFactor (bulkSourceFaces s)
      weight rightFactor (bulkSourceFaces s))

/-- The same exact pairwise expansion on the common `(2^66)^2` pair
normalization used by the finite FREE comparison. -/
theorem originalBulkVectorQuadraticJetScaledSelectedCrossCovariance_pairwise
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    originalBulkVectorQuadraticJetScaledSelectedCrossCovariance
        hw0 hw1 s hs stage n L ≈
      let scale := globalCayleyVectorJetNorthWeightScale
      (scale * scale) *
        originalBulkVectorQuadraticJetSelectedCrossPairwiseCovariance
          hw0 hw1 s hs stage n L := by
  let scaleSquare := globalCayleyVectorJetNorthWeightScale *
    globalCayleyVectorJetNorthWeightScale
  change scaleSquare *
      originalBulkVectorQuadraticJetSelectedCrossCovariance
        hw0 hw1 s hs stage n L ≈
    scaleSquare *
      originalBulkVectorQuadraticJetSelectedCrossPairwiseCovariance
        hw0 hw1 s hs stage n L
  exact Q'.mul_eqv_congr_left scaleSquare _ _
    (originalBulkVectorQuadraticJetSelectedCrossCovariance_pairwise
      hw0 hw1 s hs stage n L)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariancePairwise

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariancePairwise.originalBulkVectorQuadraticJetSelectedCrossCovariance_pairwise
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariancePairwise.originalBulkVectorQuadraticJetScaledSelectedCrossCovariance_pairwise
