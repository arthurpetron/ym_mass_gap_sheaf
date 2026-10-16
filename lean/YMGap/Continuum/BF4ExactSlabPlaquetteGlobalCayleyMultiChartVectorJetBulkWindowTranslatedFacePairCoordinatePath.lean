/-
# Explicit thin coordinate corridor for translated vector-jet face pairs

The generic Z4 coordinate path is specialized to the two literal translated
target faces.  Common spatial and temporal translations cancel from its
length.  For bulk-source faces and offsets in the existing lag window, the
path has at most `5*s + 3*L + 4` adjacency edges, and the resulting common
carrier has at most `5*s + 3*L + 5` plaquettes.

This is the quantitative pair corridor required by the guarded response
consumer.  It does not yet prove that a chosen exterior-face order leaves a
positive distance exponent, sum the insertion budgets, compare the complete
selected and full laws, or prove a continuum or mass-gap conclusion.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier
import YMGap.Continuum.Z4PlaquetteCoordinateAdjPath

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.Z4PlaquetteCoordinateAdjPath

/-- The direct coordinate path between the two literal translated target
faces. -/
def translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
    (P : Placement) (n leftOffset rightOffset : Nat) :
    (leftFace rightFace : Z4Plaq) →
      AdjPath z4SepLinf
        (translatedOriginalBulkVectorQuadraticJetPlacedFace
          P n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetPlacedFace
          P n rightOffset rightFace)
  | ⟨⟨leftX, leftY, leftZ, leftTime⟩, leftPlane⟩,
      ⟨⟨rightX, rightY, rightZ, rightTime⟩, rightPlane⟩ =>
      plaquetteCoordinatePath
        (leftX + P.space) (leftY + P.space) (leftZ + P.space)
        (leftTime + (n + leftOffset) + P.time)
        (rightX + P.space) (rightY + P.space) (rightZ + P.space)
        (rightTime + (n + rightOffset) + P.time)
        leftPlane rightPlane

private theorem bulkSourceFace_time_zero
    {s : Nat} {face : Z4Plaq} (hface : face ∈ bulkSourceFaces s) :
    face.1.2.2.2 = 0 := by
  unfold bulkSourceFaces at hface
  obtain ⟨rx, _, hface⟩ := List.mem_flatMap.mp hface
  obtain ⟨ry, _, hface⟩ := List.mem_flatMap.mp hface
  obtain ⟨rz, _, hface⟩ := List.mem_flatMap.mp hface
  obtain ⟨plane, _, rfl⟩ := List.mem_map.mp hface
  rfl

/-- Common target translation cancels exactly from the coordinate-path
length; only source coordinates and the offset difference remain. -/
theorem translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath_pathLen_le
    (P : Placement) (s n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s) :
    (translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
      P n leftOffset rightOffset leftFace rightFace).pathLen ≤
      natDist leftFace.1.1 rightFace.1.1 +
        natDist leftFace.1.2.1 rightFace.1.2.1 +
        3 * natDist leftFace.1.2.2.1 rightFace.1.2.2.1 +
        3 * natDist leftOffset rightOffset + 4 := by
  obtain ⟨⟨leftX, leftY, leftZ, leftTime⟩, leftPlane⟩ := leftFace
  obtain ⟨⟨rightX, rightY, rightZ, rightTime⟩, rightPlane⟩ := rightFace
  have hleftTime := bulkSourceFace_time_zero hleftFace
  have hrightTime := bulkSourceFace_time_zero hrightFace
  change leftTime = 0 at hleftTime
  change rightTime = 0 at hrightTime
  subst leftTime
  subst rightTime
  have hpath := plaquetteCoordinatePath_pathLen_le
    (leftX + P.space) (leftY + P.space) (leftZ + P.space)
    (0 + (n + leftOffset) + P.time)
    (rightX + P.space) (rightY + P.space) (rightZ + P.space)
    (0 + (n + rightOffset) + P.time)
    leftPlane rightPlane
  simpa only [translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath,
    natDist_add_right, Nat.zero_add, natDist_add_left] using hpath

private theorem natDist_le_of_common_window
    {base side left right : Nat}
    (hleftLower : base ≤ left) (hleftUpper : left < base + side)
    (hrightLower : base ≤ right) (hrightUpper : right < base + side) :
    natDist left right ≤ side := by
  unfold natDist
  omega

private theorem natDist_le_of_common_upper
    {bound left right : Nat} (hleft : left ≤ bound) (hright : right ≤ bound) :
    natDist left right ≤ bound := by
  unfold natDist
  omega

/-- Every pair of listed bulk faces differs by at most `s` in each spatial
base coordinate. -/
theorem bulkSourceFace_spatial_natDist_le
    {s : Nat} {leftFace rightFace : Z4Plaq}
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s) :
    natDist leftFace.1.1 rightFace.1.1 ≤ s ∧
      natDist leftFace.1.2.1 rightFace.1.2.1 ≤ s ∧
      natDist leftFace.1.2.2.1 rightFace.1.2.2.1 ≤ s := by
  have hleft := (bulkSourceFaces_mem_iff s leftFace).mp hleftFace |>.2
  have hright := (bulkSourceFaces_mem_iff s rightFace).mp hrightFace |>.2
  unfold BulkSourceBase at hleft hright
  exact
    ⟨natDist_le_of_common_window hleft.1 hleft.2.1
        hright.1 hright.2.1,
      natDist_le_of_common_window hleft.2.2.1 hleft.2.2.2.1
        hright.2.2.1 hright.2.2.2.1,
      natDist_le_of_common_window hleft.2.2.2.2.1 hleft.2.2.2.2.2
        hright.2.2.2.2.1 hright.2.2.2.2.2⟩

/-- Uniform path length over the complete bulk-source pair and lag window. -/
theorem translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath_pathLen_le_window
    (P : Placement) (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    (translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
      P n leftOffset rightOffset leftFace rightFace).pathLen ≤
        5 * s + 3 * L + 4 := by
  have hpath :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath_pathLen_le
      P s n leftOffset rightOffset leftFace rightFace hleftFace hrightFace
  have hspace := bulkSourceFace_spatial_natDist_le hleftFace hrightFace
  have hoffset := natDist_le_of_common_upper hleftOffset hrightOffset
  omega

/-- The concrete common carrier obtained from the explicit coordinate path. -/
def translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
    (P : Placement) (n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) :
    ProbeCarrier
      (translatedOriginalBulkVectorQuadraticJetFacePairLinks
        P n leftOffset rightOffset leftFace rightFace) :=
  translatedOriginalBulkVectorQuadraticJetFacePairCarrier
    P n leftOffset rightOffset leftFace rightFace
    (translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
      P n leftOffset rightOffset leftFace rightFace)

/-- The explicit pair carrier is linear in source side and lag, rather than
the ambient four-dimensional volume. -/
theorem translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier_support_length_le
    (P : Placement) (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P n leftOffset rightOffset leftFace rightFace).animal.support.length ≤
        5 * s + 3 * L + 5 := by
  exact Nat.le_trans
    (translatedOriginalBulkVectorQuadraticJetFacePairCarrier_support_length_le
      P n leftOffset rightOffset leftFace rightFace
      (translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
        P n leftOffset rightOffset leftFace rightFace))
    (by
      have hpath :=
        translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath_pathLen_le_window
          P s n leftOffset rightOffset L leftFace rightFace
          hleftFace hrightFace hleftOffset hrightOffset
      omega)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath.translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath.translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath_pathLen_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath.bulkSourceFace_spatial_natDist_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath.translatedOriginalBulkVectorQuadraticJetFacePairCoordinatePath_pathLen_le_window
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath.translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath.translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier_support_length_le
