/-
# Exterior margin for the translated vector-jet coordinate carrier

For the zero-offset placement into an arbitrary larger target slab, membership
in the translated selected action is identified with the literal fixed-spatial
source window.  Every omitted physical target face is therefore separated
from the left vector-jet face by the smaller of the temporal collar `n` and
the centered spatial collar.  Combining that distance with the explicit
coordinate-carrier support bound gives the exact positive-exponent criterion
needed before an exterior-face telescope can be summed.

This module proves only finite geometry.  It does not build the telescope,
sum covariance budgets, compare complete laws, remove volume, construct a
continuum Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateGuardedResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Literal geometric region occupied by the canonical selected source
action.  Spatial plaquettes include the terminal time slice while plaquettes
with an `x3` direction stop one slice earlier. -/
def originalBulkVectorQuadraticJetSourceWindow
    (s n L : Nat) (face : Z4Plaq) : Prop :=
  face.1.1 < s * s ∧
    face.1.2.1 < s * s ∧
    face.1.2.2.1 < s * s ∧
    0 ≤ face.1.2.2.2 ∧
    (((dirsOf face.2).2 ≠ Dir4.x3 ∧
        face.1.2.2.2 ≤ n + (L + n)) ∨
      ((dirsOf face.2).2 = Dir4.x3 ∧
        face.1.2.2.2 < n + (L + n)))

private theorem shiftFace_zero (face : Z4Plaq) :
    shiftFace 0 0 face = face := by
  obtain ⟨⟨x, y, z, time⟩, plane⟩ := face
  rfl

/-- The canonical selected source IDs enumerate exactly the displayed source
window. -/
theorem originalBulkVectorQuadraticJetIds_faces_mem_iff
    (s n L : Nat) (face : Z4Plaq) :
    face ∈
        (originalBulkVectorQuadraticJetIds s n L).map
          (slabPlaquetteAt (originalBulkVectorQuadraticJetExtent s n L)) ↔
      originalBulkVectorQuadraticJetSourceWindow s n L face := by
  unfold originalBulkVectorQuadraticJetIds
    originalBulkVectorQuadraticJetExtent
    originalBulkScalarSquareRemainderIds
    originalBulkScalarSquareRemainderExtent
    originalBulkVectorQuadraticJetSourceWindow
  simpa only [Nat.zero_add] using
    (chainIds_faces_mem_iff
      (s * s + (n + (L + n))) (s * s) 0 (n + (L + n))
      (by omega) (by omega) face)

/-- Under the zero-offset placement, a physical target ID belongs to the
translated selected action exactly when its literal target face lies in the
canonical source window. -/
theorem zeroPlacement_selectedIds_mem_iff
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges target) :
    id ∈ selectedIds (zeroPlacement s n L target hroom)
        (originalBulkVectorQuadraticJetIds s n L) ↔
      originalBulkVectorQuadraticJetSourceWindow s n L
        (slabPlaquetteAt target id) := by
  let P := zeroPlacement s n L target hroom
  constructor
  · intro hselected
    obtain ⟨sourceId, hsourceId, hsourceIdEq⟩ :=
      List.mem_map.mp hselected
    have hsourcePhysical :=
      originalBulkVectorQuadraticJetIds_physical s n L sourceId hsourceId
    have hpin := P.faceId_pin hsourcePhysical
    have hfaceEq :
        slabPlaquetteAt target id =
          slabPlaquetteAt (originalBulkVectorQuadraticJetExtent s n L)
            sourceId := by
      rw [← hsourceIdEq]
      simpa only [P, zeroPlacement, shiftFace_zero] using hpin
    rw [hfaceEq]
    exact (originalBulkVectorQuadraticJetIds_faces_mem_iff
      s n L _).mp (List.mem_map.mpr ⟨sourceId, hsourceId, rfl⟩)
  · intro hwindow
    have hsourceFace :=
      (originalBulkVectorQuadraticJetIds_faces_mem_iff
        s n L (slabPlaquetteAt target id)).mpr hwindow
    obtain ⟨sourceId, hsourceId, hfaceEq⟩ :=
      List.mem_map.mp hsourceFace
    have hsourcePhysical :=
      originalBulkVectorQuadraticJetIds_physical s n L sourceId hsourceId
    have htargetPhysical := P.faceId_physical hsourcePhysical
    have hpin := P.faceId_pin hsourcePhysical
    have htargetFaceEq :
        slabPlaquetteAt target (P.faceId sourceId) =
          slabPlaquetteAt target id := by
      calc
        slabPlaquetteAt target (P.faceId sourceId) =
            slabPlaquetteAt (originalBulkVectorQuadraticJetExtent s n L)
              sourceId := by
                simpa only [P, zeroPlacement, shiftFace_zero] using hpin
        _ = slabPlaquetteAt target id := hfaceEq
    have htargetIdEq : P.faceId sourceId = id :=
      slabPlaquetteAt_injective_on_physical
        htargetPhysical hid htargetFaceEq
    exact List.mem_map.mpr ⟨sourceId, hsourceId, htargetIdEq⟩

/-- The centered spatial collar remaining to the positive side of every bulk
source face. -/
def originalBulkVectorQuadraticJetSpatialCollar (s : Nat) : Nat :=
  s * s - (bulkSourceOffset s + s)

/-- Every face outside the selected source window is at least the smaller of
the temporal and spatial collars from the placed left local face. -/
theorem originalBulkVectorQuadraticJetPlacedFace_linfDist_ge_of_not_sourceWindow
    (s n leftOffset L : Nat) (leftFace insertedFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L)
    (hexterior :
      ¬ originalBulkVectorQuadraticJetSourceWindow s n L insertedFace) :
    Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s) ≤
      linfDist
        (originalBulkVectorQuadraticJetPlacedFace n leftOffset leftFace)
        insertedFace := by
  unfold bulkSourceFaces at hleftFace
  obtain ⟨leftX, hleftX, hleftFace⟩ := List.mem_flatMap.mp hleftFace
  obtain ⟨leftY, hleftY, hleftFace⟩ := List.mem_flatMap.mp hleftFace
  obtain ⟨leftZ, hleftZ, hleftFace⟩ := List.mem_flatMap.mp hleftFace
  obtain ⟨leftPlane, _, rfl⟩ := List.mem_map.mp hleftFace
  obtain ⟨⟨insertedX, insertedY, insertedZ, insertedTime⟩,
    insertedPlane⟩ := insertedFace
  have hs : 0 < s := by
    have := List.mem_range.mp hleftX
    omega
  have hcollar := bulkSourceOffset_add_side_le_square s hs
  by_cases hx : insertedX < s * s
  · by_cases hy : insertedY < s * s
    · by_cases hz : insertedZ < s * s
      · have htime :
            ¬ (((dirsOf insertedPlane).2 ≠ Dir4.x3 ∧
                  insertedTime ≤ n + (L + n)) ∨
                ((dirsOf insertedPlane).2 = Dir4.x3 ∧
                  insertedTime < n + (L + n))) := by
          intro htime
          apply hexterior
          exact ⟨hx, hy, hz, Nat.zero_le _, htime⟩
        have hdist : n ≤ natDist (n + leftOffset) insertedTime := by
          cases insertedPlane <;> simp [dirsOf] at htime <;>
            unfold natDist <;> omega
        have hcomponent :
            natDist (n + leftOffset) insertedTime ≤
              linfDist
                (originalBulkVectorQuadraticJetPlacedFace n leftOffset
                  (bulkSourceFaceAt s leftX leftY leftZ leftPlane))
                ((insertedX, insertedY, insertedZ, insertedTime),
                  insertedPlane) := by
          simpa only [originalBulkVectorQuadraticJetPlacedFace,
            bulkSourceFaceAt, timeShiftPlaquette, timeShiftVertex,
            cPlaq, vComp, Nat.zero_add] using
            (le_linfDist_comp
              (originalBulkVectorQuadraticJetPlacedFace n leftOffset
                (bulkSourceFaceAt s leftX leftY leftZ leftPlane))
              ((insertedX, insertedY, insertedZ, insertedTime),
                insertedPlane)
              Dir4.x3)
        exact Nat.le_trans (Nat.min_le_left _ _)
          (Nat.le_trans hdist hcomponent)
      · have hdist :
            originalBulkVectorQuadraticJetSpatialCollar s ≤
              natDist (bulkSourceOffset s + leftZ) insertedZ := by
          unfold originalBulkVectorQuadraticJetSpatialCollar natDist
          have := List.mem_range.mp hleftZ
          omega
        exact Nat.le_trans (Nat.min_le_right _ _)
          (Nat.le_trans hdist
            (le_linfDist_comp
              (originalBulkVectorQuadraticJetPlacedFace n leftOffset
                (bulkSourceFaceAt s leftX leftY leftZ leftPlane))
              ((insertedX, insertedY, insertedZ, insertedTime),
                insertedPlane)
              Dir4.x2))
    · have hdist :
          originalBulkVectorQuadraticJetSpatialCollar s ≤
            natDist (bulkSourceOffset s + leftY) insertedY := by
        unfold originalBulkVectorQuadraticJetSpatialCollar natDist
        have := List.mem_range.mp hleftY
        omega
      exact Nat.le_trans (Nat.min_le_right _ _)
        (Nat.le_trans hdist
          (le_linfDist_comp
            (originalBulkVectorQuadraticJetPlacedFace n leftOffset
              (bulkSourceFaceAt s leftX leftY leftZ leftPlane))
            ((insertedX, insertedY, insertedZ, insertedTime), insertedPlane)
            Dir4.x1))
  · have hdist :
        originalBulkVectorQuadraticJetSpatialCollar s ≤
          natDist (bulkSourceOffset s + leftX) insertedX := by
      unfold originalBulkVectorQuadraticJetSpatialCollar natDist
      have := List.mem_range.mp hleftX
      omega
    exact Nat.le_trans (Nat.min_le_right _ _)
      (Nat.le_trans hdist
        (le_linfDist_comp
          (originalBulkVectorQuadraticJetPlacedFace n leftOffset
            (bulkSourceFaceAt s leftX leftY leftZ leftPlane))
          ((insertedX, insertedY, insertedZ, insertedTime), insertedPlane)
          Dir4.x0))

/-- Every omitted physical target face has the same collar lower bound from
the root of the concrete coordinate carrier. -/
theorem zeroPlacement_coordinateCarrier_exterior_linfDist_ge
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges target)
    (homitted : id ∉ selectedIds (zeroPlacement s n L target hroom)
      (originalBulkVectorQuadraticJetIds s n L)) :
    Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s) ≤
      linfDist
        (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
          (zeroPlacement s n L target hroom)
          n leftOffset rightOffset leftFace rightFace).animal.root
        (slabPlaquetteAt target id) := by
  have hexterior :
      ¬ originalBulkVectorQuadraticJetSourceWindow s n L
        (slabPlaquetteAt target id) := by
    intro hwindow
    exact homitted ((zeroPlacement_selectedIds_mem_iff
      s n L target hroom hid).mpr hwindow)
  have hdist :=
    originalBulkVectorQuadraticJetPlacedFace_linfDist_ge_of_not_sourceWindow
      s n leftOffset L leftFace (slabPlaquetteAt target id)
      hleftFace hleftOffset hexterior
  change Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s) ≤
    linfDist
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        (zeroPlacement s n L target hroom) n leftOffset leftFace)
      (slabPlaquetteAt target id)
  simpa only [translatedOriginalBulkVectorQuadraticJetPlacedFace,
    zeroPlacement, shiftFace_zero] using hdist

/-- Exact lower bound for the exponent occurring in `covarianceBudget`. -/
theorem zeroPlacement_coordinateCarrier_exterior_exponent_ge
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges target)
    (homitted : id ∉ selectedIds (zeroPlacement s n L target hroom)
      (originalBulkVectorQuadraticJetIds s n L)) :
    Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s) -
        (5 * s + 3 * L + 5) ≤
      linfDist
          (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
            (zeroPlacement s n L target hroom)
            n leftOffset rightOffset leftFace rightFace).animal.root
          (slabPlaquetteAt target id) -
        (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
          (zeroPlacement s n L target hroom)
          n leftOffset rightOffset leftFace rightFace).animal.support.length := by
  have hdist := zeroPlacement_coordinateCarrier_exterior_linfDist_ge
    s n leftOffset rightOffset L target hroom leftFace rightFace
    hleftFace hleftOffset hid homitted
  have hsupport :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier_support_length_le
      (zeroPlacement s n L target hroom)
      s n leftOffset rightOffset L leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset
  omega

/-- The corridor branch leaves a strictly positive geometric exponent whenever
the explicit linear carrier cost is smaller than both finite collars. -/
theorem zeroPlacement_coordinateCarrier_exterior_exponent_pos
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hmargin :
      5 * s + 3 * L + 5 <
        Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s))
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges target)
    (homitted : id ∉ selectedIds (zeroPlacement s n L target hroom)
      (originalBulkVectorQuadraticJetIds s n L)) :
    0 <
      linfDist
          (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
            (zeroPlacement s n L target hroom)
            n leftOffset rightOffset leftFace rightFace).animal.root
          (slabPlaquetteAt target id) -
        (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
          (zeroPlacement s n L target hroom)
          n leftOffset rightOffset leftFace rightFace).animal.support.length := by
  have hdist := zeroPlacement_coordinateCarrier_exterior_linfDist_ge
    s n leftOffset rightOffset L target hroom leftFace rightFace
    hleftFace hleftOffset hid homitted
  have hsupport :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier_support_length_le
      (zeroPlacement s n L target hroom)
      s n leftOffset rightOffset L leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset
  omega

/-- A simple quadratic-room condition discharges the positive-exponent
inequality.  It isolates the only scale choice needed by this corridor branch:
the temporal collar must dominate the linear carrier cost, and the centered
spatial square must contain twice that cost plus the source side. -/
theorem coordinateCarrier_margin_of_quadratic_room
    (s n L : Nat)
    (htime : 5 * s + 3 * L + 6 ≤ n)
    (hspace : 2 * (5 * s + 3 * L + 6) + s ≤ s * s) :
    5 * s + 3 * L + 5 <
      Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s) := by
  have hhalf :
      5 * s + 3 * L + 6 ≤ (s * s - s) / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    omega
  have hcollar :
      5 * s + 3 * L + 6 ≤
        originalBulkVectorQuadraticJetSpatialCollar s := by
    unfold originalBulkVectorQuadraticJetSpatialCollar bulkSourceOffset
    omega
  apply Nat.lt_of_succ_le
  apply Nat.le_min.mpr
  exact ⟨by omega, by omega⟩

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin.originalBulkVectorQuadraticJetIds_faces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin.zeroPlacement_selectedIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin.originalBulkVectorQuadraticJetPlacedFace_linfDist_ge_of_not_sourceWindow
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin.zeroPlacement_coordinateCarrier_exterior_linfDist_ge
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin.zeroPlacement_coordinateCarrier_exterior_exponent_ge
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin.zeroPlacement_coordinateCarrier_exterior_exponent_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin.coordinateCarrier_margin_of_quadratic_room
