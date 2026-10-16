/-
# Exterior margin for the thermodynamic vector-jet placement

The explicit thermodynamic placement protects the translated coordinate
carrier root inside the complete translated source box.  Any target face
closer than the displayed quadratic margin can therefore be unshifted to a
physical source face.  If that target face is omitted by the selected action,
its unshifted face lies outside the canonical vector-jet source window, where
the existing source-window separation theorem applies.

This is finite geometry only.  It does not sum the exterior insertion
budgets, prove thermodynamic convergence of the selected law, construct a
continuum theory or Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Coordinate translation used by an arbitrary source placement. -/
def placementCoordinateOffset (P : Placement) : Dir4 → Nat
  | .x0 | .x1 | .x2 => P.space
  | .x3 => P.time

/-- Strict translated source box.  It is sufficient for recovering a
physical source plaquette and intentionally excludes the terminal fringe. -/
def PlacementSourceBox (P : Placement) (face : Z4Plaq) : Prop :=
  ∀ direction,
    placementCoordinateOffset P direction ≤ cPlaq face direction ∧
      cPlaq face direction <
        placementCoordinateOffset P direction + P.source

/-- Coordinate subtraction inside a translated source box. -/
def unshiftPlacementFace (P : Placement) (face : Z4Plaq) : Z4Plaq :=
  ((face.1.1 - P.space, face.1.2.1 - P.space,
    face.1.2.2.1 - P.space, face.1.2.2.2 - P.time), face.2)

theorem unshiftPlacementFace_physical
    {P : Placement} {face : Z4Plaq} (hface : PlacementSourceBox P face) :
    unshiftPlacementFace P face ∈
      boundaryCompleteSlabPlaquettes P.source := by
  obtain ⟨⟨x, y, z, time⟩, plane⟩ := face
  have hx := hface Dir4.x0
  have hy := hface Dir4.x1
  have hz := hface Dir4.x2
  have htime := hface Dir4.x3
  simp only [placementCoordinateOffset, cPlaq, vComp] at hx hy hz htime
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · rw [mem_boxPlaquettes]
    change x - P.space < P.source + 1 ∧
      y - P.space < P.source + 1 ∧
      z - P.space < P.source + 1 ∧
      time - P.time < P.source + 1
    exact ⟨by omega, by omega, by omega, by omega⟩
  · cases plane <;>
      simp only [unshiftPlacementFace, plaquetteTimeAdmissible] <;> omega

theorem shift_unshiftPlacementFace
    {P : Placement} {face : Z4Plaq} (hface : PlacementSourceBox P face) :
    shiftFace P.space P.time (unshiftPlacementFace P face) = face := by
  obtain ⟨⟨x, y, z, time⟩, plane⟩ := face
  have hx := (hface Dir4.x0).1
  have hy := (hface Dir4.x1).1
  have hz := (hface Dir4.x2).1
  have htime := (hface Dir4.x3).1
  change P.space ≤ x at hx
  change P.space ≤ y at hy
  change P.space ≤ z at hz
  change P.time ≤ time at htime
  simp only [unshiftPlacementFace, shiftFace, shiftVertex,
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy,
    Nat.sub_add_cancel hz, Nat.sub_add_cancel htime]

/-- Literal translated image of the canonical selected source window. -/
def translatedOriginalBulkVectorQuadraticJetSourceWindow
    (P : Placement) (s n L : Nat) (face : Z4Plaq) : Prop :=
  ∃ sourceFace,
    originalBulkVectorQuadraticJetSourceWindow s n L sourceFace ∧
      face = shiftFace P.space P.time sourceFace

/-- For any placement of the canonical source extent, selected-ID membership
is exactly membership in the literal translated source window. -/
theorem selectedIds_mem_iff_translatedSourceWindow
    (P : Placement) (s n L : Nat)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges P.target) :
    id ∈ selectedIds P (originalBulkVectorQuadraticJetIds s n L) ↔
      translatedOriginalBulkVectorQuadraticJetSourceWindow P s n L
        (slabPlaquetteAt P.target id) := by
  constructor
  · intro hselected
    obtain ⟨sourceId, hsourceId, hsourceIdEq⟩ :=
      List.mem_map.mp hselected
    have hsourcePhysical : sourceId ∈ slabPhysicalFaceEdges P.source := by
      rw [hsource]
      exact originalBulkVectorQuadraticJetIds_physical s n L sourceId
        hsourceId
    have hsourceWindow :=
      (originalBulkVectorQuadraticJetIds_faces_mem_iff s n L
        (slabPlaquetteAt (originalBulkVectorQuadraticJetExtent s n L)
          sourceId)).mp
        (List.mem_map.mpr ⟨sourceId, hsourceId, rfl⟩)
    refine ⟨slabPlaquetteAt
      (originalBulkVectorQuadraticJetExtent s n L) sourceId,
      hsourceWindow, ?_⟩
    rw [← hsourceIdEq]
    simpa only [hsource] using P.faceId_pin hsourcePhysical
  · rintro ⟨sourceFace, hsourceWindow, hfaceEq⟩
    have hsourceFace :=
      (originalBulkVectorQuadraticJetIds_faces_mem_iff
        s n L sourceFace).mpr hsourceWindow
    obtain ⟨sourceId, hsourceId, hsourceFaceEq⟩ :=
      List.mem_map.mp hsourceFace
    have hsourcePhysical : sourceId ∈ slabPhysicalFaceEdges P.source := by
      rw [hsource]
      exact originalBulkVectorQuadraticJetIds_physical s n L sourceId
        hsourceId
    have htargetPhysical := P.faceId_physical hsourcePhysical
    have htargetFaceEq :
        slabPlaquetteAt P.target (P.faceId sourceId) =
          slabPlaquetteAt P.target id := by
      calc
        slabPlaquetteAt P.target (P.faceId sourceId) =
            shiftFace P.space P.time
              (slabPlaquetteAt P.source sourceId) :=
                P.faceId_pin hsourcePhysical
        _ = shiftFace P.space P.time sourceFace := by
              rw [hsource, hsourceFaceEq]
        _ = slabPlaquetteAt P.target id := hfaceEq.symm
    have htargetIdEq : P.faceId sourceId = id :=
      slabPlaquetteAt_injective_on_physical
        htargetPhysical hid htargetFaceEq
    exact List.mem_map.mpr ⟨sourceId, hsourceId, htargetIdEq⟩

/-- A root protected by `margin` inside the strict translated source box. -/
def PlacementProtectedRoot
    (P : Placement) (margin : Nat) (root : Z4Plaq) : Prop :=
  ∀ direction,
    placementCoordinateOffset P direction + margin ≤
        cPlaq root direction ∧
      cPlaq root direction + margin ≤
        placementCoordinateOffset P direction + P.source

theorem near_PlacementProtectedRoot_sourceBox
    {P : Placement} {margin : Nat} {root face : Z4Plaq}
    (hroot : PlacementProtectedRoot P margin root)
    (hdist : linfDist root face < margin) :
    PlacementSourceBox P face := by
  intro direction
  have hrootDirection := hroot direction
  have hdistDirection := le_linfDist_comp root face direction
  simp only [natDist] at hdistDirection
  constructor <;> omega

theorem linfDist_shiftFace
    (space time : Nat) (left right : Z4Plaq) :
    linfDist (shiftFace space time left) (shiftFace space time right) =
      linfDist left right := by
  obtain ⟨⟨leftX, leftY, leftZ, leftTime⟩, leftPlane⟩ := left
  obtain ⟨⟨rightX, rightY, rightZ, rightTime⟩, rightPlane⟩ := right
  simp only [linfDist, cPlaq, vComp, shiftFace, shiftVertex, natDist,
    Nat.add_sub_add_right]

/-- Quadratic collar protected simultaneously on the lower spatial side, the
upper selected-window side, and both chronological sides. -/
def thermodynamicExteriorMargin (s : Nat) : Nat :=
  Nat.min (s * s)
    (Nat.min (bulkSourceOffset s)
      (originalBulkVectorQuadraticJetSpatialCollar s))

/-- Numeric protection in each spatial coordinate. -/
theorem thermodynamicSpatialProtection
    (s L coordinate : Nat)
    (hcoordinateLower : bulkSourceOffset s ≤ coordinate)
    (hcoordinateUpper : coordinate < bulkSourceOffset s + s) :
    (thermodynamicPlacement s L).space + thermodynamicExteriorMargin s ≤
        coordinate + (thermodynamicPlacement s L).space ∧
      coordinate + (thermodynamicPlacement s L).space +
            thermodynamicExteriorMargin s ≤
        (thermodynamicPlacement s L).space +
          (thermodynamicPlacement s L).source := by
  have hmarginTime : thermodynamicExteriorMargin s ≤ s * s :=
    Nat.min_le_left _ _
  have hmarginOffset :
      thermodynamicExteriorMargin s ≤ bulkSourceOffset s :=
    Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  have hs : 0 < s := by omega
  have hwindow := bulkSourceOffset_add_side_le_square s hs
  change 3 * (s * s) - bulkSourceOffset s +
        thermodynamicExteriorMargin s ≤
      coordinate + (3 * (s * s) - bulkSourceOffset s) ∧
    coordinate + (3 * (s * s) - bulkSourceOffset s) +
          thermodynamicExteriorMargin s ≤
      3 * (s * s) - bulkSourceOffset s +
        (s * s + (s * s + (L + s * s)))
  constructor <;> omega

/-- Numeric protection in the chronological coordinate. -/
theorem thermodynamicTimeProtection
    (s L leftOffset : Nat) (hleftOffset : leftOffset ≤ L) :
    (thermodynamicPlacement s L).time + thermodynamicExteriorMargin s ≤
        0 + (s * s + leftOffset) +
          (thermodynamicPlacement s L).time ∧
      0 + (s * s + leftOffset) +
            (thermodynamicPlacement s L).time +
            thermodynamicExteriorMargin s ≤
        (thermodynamicPlacement s L).time +
          (thermodynamicPlacement s L).source := by
  have hmarginTime : thermodynamicExteriorMargin s ≤ s * s :=
    Nat.min_le_left _ _
  change 3 * (s * s) - s * s + thermodynamicExteriorMargin s ≤
      0 + (s * s + leftOffset) + (3 * (s * s) - s * s) ∧
    0 + (s * s + leftOffset) + (3 * (s * s) - s * s) +
          thermodynamicExteriorMargin s ≤
      3 * (s * s) - s * s +
        (s * s + (s * s + (L + s * s)))
  constructor <;> omega

/-- Explicit coordinate form of thermodynamic source-box protection. -/
theorem thermodynamic_explicitFace_protected
    (s L leftOffset x y z time : Nat) (plane : Z4Plane)
    (htime : time = 0)
    (hxLower : bulkSourceOffset s ≤ x)
    (hxUpper : x < bulkSourceOffset s + s)
    (hyLower : bulkSourceOffset s ≤ y)
    (hyUpper : y < bulkSourceOffset s + s)
    (hzLower : bulkSourceOffset s ≤ z)
    (hzUpper : z < bulkSourceOffset s + s)
    (hleftOffset : leftOffset ≤ L) :
    PlacementProtectedRoot
      (thermodynamicPlacement s L) (thermodynamicExteriorMargin s)
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        (thermodynamicPlacement s L) (s * s) leftOffset
        ((x, y, z, time), plane)) := by
  subst time
  intro direction
  cases direction with
  | x0 =>
      change (thermodynamicPlacement s L).space +
          thermodynamicExteriorMargin s ≤
            x + (thermodynamicPlacement s L).space ∧
        x + (thermodynamicPlacement s L).space +
              thermodynamicExteriorMargin s ≤
          (thermodynamicPlacement s L).space +
            (thermodynamicPlacement s L).source
      exact thermodynamicSpatialProtection s L x hxLower hxUpper
  | x1 =>
      change (thermodynamicPlacement s L).space +
          thermodynamicExteriorMargin s ≤
            y + (thermodynamicPlacement s L).space ∧
        y + (thermodynamicPlacement s L).space +
              thermodynamicExteriorMargin s ≤
          (thermodynamicPlacement s L).space +
            (thermodynamicPlacement s L).source
      exact thermodynamicSpatialProtection s L y hyLower hyUpper
  | x2 =>
      change (thermodynamicPlacement s L).space +
          thermodynamicExteriorMargin s ≤
            z + (thermodynamicPlacement s L).space ∧
        z + (thermodynamicPlacement s L).space +
              thermodynamicExteriorMargin s ≤
          (thermodynamicPlacement s L).space +
            (thermodynamicPlacement s L).source
      exact thermodynamicSpatialProtection s L z hzLower hzUpper
  | x3 =>
      change (thermodynamicPlacement s L).time +
          thermodynamicExteriorMargin s ≤
            0 + (s * s + leftOffset) +
              (thermodynamicPlacement s L).time ∧
        0 + (s * s + leftOffset) +
              (thermodynamicPlacement s L).time +
              thermodynamicExteriorMargin s ≤
          (thermodynamicPlacement s L).time +
            (thermodynamicPlacement s L).source
      exact thermodynamicTimeProtection s L leftOffset hleftOffset

/-- The translated left coordinate-carrier root is protected by the complete
source box at the explicit thermodynamic placement. -/
theorem thermodynamic_leftFace_protected
    (s L leftOffset : Nat) (leftFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) :
    PlacementProtectedRoot
      (thermodynamicPlacement s L) (thermodynamicExteriorMargin s)
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        (thermodynamicPlacement s L) (s * s) leftOffset leftFace) := by
  obtain ⟨⟨x, y, z, time⟩, plane⟩ := leftFace
  have hcharacterization :=
    (bulkSourceFaces_mem_iff s
      (((x, y, z, time), plane) : Z4Plaq)).mp hleftFace
  have hbase := hcharacterization.2
  unfold BulkSourceBase at hbase
  dsimp only at hbase
  obtain ⟨hxLower, hxUpper, hyLower, hyUpper, hzLower, hzUpper⟩ :=
    hbase
  have htime :=
    ((internalOpenCubeFaces_mem_iff (bulkSourceWidth s) _).mp
      hcharacterization.1).1
  exact thermodynamic_explicitFace_protected s L leftOffset x y z time
    plane htime hxLower hxUpper hyLower hyUpper hzLower hzUpper hleftOffset

/-- Every omitted thermodynamic target face is separated from the coordinate
carrier root by the explicit protected quadratic collar. -/
theorem thermodynamic_coordinateCarrier_exterior_linfDist_ge
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L)
    {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
    (homitted : id ∉ thermodynamicSelectedIds s L) :
    thermodynamicExteriorMargin s ≤
      linfDist
        (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
          (thermodynamicPlacement s L) (s * s) leftOffset rightOffset
          leftFace rightFace).animal.root
        (slabPlaquetteAt (thermodynamicPlacement s L).target id) := by
  change thermodynamicExteriorMargin s ≤
    linfDist
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
      (slabPlaquetteAt (thermodynamicPlacement s L).target id)
  by_cases hdist : thermodynamicExteriorMargin s ≤
      linfDist
        (translatedOriginalBulkVectorQuadraticJetPlacedFace
          (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
        (slabPlaquetteAt (thermodynamicPlacement s L).target id)
  · exact hdist
  · have hbox := near_PlacementProtectedRoot_sourceBox
      (thermodynamic_leftFace_protected
        s L leftOffset leftFace hleftFace hleftOffset)
      (Nat.lt_of_not_ge hdist)
    let sourceFace := unshiftPlacementFace (thermodynamicPlacement s L)
      (slabPlaquetteAt (thermodynamicPlacement s L).target id)
    have hsourcePhysical :
        sourceFace ∈ boundaryCompleteSlabPlaquettes
          (thermodynamicPlacement s L).source := by
      exact unshiftPlacementFace_physical hbox
    have hshift :
        shiftFace (thermodynamicPlacement s L).space
            (thermodynamicPlacement s L).time sourceFace =
          slabPlaquetteAt (thermodynamicPlacement s L).target id := by
      exact shift_unshiftPlacementFace hbox
    have hsourceExterior :
        ¬ originalBulkVectorQuadraticJetSourceWindow
          s (s * s) L sourceFace := by
      intro hsourceWindow
      apply homitted
      apply (selectedIds_mem_iff_translatedSourceWindow
        (thermodynamicPlacement s L) s (s * s) L rfl hid).mpr
      exact ⟨sourceFace, hsourceWindow, hshift.symm⟩
    have hsourceDist :=
      originalBulkVectorQuadraticJetPlacedFace_linfDist_ge_of_not_sourceWindow
        s (s * s) leftOffset L leftFace sourceFace
        hleftFace hleftOffset hsourceExterior
    have hmargin : thermodynamicExteriorMargin s ≤
        Nat.min (s * s)
          (originalBulkVectorQuadraticJetSpatialCollar s) := by
      apply Nat.le_min.mpr
      exact ⟨Nat.min_le_left _ _,
        Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)⟩
    have hshiftDist :
        linfDist
            (originalBulkVectorQuadraticJetPlacedFace
              (s * s) leftOffset leftFace)
            sourceFace =
          linfDist
            (translatedOriginalBulkVectorQuadraticJetPlacedFace
              (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
            (slabPlaquetteAt (thermodynamicPlacement s L).target id) := by
      rw [← linfDist_shiftFace
        (thermodynamicPlacement s L).space
        (thermodynamicPlacement s L).time]
      rw [hshift]
      rfl
    exact Nat.le_trans hmargin (Nat.le_trans hsourceDist
      (Nat.le_of_eq hshiftDist))

/-- Exact lower bound for the exponent in every thermodynamic exterior
one-face insertion budget. -/
theorem thermodynamic_coordinateCarrier_exterior_exponent_ge
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
    (homitted : id ∉ thermodynamicSelectedIds s L) :
    thermodynamicExteriorMargin s - (5 * s + 3 * L + 5) ≤
      linfDist
          (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
            (thermodynamicPlacement s L) (s * s) leftOffset rightOffset
            leftFace rightFace).animal.root
          (slabPlaquetteAt (thermodynamicPlacement s L).target id) -
        (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
          (thermodynamicPlacement s L) (s * s) leftOffset rightOffset
          leftFace rightFace).animal.support.length := by
  have hdist := thermodynamic_coordinateCarrier_exterior_linfDist_ge
    s L leftOffset rightOffset leftFace rightFace hleftFace hleftOffset
    hid homitted
  have hsupport :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier_support_length_le
      (thermodynamicPlacement s L) s (s * s) leftOffset rightOffset L
      leftFace rightFace hleftFace hrightFace hleftOffset hrightOffset
  omega

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.unshiftPlacementFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.selectedIds_mem_iff_translatedSourceWindow
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.near_PlacementProtectedRoot_sourceBox
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.thermodynamicSpatialProtection
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.thermodynamicTimeProtection
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.thermodynamic_explicitFace_protected
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.thermodynamic_leftFace_protected
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.thermodynamic_coordinateCarrier_exterior_linfDist_ge
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin.thermodynamic_coordinateCarrier_exterior_exponent_ge
