/-
# A left-basis-aligned diagonal two-cube cut carrier

The outward Y/Z carrier exposed a genuine basis obstruction: its two surface
components occur around the unique four-face pivot in cyclic order
`[far, near, near, far]`, so neither left-associated SU(2) carrier pairs
within both components.  Use instead the other diagonal pair of unit cubes:
the cube at the zero offset and the cube at offset `(0,1,1,0)`.

These two face-disjoint boundaries again meet only at
`((0,1,1,0), x0)`, but corrected-slab incident order is now
`[near, near, far, far, vacuum]`.  Hence the existing left carrier `(0,1)`,
whose physical pairing is `0 <-> 1` and `2 <-> 3`, is geometrically
component-preserving.  This module proves the complete finite cut geometry
and records that load-bearing order before any recoupling construction.

Constructive contract: ordinary finite reduction compiled to Type-valued
paths; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
import YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphWarshallPathDecision
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. The other diagonal pair around the same spatial link -/

def alignedDiagonalYZOffset : AxisOffset := ⟨0, 1, 1, 0⟩

def alignedDiagonalNearSurface : List Z4Plaq :=
  axisCubeSurface zeroAxisOffset

def alignedDiagonalFarSurface : List Z4Plaq :=
  axisCubeSurface alignedDiagonalYZOffset

def alignedDiagonalYZSurface : List Z4Plaq :=
  alignedDiagonalNearSurface ++ alignedDiagonalFarSurface

abbrev alignedDiagonalYZPivot : Z4Link := outwardYZCutPivot

def alignedDiagonalNearQueryFace : Z4Plaq :=
  axisShiftPlaquette zeroAxisOffset (cubeFace .leftYZ)

def alignedDiagonalFarQueryFace : Z4Plaq :=
  axisShiftPlaquette alignedDiagonalYZOffset (cubeFace .rightYZ)

theorem alignedDiagonalNearQueryFace_mem :
    alignedDiagonalNearQueryFace ∈ alignedDiagonalNearSurface := by
  decide

theorem alignedDiagonalFarQueryFace_mem :
    alignedDiagonalFarQueryFace ∈ alignedDiagonalFarSurface := by
  decide

theorem alignedDiagonalNearSurface_evenFaceIncidence :
    EvenFaceIncidence alignedDiagonalNearSurface :=
  axisShift_evenFaceIncidence zeroAxisOffset
    unitCubeSurface_evenFaceIncidence

theorem alignedDiagonalFarSurface_evenFaceIncidence :
    EvenFaceIncidence alignedDiagonalFarSurface :=
  axisShift_evenFaceIncidence alignedDiagonalYZOffset
    unitCubeSurface_evenFaceIncidence

theorem alignedDiagonalYZSurface_evenFaceIncidence :
    EvenFaceIncidence alignedDiagonalYZSurface :=
  evenFaceIncidence_append
    alignedDiagonalNearSurface_evenFaceIncidence
    alignedDiagonalFarSurface_evenFaceIncidence

theorem alignedDiagonalYZSurface_nodup :
    alignedDiagonalYZSurface.Nodup := by
  decide

/-! ## 2. Deleting the pivot gives exactly two connected sides -/

theorem alignedDiagonalNearSurface_away_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
      alignedDiagonalNearSurface = true := by
  decide

theorem alignedDiagonalFarSurface_away_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
      alignedDiagonalFarSurface = true := by
  decide

def alignedDiagonalNearSurface_connected_away :
    InternallyConnected
      (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
      alignedDiagonalNearSurface :=
  internallyConnectedOfAllPairsReachableB _ _
    alignedDiagonalNearSurface_away_allPairsReachable

def alignedDiagonalFarSurface_connected_away :
    InternallyConnected
      (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
      alignedDiagonalFarSurface :=
  internallyConnectedOfAllPairsReachableB _ _
    alignedDiagonalFarSurface_away_allPairsReachable

theorem alignedDiagonal_allCrossSharedLinksEqPivot :
    allCrossSharedLinksEqB alignedDiagonalNearSurface
      alignedDiagonalFarSurface alignedDiagonalYZPivot = true := by
  decide

theorem alignedDiagonal_crossSharedLink_eq_pivot
    {nearFace farFace : Z4Plaq} {link : Z4Link}
    (hnearFace : nearFace ∈ alignedDiagonalNearSurface)
    (hfarFace : farFace ∈ alignedDiagonalFarSurface)
    (hnearLink : link ∈ edgesOf nearFace)
    (hfarLink : link ∈ edgesOf farFace) :
    link = alignedDiagonalYZPivot := by
  have hnearRow := List.all_eq_true.mp
    alignedDiagonal_allCrossSharedLinksEqPivot nearFace hnearFace
  have hfarRow := List.all_eq_true.mp hnearRow farFace hfarFace
  have hlinkRow := List.all_eq_true.mp hfarRow link hnearLink
  simp [hfarLink] at hlinkRow
  exact hlinkRow

theorem alignedDiagonal_noCrossAdjacencyAway :
    SupportsSeparated
      (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
      alignedDiagonalNearSurface alignedDiagonalFarSurface := by
  intro nearFace hnearFace farFace hfarFace
  unfold z4FaceAdjacentAwayB
  apply List.any_eq_false.mpr
  intro link hnearLink
  by_cases hfarLink : link ∈ edgesOf farFace
  · have hpivot := alignedDiagonal_crossSharedLink_eq_pivot
      hnearFace hfarFace hnearLink hfarLink
    simp [hpivot]
  · simp [hfarLink]

theorem alignedDiagonal_markedFaces_not_reachable_away :
    finiteSupportReachableB
      (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
      alignedDiagonalYZSurface alignedDiagonalNearQueryFace
        alignedDiagonalFarQueryFace = false := by
  decide

def alignedDiagonal_noMarkedFaceChain_away :
    ChainIn
      (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
      alignedDiagonalYZSurface alignedDiagonalNearQueryFace
        alignedDiagonalFarQueryFace -> False :=
  noChainInOfFiniteSupportReachableBFalse _ _
    alignedDiagonal_markedFaces_not_reachable_away

/-! ## 3. Unique four-incidence profile -/

private theorem faceIncidenceCount_eq_zero_of_not_touched
    (link : Z4Link) : forall support : List Z4Plaq,
    link ∉ geometricTouchedLinks support ->
      faceIncidenceCount link support = 0
  | [], _ => rfl
  | plaquette :: rest, hnot => by
      have hhead : link ∉ edgesOf plaquette := by
        intro hedge
        exact hnot (mem_geometricTouchedLinks.mpr
          ⟨plaquette, List.mem_cons_self, hedge⟩)
      have htail : link ∉ geometricTouchedLinks rest := by
        intro hrest
        obtain ⟨face, hface, hedge⟩ := mem_geometricTouchedLinks.mp hrest
        exact hnot (mem_geometricTouchedLinks.mpr
          ⟨face, List.mem_cons_of_mem plaquette hface, hedge⟩)
      simp only [faceIncidenceCount, hhead, if_false, Nat.zero_add]
      exact faceIncidenceCount_eq_zero_of_not_touched link rest htail

theorem alignedDiagonal_singleFourIncidenceProfile_checked :
    singleFourIncidenceProfileB
      alignedDiagonalYZSurface alignedDiagonalYZPivot = true := by
  decide

theorem alignedDiagonalPivot_faceIncidenceCount :
    faceIncidenceCount alignedDiagonalYZPivot
      alignedDiagonalYZSurface = 4 := by
  exact (Bool.and_eq_true _ _).mp
    alignedDiagonal_singleFourIncidenceProfile_checked |>.1 |> of_decide_eq_true

theorem alignedDiagonal_other_faceIncidenceCount_le_two
    (link : Z4Link) (hne : link ≠ alignedDiagonalYZPivot) :
    faceIncidenceCount link alignedDiagonalYZSurface ≤ 2 := by
  by_cases htouched : link ∈ geometricTouchedLinks alignedDiagonalYZSurface
  · have hall := (Bool.and_eq_true _ _).mp
      alignedDiagonal_singleFourIncidenceProfile_checked |>.2
    have hrow := List.all_eq_true.mp hall link htouched
    have hpivotFalse : decide (link = alignedDiagonalYZPivot) = false := by
      simp [hne]
    rw [hpivotFalse, Bool.false_or] at hrow
    exact of_decide_eq_true hrow
  · rw [faceIncidenceCount_eq_zero_of_not_touched
      link alignedDiagonalYZSurface htouched]
    omega

/-! ## 4. The load-bearing left-basis incident order -/

def alignedDiagonalComponentTag (faceId : Nat) : Nat :=
  if slabPlaquetteAt 5 faceId ∈ alignedDiagonalNearSurface then 1
  else if slabPlaquetteAt 5 faceId ∈ alignedDiagonalFarSurface then 2
  else 0

theorem alignedDiagonalPivot_componentTagList :
    (slabIncidentPlaqIds 5 alignedDiagonalYZPivot).map
        alignedDiagonalComponentTag = [1, 1, 2, 2, 0] := by
  decide

structure AlignedDiagonalYZCutCarrierCertificate : Type where
  nearConnected : InternallyConnected
    (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
    alignedDiagonalNearSurface
  farConnected : InternallyConnected
    (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
    alignedDiagonalFarSurface
  crossSeparated : SupportsSeparated
    (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
    alignedDiagonalNearSurface alignedDiagonalFarSurface
  markedSeparated : ChainIn
    (z4FaceAdjacentAwayB alignedDiagonalYZPivot)
    alignedDiagonalYZSurface alignedDiagonalNearQueryFace
      alignedDiagonalFarQueryFace -> False
  pivotIncidence : faceIncidenceCount alignedDiagonalYZPivot
    alignedDiagonalYZSurface = 4
  otherIncidence : forall link, link ≠ alignedDiagonalYZPivot ->
    faceIncidenceCount link alignedDiagonalYZSurface ≤ 2
  leftBasisOrder : (slabIncidentPlaqIds 5 alignedDiagonalYZPivot).map
    alignedDiagonalComponentTag = [1, 1, 2, 2, 0]

def alignedDiagonalYZCutCarrierCertificate :
    AlignedDiagonalYZCutCarrierCertificate :=
  { nearConnected := alignedDiagonalNearSurface_connected_away
    farConnected := alignedDiagonalFarSurface_connected_away
    crossSeparated := alignedDiagonal_noCrossAdjacencyAway
    markedSeparated := alignedDiagonal_noMarkedFaceChain_away
    pivotIncidence := alignedDiagonalPivot_faceIncidenceCount
    otherIncidence := alignedDiagonal_other_faceIncidenceCount_le_two
    leftBasisOrder := alignedDiagonalPivot_componentTagList }

#print axioms alignedDiagonalNearSurface_connected_away
#print axioms alignedDiagonalFarSurface_connected_away
#print axioms alignedDiagonal_crossSharedLink_eq_pivot
#print axioms alignedDiagonal_noMarkedFaceChain_away
#print axioms alignedDiagonalPivot_faceIncidenceCount
#print axioms alignedDiagonal_other_faceIncidenceCount_le_two
#print axioms alignedDiagonalPivot_componentTagList
#print axioms alignedDiagonalYZCutCarrierCertificate

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
