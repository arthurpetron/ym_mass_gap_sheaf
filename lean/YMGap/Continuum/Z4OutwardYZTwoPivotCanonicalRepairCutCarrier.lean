/-
# A same-marked-face two-pivot repair carrier for outward Y/Z

The outward Y/Z marked plaquettes themselves share the spatial link
`((0,1,1,0),x0)`.  The original two cube boundaries meet there in the side
order `Z,Y,Y,Z`, which obstructs every canonical-left local carrier.

This module constructs two different closed lobes with the same marked faces.
The target lobe is the boundary of a two-cell x-y-t bar at fixed z=1.  The
root lobe is the boundary of an explicit six-cell x-z-t animal at fixed y=1.
They are face-disjoint and share exactly two links: the marked spatial pivot
and the temporal link from the same vertex.  At the spatial pivot their four
faces occur in alternating order, so the canonical-left pairing
`0 <-> 2`, `1 <-> 3` stays inside the two lobes.

This file establishes only the finite cut geometry.  The two local SU(2)
carriers and their global positive row are subsequent compilers.

Constructive contract: literal finite cubical boundaries and sound Boolean
connectivity checks only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
import YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate
import YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphWarshallPathDecision
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. Two explicit closed cubical lobes -/

/-- Boundary of the x-y-t two-cell bar at z=1.  Its two t=0 x-y faces are
the target-side positions zero and two at the marked pivot. -/
def outwardYZCanonicalRepairTargetLobe : List Z4Plaq :=
  [((1, 0, 1, 0), .p13),
   ((1, 1, 1, 0), .p13),
   ((0, 2, 1, 0), .p03),
   ((0, 1, 1, 0), .p01),
   ((0, 1, 1, 0), .p13),
   ((0, 1, 1, 1), .p01),
   ((0, 0, 1, 1), .p01),
   ((0, 0, 1, 0), .p13),
   ((0, 0, 1, 0), .p03),
   ((0, 0, 1, 0), .p01)]

/-- Boundary of a six-cell x-z-t animal at y=1.  Its two t=0 x-z faces are
the root-side positions one and three at the marked pivot. -/
def outwardYZCanonicalRepairRootLobe : List Z4Plaq :=
  [((2, 1, 0, 0), .p23),
   ((2, 1, 1, 0), .p23),
   ((1, 1, 1, 1), .p02),
   ((1, 1, 2, 0), .p03),
   ((1, 1, 1, 0), .p02),
   ((1, 1, 0, 0), .p02),
   ((1, 1, 0, 0), .p03),
   ((1, 1, 0, 1), .p02),
   ((1, 1, 0, 1), .p23),
   ((1, 1, 1, 1), .p23),
   ((0, 1, 2, 1), .p03),
   ((0, 1, 2, 0), .p03),
   ((0, 1, 1, 0), .p02),
   ((0, 1, 1, 0), .p23),
   ((0, 1, 1, 1), .p23),
   ((0, 1, 1, 2), .p02),
   ((0, 1, 0, 2), .p02),
   ((0, 1, 0, 1), .p03),
   ((0, 1, 0, 1), .p23),
   ((0, 1, 0, 0), .p23),
   ((0, 1, 0, 0), .p03),
   ((0, 1, 0, 0), .p02)]

def outwardYZCanonicalRepairSurface : List Z4Plaq :=
  outwardYZCanonicalRepairTargetLobe ++
    outwardYZCanonicalRepairRootLobe

abbrev outwardYZCanonicalRepairSpatialPivot : Z4Link :=
  outwardYZCutPivot

abbrev outwardYZCanonicalRepairTemporalPivot : Z4Link :=
  ((0, 1, 1, 0), .x3)

theorem outwardYZCanonicalRepairTarget_mem_targetLobe :
    outwardZQueryFace ∈ outwardYZCanonicalRepairTargetLobe := by
  decide

theorem outwardYZCanonicalRepairRoot_mem_rootLobe :
    outwardYQueryFace ∈ outwardYZCanonicalRepairRootLobe := by
  decide

theorem outwardYZCanonicalRepairTargetLobe_nodup :
    outwardYZCanonicalRepairTargetLobe.Nodup := by
  decide

theorem outwardYZCanonicalRepairRootLobe_nodup :
    outwardYZCanonicalRepairRootLobe.Nodup := by
  decide

theorem outwardYZCanonicalRepairSurface_nodup :
    outwardYZCanonicalRepairSurface.Nodup := by
  decide

theorem outwardYZCanonicalRepairSurface_subset_slab_five :
    ∀ plaquette, plaquette ∈ outwardYZCanonicalRepairSurface →
      plaquette ∈ boundaryCompleteSlabPlaquettes 5 := by
  decide

theorem outwardYZCanonicalRepairTargetLobe_even :
    EvenFaceIncidence outwardYZCanonicalRepairTargetLobe :=
  evenFaceIncidenceCheck_sound _ (by decide)

theorem outwardYZCanonicalRepairRootLobe_even :
    EvenFaceIncidence outwardYZCanonicalRepairRootLobe :=
  evenFaceIncidenceCheck_sound _ (by decide)

theorem outwardYZCanonicalRepairSurface_even :
    EvenFaceIncidence outwardYZCanonicalRepairSurface :=
  evenFaceIncidence_append outwardYZCanonicalRepairTargetLobe_even
    outwardYZCanonicalRepairRootLobe_even

theorem outwardYZCanonicalRepairSurface_tailBridgeConnected :
    tailBridgeConnectedB outwardYZCanonicalRepairSurface = true := by
  decide

def outwardYZCanonicalRepairSurface_connected :
    connectedIn (L := z4Chain.toLattice)
      outwardYZCanonicalRepairSurface :=
  connectedIn_of_tailBridgeConnectedB outwardYZCanonicalRepairSurface
    outwardYZCanonicalRepairSurface_tailBridgeConnected

/-! ## 2. Exact two-link intersection and cut connectivity -/

def z4FaceAdjacentAwayTwoB (firstForbidden secondForbidden : Z4Link)
    (left right : Z4Plaq) : Bool :=
  (edgesOf left).any fun link =>
    decide (link != firstForbidden) &&
      decide (link != secondForbidden) && decide (link ∈ edgesOf right)

theorem outwardYZCanonicalRepairTargetLobe_away_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
        outwardYZCanonicalRepairTemporalPivot)
      outwardYZCanonicalRepairTargetLobe = true := by
  decide

theorem outwardYZCanonicalRepairRootLobe_away_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
        outwardYZCanonicalRepairTemporalPivot)
      outwardYZCanonicalRepairRootLobe = true := by
  decide

def outwardYZCanonicalRepairTargetLobe_connected_away :
    InternallyConnected
      (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
        outwardYZCanonicalRepairTemporalPivot)
      outwardYZCanonicalRepairTargetLobe :=
  internallyConnectedOfAllPairsReachableB _ _
    outwardYZCanonicalRepairTargetLobe_away_allPairsReachable

def outwardYZCanonicalRepairRootLobe_connected_away :
    InternallyConnected
      (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
        outwardYZCanonicalRepairTemporalPivot)
      outwardYZCanonicalRepairRootLobe :=
  internallyConnectedOfAllPairsReachableB _ _
    outwardYZCanonicalRepairRootLobe_away_allPairsReachable

def allCrossSharedLinksInB (left right : List Z4Plaq)
    (allowed : List Z4Link) : Bool :=
  left.all fun leftFace =>
    right.all fun rightFace =>
      (edgesOf leftFace).all fun link =>
        if link ∈ edgesOf rightFace then decide (link ∈ allowed)
        else true

theorem outwardYZCanonicalRepair_allCrossSharedLinksIn_two :
    allCrossSharedLinksInB outwardYZCanonicalRepairTargetLobe
      outwardYZCanonicalRepairRootLobe
      [outwardYZCanonicalRepairSpatialPivot,
       outwardYZCanonicalRepairTemporalPivot] = true := by
  decide

theorem outwardYZCanonicalRepair_crossSharedLink_mem_pivots
    {targetFace rootFace : Z4Plaq} {link : Z4Link}
    (htargetFace : targetFace ∈ outwardYZCanonicalRepairTargetLobe)
    (hrootFace : rootFace ∈ outwardYZCanonicalRepairRootLobe)
    (htargetLink : link ∈ edgesOf targetFace)
    (hrootLink : link ∈ edgesOf rootFace) :
    link ∈ [outwardYZCanonicalRepairSpatialPivot,
      outwardYZCanonicalRepairTemporalPivot] := by
  have htargetRow := List.all_eq_true.mp
    outwardYZCanonicalRepair_allCrossSharedLinksIn_two
      targetFace htargetFace
  have hrootRow := List.all_eq_true.mp htargetRow rootFace hrootFace
  have hlinkRow := List.all_eq_true.mp hrootRow link htargetLink
  simp [hrootLink] at hlinkRow
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hlinkRow

theorem outwardYZCanonicalRepairSpatialPivot_is_shared :
    outwardYZCanonicalRepairSpatialPivot ∈
        edgesOf ((0, 1, 1, 0), .p01) ∧
      outwardYZCanonicalRepairSpatialPivot ∈
        edgesOf ((0, 1, 1, 0), .p02) := by
  decide

theorem outwardYZCanonicalRepairTemporalPivot_is_shared :
    outwardYZCanonicalRepairTemporalPivot ∈
        edgesOf ((0, 1, 1, 0), .p13) ∧
      outwardYZCanonicalRepairTemporalPivot ∈
        edgesOf ((0, 1, 1, 0), .p23) := by
  decide

theorem outwardYZCanonicalRepair_noCrossAdjacencyAway :
    SupportsSeparated
      (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
        outwardYZCanonicalRepairTemporalPivot)
      outwardYZCanonicalRepairTargetLobe
      outwardYZCanonicalRepairRootLobe := by
  intro targetFace htargetFace rootFace hrootFace
  unfold z4FaceAdjacentAwayTwoB
  apply List.any_eq_false.mpr
  intro link htargetLink
  by_cases hrootLink : link ∈ edgesOf rootFace
  · have hpivots := outwardYZCanonicalRepair_crossSharedLink_mem_pivots
      htargetFace hrootFace htargetLink hrootLink
    have hpivots' :
        link = outwardYZCanonicalRepairSpatialPivot ∨
          link = outwardYZCanonicalRepairTemporalPivot := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpivots
    rcases hpivots' with hspatial | htemporal
    · subst link
      simp
    · subst link
      simp
  · simp [hrootLink]

theorem outwardYZCanonicalRepair_markedFaces_not_reachable_away :
    finiteSupportReachableB
      (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
        outwardYZCanonicalRepairTemporalPivot)
      outwardYZCanonicalRepairSurface outwardYQueryFace
        outwardZQueryFace = false := by
  decide

def outwardYZCanonicalRepair_noMarkedFaceChain_away :
    ChainIn
      (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
        outwardYZCanonicalRepairTemporalPivot)
      outwardYZCanonicalRepairSurface outwardYQueryFace
        outwardZQueryFace → False :=
  noChainInOfFiniteSupportReachableBFalse _ _
    outwardYZCanonicalRepair_markedFaces_not_reachable_away

/-! ## 3. The two local side words -/

def outwardYZCanonicalRepairSideCode (plaquette : Z4Plaq) : Nat :=
  if plaquette ∈ outwardYZCanonicalRepairTargetLobe then 1
  else if plaquette ∈ outwardYZCanonicalRepairRootLobe then 2
  else 0

def outwardYZCanonicalRepairSpatialSideWord : List Nat :=
  (slabIncidentPlaqIds 5 outwardYZCanonicalRepairSpatialPivot).map
    fun faceId => outwardYZCanonicalRepairSideCode
      (slabPlaquetteAt 5 faceId)

def outwardYZCanonicalRepairTemporalSideWord : List Nat :=
  (slabIncidentPlaqIds 5 outwardYZCanonicalRepairTemporalPivot).map
    fun faceId => outwardYZCanonicalRepairSideCode
      (slabPlaquetteAt 5 faceId)

theorem outwardYZCanonicalRepairSpatialSideWord_exact :
    outwardYZCanonicalRepairSpatialSideWord = [1, 2, 1, 2, 0] := by
  decide

theorem outwardYZCanonicalRepairTemporalSideWord_exact :
    outwardYZCanonicalRepairTemporalSideWord = [1, 2, 0, 1, 2] := by
  decide

/-! ## 4. Exact two-four/all-other-two incidence profile -/

def doubleFourIncidenceProfileB
    (support : List Z4Plaq) (firstPivot secondPivot : Z4Link) : Bool :=
  decide (faceIncidenceCount firstPivot support = 4) &&
    decide (faceIncidenceCount secondPivot support = 4) &&
    (geometricTouchedLinks support).all fun link =>
      decide (link = firstPivot) || decide (link = secondPivot) ||
        decide (faceIncidenceCount link support ≤ 2)

theorem outwardYZCanonicalRepair_doubleFourIncidenceProfile_checked :
    doubleFourIncidenceProfileB outwardYZCanonicalRepairSurface
      outwardYZCanonicalRepairSpatialPivot
      outwardYZCanonicalRepairTemporalPivot = true := by
  decide

theorem outwardYZCanonicalRepairSpatialPivot_faceIncidenceCount :
    faceIncidenceCount outwardYZCanonicalRepairSpatialPivot
      outwardYZCanonicalRepairSurface = 4 := by
  exact (Bool.and_eq_true _ _).mp
    outwardYZCanonicalRepair_doubleFourIncidenceProfile_checked |>.1
      |> of_decide_eq_true

theorem outwardYZCanonicalRepairTemporalPivot_faceIncidenceCount :
    faceIncidenceCount outwardYZCanonicalRepairTemporalPivot
      outwardYZCanonicalRepairSurface = 4 := by
  have htail := (Bool.and_eq_true _ _).mp
    outwardYZCanonicalRepair_doubleFourIncidenceProfile_checked |>.2
  exact (Bool.and_eq_true _ _).mp htail |>.1 |> of_decide_eq_true

private theorem faceIncidenceCount_eq_zero_of_not_touched
    (link : Z4Link) : ∀ support : List Z4Plaq,
    link ∉ geometricTouchedLinks support →
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

theorem outwardYZCanonicalRepair_other_faceIncidenceCount_le_two
    (link : Z4Link)
    (hneSpatial : link ≠ outwardYZCanonicalRepairSpatialPivot)
    (hneTemporal : link ≠ outwardYZCanonicalRepairTemporalPivot) :
    faceIncidenceCount link outwardYZCanonicalRepairSurface ≤ 2 := by
  by_cases htouched :
      link ∈ geometricTouchedLinks outwardYZCanonicalRepairSurface
  · have hall :
        (geometricTouchedLinks outwardYZCanonicalRepairSurface).all
          (fun touched =>
            decide (touched = outwardYZCanonicalRepairSpatialPivot) ||
              decide (touched = outwardYZCanonicalRepairTemporalPivot) ||
                decide (faceIncidenceCount touched
                  outwardYZCanonicalRepairSurface ≤ 2)) = true := by
      have htail := (Bool.and_eq_true _ _).mp
        outwardYZCanonicalRepair_doubleFourIncidenceProfile_checked |>.2
      exact (Bool.and_eq_true _ _).mp htail |>.2
    have hrow := List.all_eq_true.mp hall link htouched
    have hfirstFalse :
        decide (link = outwardYZCanonicalRepairSpatialPivot) = false := by
      simp [hneSpatial]
    have hsecondFalse :
        decide (link = outwardYZCanonicalRepairTemporalPivot) = false := by
      simp [hneTemporal]
    rw [hfirstFalse, Bool.false_or, hsecondFalse, Bool.false_or] at hrow
    exact of_decide_eq_true hrow
  · rw [faceIncidenceCount_eq_zero_of_not_touched
      link outwardYZCanonicalRepairSurface htouched]
    omega

/-- Complete finite geometry of the two-pivot repair surface. -/
structure OutwardYZTwoPivotCanonicalRepairCutCertificate : Type where
  supportConnected : connectedIn (L := z4Chain.toLattice)
    outwardYZCanonicalRepairSurface
  targetConnectedAway : InternallyConnected
    (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
      outwardYZCanonicalRepairTemporalPivot)
    outwardYZCanonicalRepairTargetLobe
  rootConnectedAway : InternallyConnected
    (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
      outwardYZCanonicalRepairTemporalPivot)
    outwardYZCanonicalRepairRootLobe
  crossSeparated : SupportsSeparated
    (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
      outwardYZCanonicalRepairTemporalPivot)
    outwardYZCanonicalRepairTargetLobe
    outwardYZCanonicalRepairRootLobe
  markedSeparated : ChainIn
    (z4FaceAdjacentAwayTwoB outwardYZCanonicalRepairSpatialPivot
      outwardYZCanonicalRepairTemporalPivot)
    outwardYZCanonicalRepairSurface outwardYQueryFace
      outwardZQueryFace → False
  crossContactsOnlyAtPivots : ∀ {targetFace rootFace : Z4Plaq}
      {link : Z4Link},
    targetFace ∈ outwardYZCanonicalRepairTargetLobe →
    rootFace ∈ outwardYZCanonicalRepairRootLobe →
    link ∈ edgesOf targetFace → link ∈ edgesOf rootFace →
    link ∈ [outwardYZCanonicalRepairSpatialPivot,
      outwardYZCanonicalRepairTemporalPivot]
  spatialIncidence : faceIncidenceCount
    outwardYZCanonicalRepairSpatialPivot
      outwardYZCanonicalRepairSurface = 4
  temporalIncidence : faceIncidenceCount
    outwardYZCanonicalRepairTemporalPivot
      outwardYZCanonicalRepairSurface = 4
  otherIncidence : ∀ link,
    link ≠ outwardYZCanonicalRepairSpatialPivot →
    link ≠ outwardYZCanonicalRepairTemporalPivot →
    faceIncidenceCount link outwardYZCanonicalRepairSurface ≤ 2
  spatialOrder : outwardYZCanonicalRepairSpatialSideWord =
    [1, 2, 1, 2, 0]
  temporalOrder : outwardYZCanonicalRepairTemporalSideWord =
    [1, 2, 0, 1, 2]

def outwardYZTwoPivotCanonicalRepairCutCertificate :
    OutwardYZTwoPivotCanonicalRepairCutCertificate :=
  { supportConnected := outwardYZCanonicalRepairSurface_connected
    targetConnectedAway := outwardYZCanonicalRepairTargetLobe_connected_away
    rootConnectedAway := outwardYZCanonicalRepairRootLobe_connected_away
    crossSeparated := outwardYZCanonicalRepair_noCrossAdjacencyAway
    markedSeparated := outwardYZCanonicalRepair_noMarkedFaceChain_away
    crossContactsOnlyAtPivots :=
      outwardYZCanonicalRepair_crossSharedLink_mem_pivots
    spatialIncidence :=
      outwardYZCanonicalRepairSpatialPivot_faceIncidenceCount
    temporalIncidence :=
      outwardYZCanonicalRepairTemporalPivot_faceIncidenceCount
    otherIncidence :=
      outwardYZCanonicalRepair_other_faceIncidenceCount_le_two
    spatialOrder := outwardYZCanonicalRepairSpatialSideWord_exact
    temporalOrder := outwardYZCanonicalRepairTemporalSideWord_exact }

#print axioms outwardYZCanonicalRepairSurface_even
#print axioms outwardYZCanonicalRepairSurface_connected
#print axioms outwardYZCanonicalRepairTargetLobe_connected_away
#print axioms outwardYZCanonicalRepairRootLobe_connected_away
#print axioms outwardYZCanonicalRepair_crossSharedLink_mem_pivots
#print axioms outwardYZCanonicalRepair_noCrossAdjacencyAway
#print axioms outwardYZCanonicalRepair_noMarkedFaceChain_away
#print axioms outwardYZCanonicalRepairSpatialSideWord_exact
#print axioms outwardYZCanonicalRepairTemporalSideWord_exact
#print axioms outwardYZCanonicalRepair_other_faceIncidenceCount_le_two
#print axioms outwardYZTwoPivotCanonicalRepairCutCertificate

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
