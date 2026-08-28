/-
# A reflected two-lobe cut with one ordinary and one bent cube boundary

At extent five, put one spatial unit-cube boundary at time two.  The second
lobe is the boundary of a bent two-cell animal: a spatial unit cube at time
three glued along one face to a temporal x-z-t unit cube reaching down to
time two.  The two closed plaquette supports are disjoint and share exactly
one link.

The marked top x-y face of the first lobe is reflected by half-time
reflection to the marked bottom x-y face of the second.  Removing the shared
pivot leaves two internally connected lobes, and every nonpivot support link
has incidence at most two.  This is the reflected geometric input for the
same local switching construction used by the aligned spatial witness.

Constructive contract: literal finite plaquette lists, sound finite closure
and reachability checkers, and exact incidence computation only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, noncomputable declaration,
or unbounded heartbeat option.
-/

import YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
import YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphWarshallPathDecision
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. Literal reflected lobes -/

def reflectedBentNearSurface : List Z4Plaq :=
  [((0, 0, 0, 2), .p12), ((1, 0, 0, 2), .p12),
   ((0, 1, 0, 2), .p02), ((0, 0, 0, 2), .p01),
   ((0, 0, 0, 2), .p02), ((0, 0, 1, 2), .p01)]

/-- Boundary of the spatial cell at `(0,0,1,3)` glued to the temporal
x-z-t cell at `(0,0,1,2)`, with their common p02 face cancelled. -/
def reflectedBentFarSurface : List Z4Plaq :=
  [((0, 0, 2, 3), .p01), ((0, 0, 1, 2), .p02),
   ((1, 0, 1, 2), .p23), ((0, 0, 2, 2), .p03),
   ((0, 0, 1, 2), .p23), ((0, 0, 1, 2), .p03),
   ((0, 0, 1, 3), .p01), ((1, 0, 1, 3), .p12),
   ((0, 1, 1, 3), .p02), ((0, 0, 1, 3), .p12)]

def reflectedBentSwitchSurface : List Z4Plaq :=
  reflectedBentNearSurface ++ reflectedBentFarSurface

def reflectedBentRootPlaquette : Z4Plaq :=
  ((0, 0, 1, 2), .p01)

def reflectedBentTargetPlaquette : Z4Plaq :=
  ((0, 0, 1, 3), .p01)

abbrev reflectedBentPivot : Z4Link :=
  ((0, 0, 1, 2), .x0)

theorem reflectedBentTarget_reflects_root :
    timeReflectPlaquette 5 reflectedBentRootPlaquette =
      reflectedBentTargetPlaquette := by
  rfl

theorem reflectedBentRoot_mem :
    reflectedBentRootPlaquette ∈ reflectedBentNearSurface := by
  decide

theorem reflectedBentTarget_mem :
    reflectedBentTargetPlaquette ∈ reflectedBentFarSurface := by
  decide

theorem reflectedBentNearSurface_nodup :
    reflectedBentNearSurface.Nodup := by
  decide

theorem reflectedBentFarSurface_nodup :
    reflectedBentFarSurface.Nodup := by
  decide

theorem reflectedBentSwitchSurface_nodup :
    reflectedBentSwitchSurface.Nodup := by
  decide

theorem reflectedBentSwitchSurface_subset_slab_five :
    ∀ plaquette, plaquette ∈ reflectedBentSwitchSurface →
      plaquette ∈ boundaryCompleteSlabPlaquettes 5 := by
  decide

theorem reflectedBentNearSurface_evenFaceIncidence :
    EvenFaceIncidence reflectedBentNearSurface :=
  evenFaceIncidenceCheck_sound reflectedBentNearSurface (by decide)

theorem reflectedBentFarSurface_evenFaceIncidence :
    EvenFaceIncidence reflectedBentFarSurface :=
  evenFaceIncidenceCheck_sound reflectedBentFarSurface (by decide)

theorem reflectedBentSwitchSurface_evenFaceIncidence :
    EvenFaceIncidence reflectedBentSwitchSurface :=
  evenFaceIncidenceCheck_sound reflectedBentSwitchSurface (by decide)

theorem reflectedBentSwitchSurface_tailBridgeConnected :
    tailBridgeConnectedB reflectedBentSwitchSurface = true := by
  decide

def reflectedBentSwitchSurface_connected :
    connectedIn (L := z4Chain.toLattice)
      reflectedBentSwitchSurface :=
  connectedIn_of_tailBridgeConnectedB reflectedBentSwitchSurface
    reflectedBentSwitchSurface_tailBridgeConnected

/-! ## 2. The pivot separates the two connected lobes -/

theorem reflectedBentNearSurface_away_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayB reflectedBentPivot)
      reflectedBentNearSurface = true := by
  decide

theorem reflectedBentFarSurface_away_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayB reflectedBentPivot)
      reflectedBentFarSurface = true := by
  decide

def reflectedBentNearSurface_connected_away :
    InternallyConnected
      (z4FaceAdjacentAwayB reflectedBentPivot)
      reflectedBentNearSurface :=
  internallyConnectedOfAllPairsReachableB _ _
    reflectedBentNearSurface_away_allPairsReachable

def reflectedBentFarSurface_connected_away :
    InternallyConnected
      (z4FaceAdjacentAwayB reflectedBentPivot)
      reflectedBentFarSurface :=
  internallyConnectedOfAllPairsReachableB _ _
    reflectedBentFarSurface_away_allPairsReachable

theorem reflectedBent_allCrossSharedLinksEqPivot :
    allCrossSharedLinksEqB reflectedBentNearSurface
      reflectedBentFarSurface reflectedBentPivot = true := by
  decide

theorem reflectedBent_crossSharedLink_eq_pivot
    {nearFace farFace : Z4Plaq} {link : Z4Link}
    (hnearFace : nearFace ∈ reflectedBentNearSurface)
    (hfarFace : farFace ∈ reflectedBentFarSurface)
    (hnearLink : link ∈ edgesOf nearFace)
    (hfarLink : link ∈ edgesOf farFace) :
    link = reflectedBentPivot := by
  have hnearRow := List.all_eq_true.mp
    reflectedBent_allCrossSharedLinksEqPivot nearFace hnearFace
  have hfarRow := List.all_eq_true.mp hnearRow farFace hfarFace
  have hlinkRow := List.all_eq_true.mp hfarRow link hnearLink
  simp [hfarLink] at hlinkRow
  exact hlinkRow

theorem reflectedBent_noCrossAdjacencyAway :
    SupportsSeparated
      (z4FaceAdjacentAwayB reflectedBentPivot)
      reflectedBentNearSurface reflectedBentFarSurface := by
  intro nearFace hnearFace farFace hfarFace
  unfold z4FaceAdjacentAwayB
  apply List.any_eq_false.mpr
  intro link hnearLink
  by_cases hfarLink : link ∈ edgesOf farFace
  · have hpivot := reflectedBent_crossSharedLink_eq_pivot
      hnearFace hfarFace hnearLink hfarLink
    simp [hpivot]
  · simp [hfarLink]

theorem reflectedBent_markedFaces_not_reachable_away :
    finiteSupportReachableB
      (z4FaceAdjacentAwayB reflectedBentPivot)
      reflectedBentSwitchSurface reflectedBentRootPlaquette
        reflectedBentTargetPlaquette = false := by
  decide

def reflectedBent_noMarkedFaceChain_away :
    ChainIn
      (z4FaceAdjacentAwayB reflectedBentPivot)
      reflectedBentSwitchSurface reflectedBentRootPlaquette
        reflectedBentTargetPlaquette → False :=
  noChainInOfFiniteSupportReachableBFalse _ _
    reflectedBent_markedFaces_not_reachable_away

/-! ## 3. Unique four-incidence profile and slab order -/

theorem reflectedBent_singleFourIncidenceProfile_checked :
    singleFourIncidenceProfileB
      reflectedBentSwitchSurface reflectedBentPivot = true := by
  decide

theorem reflectedBentPivot_faceIncidenceCount :
    faceIncidenceCount reflectedBentPivot
      reflectedBentSwitchSurface = 4 := by
  exact (Bool.and_eq_true _ _).mp
    reflectedBent_singleFourIncidenceProfile_checked |>.1 |> of_decide_eq_true

private theorem faceIncidenceCount_eq_zero_of_not_touched
    (link : Z4Link) : forall support : List Z4Plaq,
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

theorem reflectedBent_other_faceIncidenceCount_le_two
    (link : Z4Link) (hne : link ≠ reflectedBentPivot) :
    faceIncidenceCount link reflectedBentSwitchSurface ≤ 2 := by
  by_cases htouched : link ∈ geometricTouchedLinks reflectedBentSwitchSurface
  · have hall := (Bool.and_eq_true _ _).mp
      reflectedBent_singleFourIncidenceProfile_checked |>.2
    have hrow := List.all_eq_true.mp hall link htouched
    have hpivotFalse : decide (link = reflectedBentPivot) = false := by
      simp [hne]
    rw [hpivotFalse, Bool.false_or] at hrow
    exact of_decide_eq_true hrow
  · rw [faceIncidenceCount_eq_zero_of_not_touched
      link reflectedBentSwitchSurface htouched]
    omega

def reflectedBentComponentTag (faceId : Nat) : Nat :=
  if slabPlaquetteAt 5 faceId ∈ reflectedBentNearSurface then 1
  else if slabPlaquetteAt 5 faceId ∈ reflectedBentFarSurface then 2
  else 0

theorem reflectedBentPivot_componentTagList :
    (slabIncidentPlaqIds 5 reflectedBentPivot).map
      reflectedBentComponentTag = [1, 0, 1, 2, 2] := by
  decide

structure ReflectedBentCutCarrierCertificate : Type where
  reflected : timeReflectPlaquette 5 reflectedBentRootPlaquette =
    reflectedBentTargetPlaquette
  supportConnected : connectedIn (L := z4Chain.toLattice)
    reflectedBentSwitchSurface
  nearConnectedAway : InternallyConnected
    (z4FaceAdjacentAwayB reflectedBentPivot) reflectedBentNearSurface
  farConnectedAway : InternallyConnected
    (z4FaceAdjacentAwayB reflectedBentPivot) reflectedBentFarSurface
  crossSeparated : SupportsSeparated
    (z4FaceAdjacentAwayB reflectedBentPivot)
    reflectedBentNearSurface reflectedBentFarSurface
  markedSeparated : ChainIn
    (z4FaceAdjacentAwayB reflectedBentPivot)
    reflectedBentSwitchSurface reflectedBentRootPlaquette
      reflectedBentTargetPlaquette → False
  pivotIncidence : faceIncidenceCount reflectedBentPivot
    reflectedBentSwitchSurface = 4
  otherIncidence : ∀ link, link ≠ reflectedBentPivot →
    faceIncidenceCount link reflectedBentSwitchSurface ≤ 2
  slabOrder : (slabIncidentPlaqIds 5 reflectedBentPivot).map
    reflectedBentComponentTag = [1, 0, 1, 2, 2]

def reflectedBentCutCarrierCertificate :
    ReflectedBentCutCarrierCertificate :=
  { reflected := reflectedBentTarget_reflects_root
    supportConnected := reflectedBentSwitchSurface_connected
    nearConnectedAway := reflectedBentNearSurface_connected_away
    farConnectedAway := reflectedBentFarSurface_connected_away
    crossSeparated := reflectedBent_noCrossAdjacencyAway
    markedSeparated := reflectedBent_noMarkedFaceChain_away
    pivotIncidence := reflectedBentPivot_faceIncidenceCount
    otherIncidence := reflectedBent_other_faceIncidenceCount_le_two
    slabOrder := reflectedBentPivot_componentTagList }

#print axioms reflectedBentTarget_reflects_root
#print axioms reflectedBentSwitchSurface_evenFaceIncidence
#print axioms reflectedBentSwitchSurface_connected
#print axioms reflectedBentNearSurface_connected_away
#print axioms reflectedBentFarSurface_connected_away
#print axioms reflectedBent_crossSharedLink_eq_pivot
#print axioms reflectedBent_noMarkedFaceChain_away
#print axioms reflectedBentPivot_faceIncidenceCount
#print axioms reflectedBent_other_faceIncidenceCount_le_two
#print axioms reflectedBentPivot_componentTagList
#print axioms reflectedBentCutCarrierCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
