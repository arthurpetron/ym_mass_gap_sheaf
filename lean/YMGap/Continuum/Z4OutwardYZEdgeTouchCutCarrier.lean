/-
# The outward Y/Z edge-touch surface is a genuine one-link cut carrier

The earlier seven-cube switching candidate had a geometric bypass around its
four-incidence link.  The twelve-face `outwardYZSurface` has the opposite
topology: it is the union of two face-disjoint unit-cube boundaries which meet
only at the link `((0,1,1,0),x0)`.

This file certifies the exact causal geometry needed by a local recoupling
switch.  After deleting that link, each six-face cube boundary is still
internally connected, while the marked Y and Z query faces lie in different
components.  The same link is the unique four-incidence link of the union;
every other touched link is bivalent.

Constructive contract: all finite checks are ordinary kernel reduction and
are compiled to Type-valued paths.  No choice principle, `native_decide`,
unchecked existence claim, or unbounded heartbeat option is used.
-/

import YMGap.Continuum.FiniteBoolGraphWarshallPathDecision
import YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphWarshallPathDecision
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. A finite, witness-producing link-deletion graph -/

/-- Two plaquettes are adjacent away from `forbidden` when they share one of
the four displayed boundary links and that link is not `forbidden`. -/
def z4FaceAdjacentAwayB (forbidden : Z4Link)
    (left right : Z4Plaq) : Bool :=
  (edgesOf left).any fun link =>
    decide (link != forbidden) && decide (link ∈ edgesOf right)

/-- Check every ordered pair in a finite support for reachability. -/
def allPairsReachableB {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State) : Bool :=
  support.all fun first =>
    support.all fun last =>
      finiteSupportReachableB adjacent support first last

/-- A successful all-pairs check contracts to genuine Type-valued internal
paths, not merely a propositional connectivity assertion. -/
def internallyConnectedOfAllPairsReachableB
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (hcheck : allPairsReachableB adjacent support = true) :
    InternallyConnected adjacent support := by
  intro first last hfirst hlast
  apply chainInOfFiniteSupportReachableB
  exact List.all_eq_true.mp
    (List.all_eq_true.mp hcheck first hfirst) last hlast

/-! ## 2. The literal edge-touch cut -/

/-- The sole link at which the shifted Y and Z cube boundaries touch. -/
abbrev outwardYZCutPivot : Z4Link := ((0, 1, 1, 0), .x0)

theorem outwardYSurface_awayFromPivot_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayB outwardYZCutPivot) outwardYSurface = true := by
  decide

theorem outwardZSurface_awayFromPivot_allPairsReachable :
    allPairsReachableB
      (z4FaceAdjacentAwayB outwardYZCutPivot) outwardZSurface = true := by
  decide

/-- Deleting the pivot does not cut either individual cube boundary. -/
def outwardYSurface_connected_awayFromPivot :
    InternallyConnected
      (z4FaceAdjacentAwayB outwardYZCutPivot) outwardYSurface :=
  internallyConnectedOfAllPairsReachableB _ _
    outwardYSurface_awayFromPivot_allPairsReachable

/-- Deleting the pivot does not cut either individual cube boundary. -/
def outwardZSurface_connected_awayFromPivot :
    InternallyConnected
      (z4FaceAdjacentAwayB outwardYZCutPivot) outwardZSurface :=
  internallyConnectedOfAllPairsReachableB _ _
    outwardZSurface_awayFromPivot_allPairsReachable

/-- A finite check that every link shared by a left/right face pair is the
displayed pivot. -/
def allCrossSharedLinksEqB (left right : List Z4Plaq)
    (pivot : Z4Link) : Bool :=
  left.all fun leftFace =>
    right.all fun rightFace =>
      (edgesOf leftFace).all fun link =>
        if link ∈ edgesOf rightFace then decide (link = pivot) else true

theorem outwardYZ_allCrossSharedLinksEqPivot :
    allCrossSharedLinksEqB
      outwardYSurface outwardZSurface outwardYZCutPivot = true := by
  decide

/-- The two cube boundaries have no geometric contact except the pivot. -/
theorem outwardYZ_crossSharedLink_eq_pivot
    {leftFace rightFace : Z4Plaq} {link : Z4Link}
    (hleftFace : leftFace ∈ outwardYSurface)
    (hrightFace : rightFace ∈ outwardZSurface)
    (hleftLink : link ∈ edgesOf leftFace)
    (hrightLink : link ∈ edgesOf rightFace) :
    link = outwardYZCutPivot := by
  have hleftRow := List.all_eq_true.mp
    outwardYZ_allCrossSharedLinksEqPivot leftFace hleftFace
  have hrightRow := List.all_eq_true.mp hleftRow rightFace hrightFace
  have hlinkRow := List.all_eq_true.mp hrightRow link hleftLink
  simp [hrightLink] at hlinkRow
  exact hlinkRow

theorem outwardYZ_noCrossAdjacencyAwayFromPivot :
    SupportsSeparated
      (z4FaceAdjacentAwayB outwardYZCutPivot)
      outwardYSurface outwardZSurface := by
  intro leftFace hleftFace rightFace hrightFace
  unfold z4FaceAdjacentAwayB
  apply List.any_eq_false.mpr
  intro link hleftLink
  by_cases hrightLink : link ∈ edgesOf rightFace
  · have hpivot := outwardYZ_crossSharedLink_eq_pivot
      hleftFace hrightFace hleftLink hrightLink
    simp [hpivot]
  · simp [hrightLink]

/-- The two standard coarse query faces are separated in the full twelve-face
support once the pivot is forbidden. -/
theorem outwardYZ_markedFaces_not_reachable_awayFromPivot :
    finiteSupportReachableB
      (z4FaceAdjacentAwayB outwardYZCutPivot)
      outwardYZSurface outwardYQueryFace outwardZQueryFace = false := by
  decide

/-- The false finite check is exposed as a constructive refutation of every
purported pivot-avoiding marked-face path. -/
def outwardYZ_noMarkedFaceChain_awayFromPivot :
    ChainIn
      (z4FaceAdjacentAwayB outwardYZCutPivot)
      outwardYZSurface outwardYQueryFace outwardZQueryFace -> False :=
  noChainInOfFiniteSupportReachableBFalse _ _
    outwardYZ_markedFaces_not_reachable_awayFromPivot

/-! ## 3. Exact single-four-incidence profile -/

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

/-- Check the one-four/all-other-at-most-two incidence profile only on the
finite touched-link list; untouched links are handled generically. -/
def singleFourIncidenceProfileB
    (support : List Z4Plaq) (pivot : Z4Link) : Bool :=
  decide (faceIncidenceCount pivot support = 4) &&
    (geometricTouchedLinks support).all fun link =>
      decide (link = pivot) || decide (faceIncidenceCount link support ≤ 2)

theorem outwardYZ_singleFourIncidenceProfile_checked :
    singleFourIncidenceProfileB outwardYZSurface outwardYZCutPivot = true := by
  decide

theorem outwardYZCutPivot_faceIncidenceCount :
    faceIncidenceCount outwardYZCutPivot outwardYZSurface = 4 := by
  have hparts := (Bool.and_eq_true _ _).mp
    outwardYZ_singleFourIncidenceProfile_checked
  exact of_decide_eq_true hparts.1

theorem outwardYZ_other_faceIncidenceCount_le_two
    (link : Z4Link) (hne : link ≠ outwardYZCutPivot) :
    faceIncidenceCount link outwardYZSurface ≤ 2 := by
  by_cases htouched : link ∈ geometricTouchedLinks outwardYZSurface
  · have hall := (Bool.and_eq_true _ _).mp
      outwardYZ_singleFourIncidenceProfile_checked |>.2
    have hrow := List.all_eq_true.mp hall link htouched
    have hpivotFalse : decide (link = outwardYZCutPivot) = false := by
      simp [hne]
    rw [hpivotFalse, Bool.false_or] at hrow
    exact of_decide_eq_true hrow
  · rw [faceIncidenceCount_eq_zero_of_not_touched
      link outwardYZSurface htouched]
    omega

/-- The support is therefore a literal two-component, one-pivot cut carrier:
each side remains connected away from the pivot, all cross contacts use it,
the marked faces are separated without it, and it is the sole possible
higher-valence link. -/
structure OutwardYZCutCarrierCertificate : Type where
  leftConnected : InternallyConnected
    (z4FaceAdjacentAwayB outwardYZCutPivot) outwardYSurface
  rightConnected : InternallyConnected
    (z4FaceAdjacentAwayB outwardYZCutPivot) outwardZSurface
  crossSeparated : SupportsSeparated
    (z4FaceAdjacentAwayB outwardYZCutPivot)
    outwardYSurface outwardZSurface
  markedSeparated : ChainIn
    (z4FaceAdjacentAwayB outwardYZCutPivot)
    outwardYZSurface outwardYQueryFace outwardZQueryFace -> False
  pivotIncidence : faceIncidenceCount
    outwardYZCutPivot outwardYZSurface = 4
  otherIncidence : forall link, link ≠ outwardYZCutPivot ->
    faceIncidenceCount link outwardYZSurface ≤ 2

def outwardYZCutCarrierCertificate : OutwardYZCutCarrierCertificate :=
  { leftConnected := outwardYSurface_connected_awayFromPivot
    rightConnected := outwardZSurface_connected_awayFromPivot
    crossSeparated := outwardYZ_noCrossAdjacencyAwayFromPivot
    markedSeparated := outwardYZ_noMarkedFaceChain_awayFromPivot
    pivotIncidence := outwardYZCutPivot_faceIncidenceCount
    otherIncidence := outwardYZ_other_faceIncidenceCount_le_two }

#print axioms internallyConnectedOfAllPairsReachableB
#print axioms outwardYSurface_connected_awayFromPivot
#print axioms outwardZSurface_connected_awayFromPivot
#print axioms outwardYZ_crossSharedLink_eq_pivot
#print axioms outwardYZ_noCrossAdjacencyAwayFromPivot
#print axioms outwardYZ_noMarkedFaceChain_awayFromPivot
#print axioms outwardYZCutPivot_faceIncidenceCount
#print axioms outwardYZ_other_faceIncidenceCount_le_two
#print axioms outwardYZCutCarrierCertificate

end YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier
