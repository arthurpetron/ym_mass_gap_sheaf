/-
# The marked seven-cube faces bypass the proposed recoupling pivot

The outward Z query face reaches the outward Y query face through one
intermediate face and two literal shared links.  Neither shared link is the
unique four-incidence pivot of the seven-cube surface.  Thus deleting only
that pivot does not geometrically separate the two marked faces.

This is a witness-bearing obstruction certificate, not yet a theorem about
every realized strand pairing: the downstream sparse-link compiler must still
show that each displayed bivalent geometric step is forced in the physical
strand graph.

Constructive contract: literal finite incidence and Type-valued path data;
no choice, `Classical`, `native_decide`, `sorry`, new axiom, or unbounded
heartbeat.  The two dependent terminal constructions use a bounded
one-million-heartbeat allowance.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
import YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource

namespace YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
open YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource
open YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor
open YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns

/-! ## 1. A generic two-step path avoiding one link -/

/-- Two consecutive shared-link steps inside `support`, together with the
data that neither displayed shared link is `forbidden`. -/
structure TwoStepLinkPathAway
    (support : List Z4Plaq) (forbidden : Z4Link)
    (first last : Z4Plaq) : Type where
  middle : Z4Plaq
  first_mem : first ∈ support
  middle_mem : middle ∈ support
  last_mem : last ∈ support
  firstLink : Z4Link
  firstLink_ne : firstLink ≠ forbidden
  first_on_first : z4Boundary first firstLink = true
  first_on_middle : z4Boundary middle firstLink = true
  secondLink : Z4Link
  secondLink_ne : secondLink ≠ forbidden
  second_on_middle : z4Boundary middle secondLink = true
  second_on_last : z4Boundary last secondLink = true

/-- Forgetting the avoidance data gives an ordinary internal plaquette chain. -/
def TwoStepLinkPathAway.toChainIn
    {support : List Z4Plaq} {forbidden : Z4Link}
    {first last : Z4Plaq}
    (path : TwoStepLinkPathAway support forbidden first last) :
    ChainIn z4Chain.toLattice support first last :=
  .step
    { link := path.firstLink
      on_p := path.first_on_first
      on_q := path.first_on_middle }
    path.middle_mem
    (.step
      { link := path.secondLink
        on_p := path.second_on_middle
        on_q := path.second_on_last }
      path.last_mem
      (ChainIn.refl (L := z4Chain.toLattice) (X := support) last))

/-! ## 2. The literal seven-cube bypass -/

abbrev sevenCubeSwitchBypassMiddle : Z4Plaq :=
  ((0, 0, 0, 0), .p12)

abbrev sevenCubeSwitchBypassFirstLink : Z4Link :=
  ((0, 0, 1, 0), .x1)

abbrev sevenCubeSwitchBypassSecondLink : Z4Link :=
  ((0, 1, 0, 0), .x2)

/-- The marked target and root are joined by two bivalent geometric steps
which avoid the sole four-incidence link. -/
def sevenCubeSwitchRootTarget_pivotBypass :
    TwoStepLinkPathAway sevenCubeSwitchSurface sevenCubeSwitchPivot
      outwardZQueryFace outwardYQueryFace where
  middle := sevenCubeSwitchBypassMiddle
  first_mem := by decide
  middle_mem := by decide
  last_mem := by decide
  firstLink := sevenCubeSwitchBypassFirstLink
  firstLink_ne := by decide
  first_on_first := by decide
  first_on_middle := by decide
  secondLink := sevenCubeSwitchBypassSecondLink
  secondLink_ne := by decide
  second_on_middle := by decide
  second_on_last := by decide

/-- In particular, the ordinary marked-face connectivity admits a displayed
path whose adjacency witnesses do not use the proposed pivot. -/
def sevenCubeSwitchRootTarget_chainAwayFromPivot :
    ChainIn z4Chain.toLattice sevenCubeSwitchSurface
      outwardZQueryFace outwardYQueryFace :=
  sevenCubeSwitchRootTarget_pivotBypass.toChainIn

/-! ## 3. The two bivalent steps are forced by every accepted local witness -/

abbrev sevenCubeSwitchBypassMiddleFaceId : Nat :=
  slabFaceIdOfPlaquette 5 sevenCubeSwitchBypassMiddle

private theorem sevenCubeSwitchBypassFirst_positiveFace
    (faceId : Nat)
    (hincident : faceId ∈
      slabIncidentPlaqIds 5 sevenCubeSwitchBypassFirstLink)
    (hpositive : 0 < sevenCubeSwitchLeftPhysical faceId) :
    faceId = sevenCubeSwitchTargetFaceId ∨
      faceId = sevenCubeSwitchBypassMiddleFaceId := by
  have hids : slabIncidentPlaqIds 5 sevenCubeSwitchBypassFirstLink =
      [3, 33, 36, 37] := by decide
  rw [hids] at hincident
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hincident
  rcases hincident with rfl | rfl | rfl | rfl
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · have hzero : sevenCubeSwitchLeftPhysical 36 = 0 := by
      unfold sevenCubeSwitchLeftPhysical
      decide
    rw [hzero] at hpositive
    omega
  · have hzero : sevenCubeSwitchLeftPhysical 37 = 0 := by
      unfold sevenCubeSwitchLeftPhysical
      decide
    rw [hzero] at hpositive
    omega

private theorem sevenCubeSwitchBypassSecond_positiveFace
    (faceId : Nat)
    (hincident : faceId ∈
      slabIncidentPlaqIds 5 sevenCubeSwitchBypassSecondLink)
    (hpositive : 0 < sevenCubeSwitchLeftPhysical faceId) :
    faceId = sevenCubeSwitchBypassMiddleFaceId ∨
      faceId = sevenCubeSwitchRootFaceId := by
  have hids : slabIncidentPlaqIds 5 sevenCubeSwitchBypassSecondLink =
      [3, 199, 201, 203] := by decide
  rw [hids] at hincident
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hincident
  rcases hincident with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · have hzero : sevenCubeSwitchLeftPhysical 201 = 0 := by
      unfold sevenCubeSwitchLeftPhysical
      decide
    rw [hzero] at hpositive
    omega
  · have hzero : sevenCubeSwitchLeftPhysical 203 = 0 := by
      unfold sevenCubeSwitchLeftPhysical
      decide
    rw [hzero] at hpositive
    omega

/-- A local edge together with the ordered face identifiers that it joins. -/
structure ForcedSlabFaceEdge
    (cutoff extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link)
    (sourceFace targetFace : Nat) : Type where
  edge : SlabFaceStrandEdge physical
  edge_mem : edge ∈
    slabLinkFaceStrandEdges cutoff extent physical link auxiliary hmem
  source_eq : edge.source.faceId = sourceFace
  target_eq : edge.target.faceId = targetFace

def sevenCubeSwitchBypassFirstSourcePosition : Fin
    (slabIncidentPlaqIds 5 sevenCubeSwitchBypassFirstLink).length :=
  ⟨1, by decide⟩

theorem sevenCubeSwitchBypassFirstSourcePosition_faceId :
    (slabIncidentPlaqIds 5 sevenCubeSwitchBypassFirstLink).get
        sevenCubeSwitchBypassFirstSourcePosition =
      sevenCubeSwitchTargetFaceId := by
  decide

def sevenCubeSwitchBypassFirstSourceSlot : Fin
    (sevenCubeSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 sevenCubeSwitchBypassFirstLink).get
        sevenCubeSwitchBypassFirstSourcePosition)) :=
  ⟨0, by
    rw [sevenCubeSwitchBypassFirstSourcePosition_faceId]
    exact sevenCubeSwitchFace_positive outwardZQueryFace
      sevenCube011To100_queryFaces.1.2.2⟩

def sevenCubeSwitchBypassSecondSourcePosition : Fin
    (slabIncidentPlaqIds 5 sevenCubeSwitchBypassSecondLink).length :=
  ⟨0, by decide⟩

theorem sevenCubeSwitchBypassSecondSourcePosition_faceId :
    (slabIncidentPlaqIds 5 sevenCubeSwitchBypassSecondLink).get
        sevenCubeSwitchBypassSecondSourcePosition =
      sevenCubeSwitchBypassMiddleFaceId := by
  decide

def sevenCubeSwitchBypassSecondSourceSlot : Fin
    (sevenCubeSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 sevenCubeSwitchBypassSecondLink).get
        sevenCubeSwitchBypassSecondSourcePosition)) :=
  ⟨0, by
    rw [sevenCubeSwitchBypassSecondSourcePosition_faceId]
    exact sevenCubeSwitchFace_positive sevenCubeSwitchBypassMiddle
      (by decide)⟩

/-- Construct the canonical physical terminal at any literal incident face
position and bounded strand slot.  Factoring this compiler keeps downstream
fixed-geometry proofs independent of the resolved fusion-tree internals. -/
def slabLinkPhysicalTerminalAt
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link)
    (position : Fin (slabIncidentPlaqIds extent link).length)
    (slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position))) :
    SlabLinkPhysicalStrandTerminal cutoff extent physical link auxiliary
      hmem :=
  (canonicalPhysicalSlotObservation
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed cutoff extent physical link
      auxiliary hmem)
    position
    (slabLinkCanonicalSlotAt (auxiliary := auxiliary) position slot)).terminal

theorem slabLinkPhysicalTerminalAt_copy
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link)
    (position : Fin (slabIncidentPlaqIds extent link).length)
    (slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position))) :
    slabLinkPhysicalTerminalFaceStrandCopy cutoff extent physical link
        auxiliary hmem (slabLinkPhysicalTerminalAt hmem position slot) =
      { faceId := (slabIncidentPlaqIds extent link).get position
        slot := slot } := by
  unfold slabLinkPhysicalTerminalAt
  exact slabLinkPhysicalSlotObservation_copy
    (cutoff := cutoff) (hmem := hmem) position slot _

def sevenCubeSwitchBypassFirstTerminal
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink) :
    SlabLinkPhysicalStrandTerminal 1 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchBypassFirstLink auxiliary hmem :=
  slabLinkPhysicalTerminalAt hmem
    sevenCubeSwitchBypassFirstSourcePosition
    sevenCubeSwitchBypassFirstSourceSlot

theorem sevenCubeSwitchBypassFirstTerminal_sourceFace
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink) :
    (slabLinkPhysicalTerminalFaceStrandCopy 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
      auxiliary hmem
      (sevenCubeSwitchBypassFirstTerminal auxiliary hmem)).faceId =
        sevenCubeSwitchTargetFaceId := by
  have hcopy := slabLinkPhysicalTerminalAt_copy hmem
    sevenCubeSwitchBypassFirstSourcePosition
    sevenCubeSwitchBypassFirstSourceSlot
  have hface := congrArg
    (fun copy : SlabFaceStrandCopy sevenCubeSwitchLeftPhysical => copy.faceId)
    hcopy
  exact hface.trans sevenCubeSwitchBypassFirstSourcePosition_faceId

theorem sevenCubeSwitchBypassFirst_partnerFace
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
      auxiliary hmem)
    (hsource : (slabLinkPhysicalTerminalOccurrence 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
      auxiliary hmem terminal).faceId = sevenCubeSwitchTargetFaceId) :
    (slabLinkPhysicalTerminalOccurrence 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
      auxiliary hmem
      (slabLinkPhysicalStrandPartner 1 5 sevenCubeSwitchLeftPhysical
        sevenCubeSwitchBypassFirstLink auxiliary hmem terminal)).faceId =
      sevenCubeSwitchBypassMiddleFaceId := by
  let partner := slabLinkPhysicalStrandPartner 1 5
    sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
    auxiliary hmem terminal
  have hpartnerIncident :
      (slabLinkPhysicalTerminalOccurrence 1 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
        auxiliary hmem partner).faceId ∈
        slabIncidentPlaqIds 5 sevenCubeSwitchBypassFirstLink :=
    SlabLinkFaceStrandOccurrence.faceId_mem_incident _
  have hpartnerPositive : 0 < sevenCubeSwitchLeftPhysical
      (slabLinkPhysicalTerminalOccurrence 1 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
        auxiliary hmem partner).faceId :=
    Nat.zero_lt_of_lt
      (slabLinkPhysicalTerminalOccurrence 1 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
        auxiliary hmem partner).slot.isLt
  have hcases := sevenCubeSwitchBypassFirst_positiveFace
    _ hpartnerIncident hpartnerPositive
  have hne := slabLinkPhysicalStrandPartner_faceId_ne 1 5
    sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
    auxiliary hmem terminal
  rcases hcases with htarget | hmiddle
  · apply False.elim
    apply hne
    exact htarget.trans hsource.symm
  · exact hmiddle

/-- Every accepted auxiliary witness at the first bypass link pairs the
marked Z-face strand with the intermediate face strand. -/
def sevenCubeSwitchBypassFirst_forcedEdge
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink) :
    ForcedSlabFaceEdge 1 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchBypassFirstLink auxiliary hmem
      sevenCubeSwitchTargetFaceId sevenCubeSwitchBypassMiddleFaceId :=
  { edge := slabLinkFaceStrandEdgeOfTerminal 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
      auxiliary hmem
      (sevenCubeSwitchBypassFirstTerminal auxiliary hmem)
    edge_mem := slabLinkFaceStrandEdgeOfTerminal_mem 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassFirstLink
      auxiliary hmem
      (sevenCubeSwitchBypassFirstTerminal auxiliary hmem)
    source_eq := sevenCubeSwitchBypassFirstTerminal_sourceFace auxiliary hmem
    target_eq := sevenCubeSwitchBypassFirst_partnerFace auxiliary hmem
      (sevenCubeSwitchBypassFirstTerminal auxiliary hmem)
      (sevenCubeSwitchBypassFirstTerminal_sourceFace auxiliary hmem) }

def sevenCubeSwitchBypassSecondTerminal
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink) :
    SlabLinkPhysicalStrandTerminal 1 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchBypassSecondLink auxiliary hmem :=
  slabLinkPhysicalTerminalAt hmem
    sevenCubeSwitchBypassSecondSourcePosition
    sevenCubeSwitchBypassSecondSourceSlot

theorem sevenCubeSwitchBypassSecondTerminal_sourceFace
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink) :
    (slabLinkPhysicalTerminalFaceStrandCopy 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
      auxiliary hmem
      (sevenCubeSwitchBypassSecondTerminal auxiliary hmem)).faceId =
        sevenCubeSwitchBypassMiddleFaceId := by
  have hcopy := slabLinkPhysicalTerminalAt_copy hmem
    sevenCubeSwitchBypassSecondSourcePosition
    sevenCubeSwitchBypassSecondSourceSlot
  have hface := congrArg
    (fun copy : SlabFaceStrandCopy sevenCubeSwitchLeftPhysical => copy.faceId)
    hcopy
  exact hface.trans sevenCubeSwitchBypassSecondSourcePosition_faceId

theorem sevenCubeSwitchBypassSecond_partnerFace
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
      auxiliary hmem)
    (hsource : (slabLinkPhysicalTerminalOccurrence 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
      auxiliary hmem terminal).faceId = sevenCubeSwitchBypassMiddleFaceId) :
    (slabLinkPhysicalTerminalOccurrence 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
      auxiliary hmem
      (slabLinkPhysicalStrandPartner 1 5 sevenCubeSwitchLeftPhysical
        sevenCubeSwitchBypassSecondLink auxiliary hmem terminal)).faceId =
      sevenCubeSwitchRootFaceId := by
  let partner := slabLinkPhysicalStrandPartner 1 5
    sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
    auxiliary hmem terminal
  have hpartnerIncident :
      (slabLinkPhysicalTerminalOccurrence 1 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
        auxiliary hmem partner).faceId ∈
        slabIncidentPlaqIds 5 sevenCubeSwitchBypassSecondLink :=
    SlabLinkFaceStrandOccurrence.faceId_mem_incident _
  have hpartnerPositive : 0 < sevenCubeSwitchLeftPhysical
      (slabLinkPhysicalTerminalOccurrence 1 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
        auxiliary hmem partner).faceId :=
    Nat.zero_lt_of_lt
      (slabLinkPhysicalTerminalOccurrence 1 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
        auxiliary hmem partner).slot.isLt
  have hcases := sevenCubeSwitchBypassSecond_positiveFace
    _ hpartnerIncident hpartnerPositive
  have hne := slabLinkPhysicalStrandPartner_faceId_ne 1 5
    sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
    auxiliary hmem terminal
  rcases hcases with hmiddle | hroot
  · apply False.elim
    apply hne
    exact hmiddle.trans hsource.symm
  · exact hroot

/-- Every accepted auxiliary witness at the second bypass link pairs the
intermediate-face strand with the marked Y-face strand. -/
def sevenCubeSwitchBypassSecond_forcedEdge
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink) :
    ForcedSlabFaceEdge 1 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchBypassSecondLink auxiliary hmem
      sevenCubeSwitchBypassMiddleFaceId sevenCubeSwitchRootFaceId :=
  { edge := slabLinkFaceStrandEdgeOfTerminal 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
      auxiliary hmem
      (sevenCubeSwitchBypassSecondTerminal auxiliary hmem)
    edge_mem := slabLinkFaceStrandEdgeOfTerminal_mem 1 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchBypassSecondLink
      auxiliary hmem
      (sevenCubeSwitchBypassSecondTerminal auxiliary hmem)
    source_eq := sevenCubeSwitchBypassSecondTerminal_sourceFace auxiliary hmem
    target_eq := sevenCubeSwitchBypassSecond_partnerFace auxiliary hmem
      (sevenCubeSwitchBypassSecondTerminal auxiliary hmem)
      (sevenCubeSwitchBypassSecondTerminal_sourceFace auxiliary hmem) }

/-! ## 4. Globalization and failure of every one-pivot target -/

theorem sevenCubeSwitchBypassFirstLink_mem_boundaryComplete :
    sevenCubeSwitchBypassFirstLink ∈ boundaryCompleteSlabLinks 5 := by
  apply (mem_boundaryCompleteSlabLinks_iff 5
    sevenCubeSwitchBypassFirstLink).mpr
  exact ⟨outwardZQueryFace,
    sevenCubeSwitchSurface_subset_slab_five outwardZQueryFace
      sevenCube011To100_queryFaces.1.2.2,
    by decide⟩

theorem sevenCubeSwitchBypassSecondLink_mem_boundaryComplete :
    sevenCubeSwitchBypassSecondLink ∈ boundaryCompleteSlabLinks 5 := by
  apply (mem_boundaryCompleteSlabLinks_iff 5
    sevenCubeSwitchBypassSecondLink).mpr
  exact ⟨sevenCubeSwitchBypassMiddle,
    sevenCubeSwitchSurface_subset_slab_five
      sevenCubeSwitchBypassMiddle (by decide),
    by decide⟩

def sevenCubeSwitchBypassFirstLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨sevenCubeSwitchBypassFirstLink,
    sevenCubeSwitchBypassFirstLink_mem_boundaryComplete⟩

def sevenCubeSwitchBypassSecondLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨sevenCubeSwitchBypassSecondLink,
    sevenCubeSwitchBypassSecondLink_mem_boundaryComplete⟩

/-- One edge of an already assembled global strand list, with its projected
source and target face identifiers retained. -/
structure ForcedListedFaceEdge
    (physical : SlabLabelling)
    (edges : List (SlabFaceStrandEdge physical))
    (sourceFace targetFace : Nat) : Type where
  edge : SlabFaceStrandEdge physical
  edge_mem : edge ∈ edges
  source_eq : edge.source.faceId = sourceFace
  target_eq : edge.target.faceId = targetFace

def sevenCubeSwitchBypassFirst_globalForcedEdge
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFusionWitnessAssignmentsOn 1 5
      sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)) :
    ForcedListedFaceEdge sevenCubeSwitchLeftPhysical
      (slabFusionWitnessAssignmentFaceStrandEdges 1 5
        sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
        assignment hassignment)
      sevenCubeSwitchTargetFaceId sevenCubeSwitchBypassMiddleFaceId := by
  let linked := sevenCubeSwitchBypassFirstLinked
  let auxiliary := slabFusionWitnessAssignmentAt linked.1 assignment
  let hmem := slabFusionWitnessAssignmentAt_mem_local 1 5
    sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
    assignment hassignment linked.1 linked.2
  let localEdge := sevenCubeSwitchBypassFirst_forcedEdge auxiliary hmem
  exact
    { edge := localEdge.edge
      edge_mem := slabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
        1 5 sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
        assignment hassignment linked
        (sevenCubeSwitchBypassFirstTerminal auxiliary hmem)
      source_eq := localEdge.source_eq
      target_eq := localEdge.target_eq }

def sevenCubeSwitchBypassSecond_globalForcedEdge
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFusionWitnessAssignmentsOn 1 5
      sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)) :
    ForcedListedFaceEdge sevenCubeSwitchLeftPhysical
      (slabFusionWitnessAssignmentFaceStrandEdges 1 5
        sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
        assignment hassignment)
      sevenCubeSwitchBypassMiddleFaceId sevenCubeSwitchRootFaceId := by
  let linked := sevenCubeSwitchBypassSecondLinked
  let auxiliary := slabFusionWitnessAssignmentAt linked.1 assignment
  let hmem := slabFusionWitnessAssignmentAt_mem_local 1 5
    sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
    assignment hassignment linked.1 linked.2
  let localEdge := sevenCubeSwitchBypassSecond_forcedEdge auxiliary hmem
  exact
    { edge := localEdge.edge
      edge_mem := slabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
        1 5 sevenCubeSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
        assignment hassignment linked
        (sevenCubeSwitchBypassSecondTerminal auxiliary hmem)
      source_eq := localEdge.source_eq
      target_eq := localEdge.target_eq }

/-- Two displayed left-replica edges `target -> middle -> root` force the
paired-face obstruction Boolean to be true. -/
theorem sevenCubeSwitchPair_connected_of_two_left_edges
    (pair : SlabObservableTwoReplicaPair sevenCubeSwitchPhysicalData
      sevenCubeSwitchRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
      sevenCubeSwitchTargetFaceId)
    (first second : SlabFaceStrandEdge pair.1.1.1)
    (hfirst : first ∈ slabObservableTwoReplicaPairLeftStrandEdges
      sevenCubeSwitchPhysicalData pair)
    (hsecond : second ∈ slabObservableTwoReplicaPairLeftStrandEdges
      sevenCubeSwitchPhysicalData pair)
    (hfirstSource : first.source.faceId = sevenCubeSwitchTargetFaceId)
    (hfirstTarget : first.target.faceId = sevenCubeSwitchBypassMiddleFaceId)
    (hsecondSource : second.source.faceId = sevenCubeSwitchBypassMiddleFaceId)
    (hsecondTarget : second.target.faceId = sevenCubeSwitchRootFaceId) :
    slabObservableTwoReplicaPairPairedFaceConnectedB
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
      sevenCubeSwitchTargetFaceId pair = true := by
  have htarget :=
    slabObservableTwoReplicaPairPairedFaceSwapMask_target
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
      sevenCubeSwitchTargetFaceId
      sevenCubeSwitchTargetFaceId_physical pair hpair
  have hfirstMask :=
    slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_left_edge
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
      sevenCubeSwitchTargetFaceId
      sevenCubeSwitchTargetFaceId_physical pair hpair hfirst
  have hsecondMask :=
    slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_left_edge
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
      sevenCubeSwitchTargetFaceId
      sevenCubeSwitchTargetFaceId_physical pair hpair hsecond
  rw [hfirstTarget, hfirstSource] at hfirstMask
  rw [hsecondTarget, hsecondSource] at hsecondMask
  unfold slabObservableTwoReplicaPairPairedFaceConnectedB
  exact hsecondMask.trans (hfirstMask.trans htarget)

end YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass

#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass.sevenCubeSwitchRootTarget_pivotBypass
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass.sevenCubeSwitchRootTarget_chainAwayFromPivot
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass.sevenCubeSwitchBypassFirst_forcedEdge
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass.sevenCubeSwitchBypassSecond_forcedEdge
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass.sevenCubeSwitchBypassFirst_globalForcedEdge
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass.sevenCubeSwitchBypassSecond_globalForcedEdge
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass.sevenCubeSwitchPair_connected_of_two_left_edges
