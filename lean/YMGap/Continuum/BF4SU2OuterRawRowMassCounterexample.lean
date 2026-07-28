/-
# A positive fine row with zero BF4 four-preimage raw-row mass

The four nondegenerate dyadic face preimages do not retain enough transverse
flux to define a positive coarse row on every positive fine physical term.
This module pins the first exact obstruction.

The fine state has one doubled central `p01` face and a sixteen-face
spin-one collar.  Every active fine link carries either the word `(1,1)` or
the word `(2,1,1)`, so every fine Haar multiplicity is one and the full
heat-kernel summand is strictly positive.

At coarse scale, however, the only nonvacuum four-preimage packet is
`(2,0,0,0)` on face `p01`.  Positivity forces its final label to be two,
while the two other faces incident to the displayed coarse `x0` link have
vacuum packets and hence final label zero.  The resulting local word
`(2,0,0)` has no invariant tensor.  Therefore no joint channel selection
exists, the raw-row mass is not positive, and the advertised all-row
`SU2OuterRawRowMassPositive` structure is contradictory for this geometry.

The obstruction identifies the exact information loss: side faces carrying
the fine intertwiner flow are absent from `wholeSlabFinePacket`.  A corrected
kernel must retain a collared packet or the fine intertwiner carrier through
conditional integration.

## Axiom gate

Finite `Nat`, `List`, `Bool`, and exact `Q'` computation only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, noncomputable
declaration, or proof by contradiction is used.
-/

import YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
import YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
import YMGap.Continuum.SU2PairChannelSupportAddition

namespace YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PairChannelSupportAddition
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

def collarSupport : List Z4Plaq :=
  [((1, 1, 0, 0), .p01),
   ((1, 1, 0, 0), .p02), ((1, 1, 0, 0), .p03),
   ((1, 1, 0, 0), .p12), ((1, 1, 0, 0), .p13),
   ((1, 1, 0, 1), .p02), ((1, 1, 0, 1), .p12),
   ((1, 1, 1, 0), .p03), ((1, 1, 1, 0), .p13),
   ((1, 2, 0, 0), .p02), ((1, 2, 0, 0), .p03),
   ((1, 2, 0, 1), .p02), ((1, 2, 1, 0), .p03),
   ((2, 1, 0, 0), .p12), ((2, 1, 0, 0), .p13),
   ((2, 1, 0, 1), .p12), ((2, 1, 1, 0), .p13)]

def distinguishedFineFace : Z4Plaq :=
  ((1, 1, 0, 0), .p01)

def collarSupportFaceIds : List Nat :=
  [421, 422, 423, 424, 427, 429, 443, 445,
   505, 506, 511, 527, 759, 760, 765, 781]

def collarState : EdgeLabelling :=
  fun id =>
    if id = 420 then 2
    else if id ∈ collarSupportFaceIds then 1 else 0

theorem collarState_mem :
    collarState ∈ counterScalePair.fine.physicalLabellings := by
  change collarState ∈ boundedEdgeLabellings 2 (slabPhysicalFaceEdges 3)
  apply boundedEdgeLabellings_complete
  · intro id hid
    unfold collarState
    by_cases hdistinguished : id = 420
    · simp [hdistinguished]
    · by_cases hsupport : id ∈ collarSupportFaceIds
      · simp [hdistinguished, hsupport]
      · simp [hdistinguished, hsupport]
  · intro id hid
    unfold collarState
    have hidLower : 1344 ≤ id := by
      change id ∉ List.range 1344 at hid
      simp only [List.mem_range] at hid
      omega
    have hne : id ≠ 420 := by omega
    have hnotSupport : id ∉ collarSupportFaceIds := by
      unfold collarSupportFaceIds
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    simp [hne, hnotSupport]

def collarActiveLinks : List Z4Link :=
  (collarSupport.flatMap edgesOf).eraseDups

theorem collarActiveLinks_eq_literal :
    collarActiveLinks =
      [((1, 1, 0, 0), .x0), ((1, 1, 0, 0), .x1),
       ((1, 2, 0, 0), .x0), ((2, 1, 0, 0), .x1),
       ((1, 1, 0, 0), .x2), ((1, 1, 1, 0), .x0),
       ((2, 1, 0, 0), .x2), ((1, 1, 0, 0), .x3),
       ((1, 1, 0, 1), .x0), ((2, 1, 0, 0), .x3),
       ((1, 1, 1, 0), .x1), ((1, 2, 0, 0), .x2),
       ((1, 1, 0, 1), .x1), ((1, 2, 0, 0), .x3),
       ((1, 1, 0, 1), .x2), ((1, 1, 1, 1), .x0),
       ((2, 1, 0, 1), .x2), ((1, 1, 1, 1), .x1),
       ((1, 2, 0, 1), .x2), ((1, 1, 1, 0), .x3),
       ((2, 1, 1, 0), .x3), ((1, 2, 1, 0), .x3),
       ((1, 2, 1, 0), .x0), ((2, 2, 0, 0), .x2),
       ((1, 2, 0, 1), .x0), ((2, 2, 0, 0), .x3),
       ((1, 2, 1, 1), .x0), ((2, 2, 0, 1), .x2),
       ((2, 2, 1, 0), .x3), ((2, 1, 1, 0), .x1),
       ((2, 1, 0, 1), .x1), ((2, 1, 1, 1), .x1)] := by
  decide

private theorem collarState_nonzero_support
    {id : Nat} (hstate : collarState id ≠ 0) :
    slabPlaquetteAt 3 id ∈ collarSupport := by
  by_cases hdistinguished : id = 420
  · subst id
    decide
  · have hsupportId : id ∈ collarSupportFaceIds := by
      by_cases hsupport : id ∈ collarSupportFaceIds
      · exact hsupport
      · exact False.elim
          (hstate (by simp [collarState, hdistinguished, hsupport]))
    have hall :
        collarSupportFaceIds.all (fun faceId =>
          decide (slabPlaquetteAt 3 faceId ∈ collarSupport)) = true := by
      decide
    simpa only [decide_eq_true_eq] using
      List.all_eq_true.mp hall id hsupportId

private theorem incident_of_nonzero_mem_active
    {link : Z4Link} {id : Nat}
    (hid : id ∈ slabIncidentPlaqIds 3 link)
    (hstate : collarState id ≠ 0) :
    link ∈ collarActiveLinks := by
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    (mem_slabIncidentPlaqIds.mp hid)
  have hlookup :
      slabPlaquetteAt 3 id = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  have hsupport := collarState_nonzero_support hstate
  rw [hlookup] at hsupport
  unfold collarActiveLinks
  simp only [List.mem_eraseDups, List.mem_flatMap]
  exact ⟨plaquette, hsupport, hedge⟩

private theorem ZeroExtension.nil_map_of_all_zero
    {A : Type} (value : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item = 0) →
      ZeroExtension [] (items.map value)
  | [], _ => ZeroExtension.nil
  | head :: tail, hzero => by
      simp only [List.map_cons, hzero head List.mem_cons_self]
      exact ZeroExtension.insertZero
        (ZeroExtension.nil_map_of_all_zero value tail
          (fun item hitem =>
            hzero item (List.mem_cons_of_mem head hitem)))

private theorem collarState_linkMultiplicity_pos
    (link : Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks 3) :
    0 < slabExplicitLinkMultiplicity 2 3 collarState link := by
  by_cases hactive : link ∈ collarActiveLinks
  · rw [collarActiveLinks_eq_literal] at hactive
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hactive
    rcases hactive with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · have hzero :
        ∀ id, id ∈ slabIncidentPlaqIds 3 link →
          collarState id = 0 := by
      intro id hid
      by_cases hstate : collarState id = 0
      · exact hstate
      · exact False.elim
          (hactive (incident_of_nonzero_mem_active hid hstate))
    have hzeroExtension :
        ZeroExtension []
          ((slabIncidentPlaqIds 3 link).map collarState) :=
      ZeroExtension.nil_map_of_all_zero
        collarState (slabIncidentPlaqIds 3 link) hzero
    have htargetLength :
        ((slabIncidentPlaqIds 3 link).map collarState).length ≤ 6 := by
      simpa only [List.length_map] using
        slabIncidentPlaqIds_length_le_six 3 link
    have hnilBounded :
        SpinsBounded (linkAuxiliaryCutoff 2) [] := by
      intro spin hspin
      exact False.elim (List.not_mem_nil hspin)
    have heq :=
      explicitValenceMultiplicity_zeroExtension
        (cutoff := linkAuxiliaryCutoff 2)
        hzeroExtension (by decide) htargetLength hnilBounded
    unfold slabExplicitLinkMultiplicity
    rw [← heq]
    decide

private theorem natListProduct_pos_on {A : Type}
    (value : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → 0 < value item) →
      0 < natListProduct value items
  | [], _ => Nat.zero_lt_succ 0
  | head :: tail, hvalue => by
      simp only [natListProduct]
      exact Nat.mul_pos
        (hvalue head List.mem_cons_self)
        (natListProduct_pos_on value tail
          (fun item hitem =>
            hvalue item (List.mem_cons_of_mem head hitem)))

theorem collarState_linkProduct_pos :
    0 < slabExplicitLinkMultiplicityProduct 2 3 collarState := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_pos_on _ _
    collarState_linkMultiplicity_pos

private theorem eliminateLinks_pos_local
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') < value id) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids
  | [] => by
      change (0 : Q') < 1
      decide
  | head :: tail =>
      Q'.mul_pos (hvalue head)
        (eliminateLinks_pos_local value hvalue tail)

theorem collarState_faceFactor_pos :
    (0 : Q') <
      slabParametricKPhysicalFaceFactor 1 2 3 collarState := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_pos_local
  intro id
  have hspin : collarState id < 2 + 1 := by
    unfold collarState
    by_cases hdistinguished : id = 420
    · simp [hdistinguished]
    · by_cases hsupport : id ∈ collarSupportFaceIds
      · simp [hdistinguished, hsupport]
      · simp [hdistinguished, hsupport]
  rw [coeffAt_heatKernelPacket hspin]
  exact
    YMGap.Continuum.FusionResidualBound.coeffW_pos
      (by decide) (collarState id)

private theorem qOfNat_pos_of_pos
    (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  show (0 : Int) * ((Q'.ofNat value).den : Int) <
    (Q'.ofNat value).num * (1 : Int)
  rw [Int.zero_mul, Q'.ofNat_num_cast, Int.mul_one]
  exact Int.ofNat_lt.mpr hvalue

theorem collarState_physicalTerm_pos :
    (0 : Q') <
      counterScalePair.fine.physicalTerm collarState := by
  change
    (0 : Q') <
      slabParametricKPhysicalFaceFactor 1 2 3 collarState *
        Q'.ofNat
          (slabExplicitLinkMultiplicityProduct 2 3 collarState)
  exact Q'.mul_pos
    collarState_faceFactor_pos
    (qOfNat_pos_of_pos _ collarState_linkProduct_pos)

def selectedCoarseFaceId : Nat := 0
def firstVacuumCoarseFaceId : Nat := 1
def secondVacuumCoarseFaceId : Nat := 2
def badCoarseLink : Z4Link := ((0, 0, 0, 0), .x0)

theorem selectedCoarseFaceId_mem :
    selectedCoarseFaceId ∈ counterScalePair.coarse.faceEdges := by
  decide

theorem firstVacuumCoarseFaceId_mem :
    firstVacuumCoarseFaceId ∈ counterScalePair.coarse.faceEdges := by
  decide

theorem secondVacuumCoarseFaceId_mem :
    secondVacuumCoarseFaceId ∈ counterScalePair.coarse.faceEdges := by
  decide

theorem badCoarseLink_mem :
    badCoarseLink ∈
      boundaryCompleteSlabLinks counterScalePair.coarse.extent := by
  decide

theorem selectedCoarseFace_packet :
    wholeSlabFinePacket counterScalePair collarState
        selectedCoarseFaceId =
      (⟨2, 0, 0, 0⟩ : FaceSpinPacket) := by
  decide

theorem firstVacuumCoarseFace_packet :
    wholeSlabFinePacket counterScalePair collarState
        firstVacuumCoarseFaceId =
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket) := by
  decide

theorem secondVacuumCoarseFace_packet :
    wholeSlabFinePacket counterScalePair collarState
        secondVacuumCoarseFaceId =
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket) := by
  decide

private theorem selectedPacket_positive_final_eq_two
    {w : Q'} {state : PairChannelState}
    (hpositive :
      (0 : Q') <
        packetPairChannelRawWeight w
          (⟨2, 0, 0, 0⟩ : FaceSpinPacket) state) :
    state.2 = 2 := by
  have hsupported :=
    packetPairChannelSupported_of_rawWeight_pos hpositive
  have hleft : state.1.1 = 2 := by
    have h := hsupported.1
    change fusionOK 2 0 state.1.1 = true at h
    rw [fusionOK_zero_right_eq_decide] at h
    simpa only [decide_eq_true_eq] using h
  have hright : state.1.2 = 0 := by
    have h := hsupported.2.1
    change fusionOK 0 0 state.1.2 = true at h
    rw [fusionOK_zero_left_eq_decide] at h
    simpa only [decide_eq_true_eq] using h
  have hfinal := hsupported.2.2
  rw [hleft, hright, fusionOK_zero_right_eq_decide] at hfinal
  simpa only [decide_eq_true_eq] using hfinal

private theorem vacuumPacket_positive_final_eq_zero
    {w : Q'} {state : PairChannelState}
    (hpositive :
      (0 : Q') <
        packetPairChannelRawWeight w
          (⟨0, 0, 0, 0⟩ : FaceSpinPacket) state) :
    state.2 = 0 := by
  have hsupported :=
    packetPairChannelSupported_of_rawWeight_pos hpositive
  have hleft : state.1.1 = 0 := by
    have h := hsupported.1
    change fusionOK 0 0 state.1.1 = true at h
    rw [fusionOK_zero_left_eq_decide] at h
    simpa only [decide_eq_true_eq] using h
  have hright : state.1.2 = 0 := by
    have h := hsupported.2.1
    change fusionOK 0 0 state.1.2 = true at h
    rw [fusionOK_zero_left_eq_decide] at h
    simpa only [decide_eq_true_eq] using h
  have hfinal := hsupported.2.2
  rw [hleft, hright, fusionOK_zero_left_eq_decide] at hfinal
  simpa only [decide_eq_true_eq] using hfinal

theorem no_collarState_jointChannelSelection :
    WholeSlabJointChannelSelection
      counterScalePair collarState → False := by
  intro selection
  have hselectedChannel :
      (selection.faceChannel selectedCoarseFaceId).2 = 2 := by
    apply selectedPacket_positive_final_eq_two
    rw [← selectedCoarseFace_packet]
    exact selection.faceChannel_positive
      selectedCoarseFaceId selectedCoarseFaceId_mem
  have hfirstVacuumChannel :
      (selection.faceChannel firstVacuumCoarseFaceId).2 = 0 := by
    apply vacuumPacket_positive_final_eq_zero
    rw [← firstVacuumCoarseFace_packet]
    exact selection.faceChannel_positive
      firstVacuumCoarseFaceId firstVacuumCoarseFaceId_mem
  have hsecondVacuumChannel :
      (selection.faceChannel secondVacuumCoarseFaceId).2 = 0 := by
    apply vacuumPacket_positive_final_eq_zero
    rw [← secondVacuumCoarseFace_packet]
    exact selection.faceChannel_positive
      secondVacuumCoarseFaceId secondVacuumCoarseFaceId_mem
  have htargetSelected :
      selection.coarseTarget selectedCoarseFaceId = 2 := by
    rw [← selection.faceChannel_final
      selectedCoarseFaceId selectedCoarseFaceId_mem]
    exact hselectedChannel
  have htargetFirstVacuum :
      selection.coarseTarget firstVacuumCoarseFaceId = 0 := by
    rw [← selection.faceChannel_final
      firstVacuumCoarseFaceId firstVacuumCoarseFaceId_mem]
    exact hfirstVacuumChannel
  have htargetSecondVacuum :
      selection.coarseTarget secondVacuumCoarseFaceId = 0 := by
    rw [← selection.faceChannel_final
      secondVacuumCoarseFaceId secondVacuumCoarseFaceId_mem]
    exact hsecondVacuumChannel
  have hzero :
      slabExplicitLinkMultiplicity
        counterScalePair.coarse.cutoff
        counterScalePair.coarse.extent
        selection.coarseTarget badCoarseLink = 0 := by
    unfold slabExplicitLinkMultiplicity
    change explicitValenceMultiplicity
      (linkAuxiliaryCutoff 8)
      (slabIncidentPlaqIds 1 badCoarseLink).length
      (externalSpinsOfList
        ((slabIncidentPlaqIds 1 badCoarseLink).map
          selection.coarseTarget)) = 0
    rw [show slabIncidentPlaqIds 1 badCoarseLink =
      [selectedCoarseFaceId, firstVacuumCoarseFaceId,
        secondVacuumCoarseFaceId] by decide]
    simp only [List.map_cons, List.map_nil, List.length_cons,
      List.length_nil]
    rw [htargetSelected, htargetFirstVacuum,
      htargetSecondVacuum]
    decide
  have hpositive :=
    selection.coarseLink_positive badCoarseLink badCoarseLink_mem
  rw [hzero] at hpositive
  exact Nat.not_lt_zero 0 hpositive

theorem collarState_rawRowMass_not_pos :
    ¬ (0 : Q') <
      wholeSlabJointRawRowMass counterScalePair collarState := by
  intro hmass
  exact no_collarState_jointChannelSelection
    (positiveWholeSlabRawTargetOfRowMass
      hmass).toJointChannelSelection

theorem no_SU2OuterRawRowMassPositive :
    SU2OuterRawRowMassPositive
      counterGeometry 1 (by decide) 1 (by decide) → False := by
  intro mass
  exact collarState_rawRowMass_not_pos
    (mass.positive
      2 collarState (by decide)
      collarState_mem collarState_physicalTerm_pos)

#print axioms collarState_mem
#print axioms collarState_linkProduct_pos
#print axioms collarState_physicalTerm_pos
#print axioms no_collarState_jointChannelSelection
#print axioms collarState_rawRowMass_not_pos
#print axioms no_SU2OuterRawRowMassPositive

end YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample
