/-
# The AF cofinal trajectory has a genuine cutoff-four fallback step

The first member of the AF cofinal family with two block steps reaches the
previously exposed collar obstruction at its second step.  That step has fine
cutoff four, fine half-size one, coarse cutoff sixteen, and coarse half-size
zero.  The same finite collar state has strictly positive AF Wilson mass, but
its complete four-preimage recoupling row has no positive coarse target.

Consequently the positive-incoherent source mass and the exact fallback `L1`
cost are strictly positive on this literal AF trajectory step.  Thus the
first-step cutoff-one cancellation does not extend to all later AF steps;
continuum work must quantitatively control or telescope the later fallback
producer rather than delete it by support.

This is one finite depth-one obstruction only.  It supplies no lower bound
uniform in coupling, cutoff, volume, or depth, and proves no continuum limit,
spectral gap, or Clay theorem.

Constructive contract: finite `Nat`/`List` computation and exact `Q'` order
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTrajectory
import YMGap.Continuum.CompactDualAllCutoffPhysicalPushforwardCounterexample

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalFallbackObstruction

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
open YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTrajectory
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PairChannelSupportAddition
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact later AF step -/

def afCutoffFourScalePair : SlabScalePair :=
  su2OuterScalePair counterGeometry
    (afNomeSchedule.nome 1)
    (Q'.le_of_lt (afNomeSchedule.nome_pos 1))
    (afNomeSchedule.nome 2)
    (afNomeSchedule.nome_pos 2) 4

/-- The second step of the depth-one AF trajectory is definitionally the
cutoff-four collar geometry at the scheduled couplings. -/
theorem afCofinalTrajectory_depthOne_lastPair :
    (lastStep (afCofinalTrajectory 1)).pair =
      afCutoffFourScalePair := by
  rfl

theorem afCutoffFourScalePair_fine_cutoff :
    afCutoffFourScalePair.fine.cutoff = 4 := rfl

theorem afCutoffFourScalePair_coarse_cutoff :
    afCutoffFourScalePair.coarse.cutoff = 16 := rfl

theorem afCutoffFourScalePair_fine_half :
    afCutoffFourScalePair.fine.half = 1 := rfl

theorem afCutoffFourScalePair_coarse_half :
    afCutoffFourScalePair.coarse.half = 0 := rfl

/-! ## 2. The collar state still has positive AF Wilson mass -/

theorem collarState_mem_afCutoffFour :
    collarState ∈ afCutoffFourScalePair.fine.physicalLabellings := by
  change collarState ∈
    boundedEdgeLabellings 4 (slabPhysicalFaceEdges 3)
  exact boundedEdgeLabellings_mem_of_le
    (K := 2) (L := 4) (by omega)
    (slabPhysicalFaceEdges 3) collarState_mem

private theorem eliminateLinks_pos_local
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') < value id) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids
  | [] => by
      change (0 : Q') < 1
      decide
  | head :: tail =>
      Q'.mul_pos (hvalue head)
        (eliminateLinks_pos_local value hvalue tail)

theorem collarState_faceFactor_pos_afCutoffFour :
    (0 : Q') <
      slabParametricKPhysicalFaceFactor
        (afNomeSchedule.nome 1) 4 3 collarState := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_pos_local
  intro id
  have hspin : collarState id < 4 + 1 := by
    unfold collarState
    by_cases hdistinguished : id = 420
    · simp [hdistinguished]
    · by_cases hsupport : id ∈ collarSupportFaceIds
      · simp [hdistinguished, hsupport]
      · simp [hdistinguished, hsupport]
  rw [coeffAt_heatKernelPacket hspin]
  exact
    YMGap.Continuum.FusionResidualBound.coeffW_pos
      (afNomeSchedule.nome_pos 1) (collarState id)

theorem collarState_linkProduct_pos_afCutoffFour :
    0 < slabExplicitLinkMultiplicityProduct 4 3 collarState := by
  have hbounded :
      SlabFaceLabellingBounded 2 3 collarState :=
    slabFaceLabellingBounded_of_physical collarState_mem
  have hstable :=
    slabExplicitLinkMultiplicityProduct_cutoff_stable
      (K := 2) (L := 4) (extent := 3)
      (physical := collarState) (by omega) hbounded
  rw [hstable]
  exact collarState_linkProduct_pos

private theorem qOfNat_pos_of_pos
    (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  show (0 : Int) * ((Q'.ofNat value).den : Int) <
    (Q'.ofNat value).num * (1 : Int)
  rw [Int.zero_mul, Q'.ofNat_num_cast, Int.mul_one]
  exact Int.ofNat_lt.mpr hvalue

theorem collarState_physicalTerm_pos_afCutoffFour :
    (0 : Q') <
      afCutoffFourScalePair.fine.physicalTerm collarState := by
  change
    (0 : Q') <
      slabParametricKPhysicalFaceFactor
          (afNomeSchedule.nome 1) 4 3 collarState *
        Q'.ofNat
          (slabExplicitLinkMultiplicityProduct 4 3 collarState)
  exact Q'.mul_pos
    collarState_faceFactor_pos_afCutoffFour
    (qOfNat_pos_of_pos _ collarState_linkProduct_pos_afCutoffFour)

/-! ## 3. No positive four-preimage row at cutoff four -/

theorem selectedCoarseFace_packet_afCutoffFour :
    wholeSlabFinePacket afCutoffFourScalePair collarState
        selectedCoarseFaceId =
      (⟨2, 0, 0, 0⟩ : FaceSpinPacket) := by
  decide

theorem firstVacuumCoarseFace_packet_afCutoffFour :
    wholeSlabFinePacket afCutoffFourScalePair collarState
        firstVacuumCoarseFaceId =
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket) := by
  decide

theorem secondVacuumCoarseFace_packet_afCutoffFour :
    wholeSlabFinePacket afCutoffFourScalePair collarState
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

theorem no_collarState_jointChannelSelection_afCutoffFour :
    WholeSlabJointChannelSelection
      afCutoffFourScalePair collarState → False := by
  intro selection
  have hselectedChannel :
      (selection.faceChannel selectedCoarseFaceId).2 = 2 := by
    apply selectedPacket_positive_final_eq_two
    rw [← selectedCoarseFace_packet_afCutoffFour]
    exact selection.faceChannel_positive
      selectedCoarseFaceId (by decide)
  have hfirstVacuumChannel :
      (selection.faceChannel firstVacuumCoarseFaceId).2 = 0 := by
    apply vacuumPacket_positive_final_eq_zero
    rw [← firstVacuumCoarseFace_packet_afCutoffFour]
    exact selection.faceChannel_positive
      firstVacuumCoarseFaceId (by decide)
  have hsecondVacuumChannel :
      (selection.faceChannel secondVacuumCoarseFaceId).2 = 0 := by
    apply vacuumPacket_positive_final_eq_zero
    rw [← secondVacuumCoarseFace_packet_afCutoffFour]
    exact selection.faceChannel_positive
      secondVacuumCoarseFaceId (by decide)
  have htargetSelected :
      selection.coarseTarget selectedCoarseFaceId = 2 := by
    rw [← selection.faceChannel_final
      selectedCoarseFaceId (by decide)]
    exact hselectedChannel
  have htargetFirstVacuum :
      selection.coarseTarget firstVacuumCoarseFaceId = 0 := by
    rw [← selection.faceChannel_final
      firstVacuumCoarseFaceId (by decide)]
    exact hfirstVacuumChannel
  have htargetSecondVacuum :
      selection.coarseTarget secondVacuumCoarseFaceId = 0 := by
    rw [← selection.faceChannel_final
      secondVacuumCoarseFaceId (by decide)]
    exact hsecondVacuumChannel
  have hzero :
      slabExplicitLinkMultiplicity
        afCutoffFourScalePair.coarse.cutoff
        afCutoffFourScalePair.coarse.extent
        selection.coarseTarget badCoarseLink = 0 := by
    unfold slabExplicitLinkMultiplicity
    change explicitValenceMultiplicity
      (linkAuxiliaryCutoff 16)
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
    selection.coarseLink_positive badCoarseLink (by decide)
  rw [hzero] at hpositive
  exact Nat.not_lt_zero 0 hpositive

theorem collarState_rawRowMass_not_pos_afCutoffFour :
    ¬ (0 : Q') <
      wholeSlabJointRawRowMass
        afCutoffFourScalePair collarState := by
  intro hmass
  exact no_collarState_jointChannelSelection_afCutoffFour
    (positiveWholeSlabRawTargetOfRowMass
      hmass).toJointChannelSelection

theorem collarState_wholeSlabRawRowPartition_not_pos_afCutoffFour :
    ¬ (0 : Q') <
      wholeSlabRawRowPartition
        afCutoffFourScalePair collarState := by
  simpa only [wholeSlabRawRowPartition,
    wholeSlabJointRawRowMass] using
      collarState_rawRowMass_not_pos_afCutoffFour

/-! ## 4. Strictly positive fallback on the actual AF step -/

theorem collarState_normalizedMass_pos_afCutoffFour :
    (0 : Q') <
      afCutoffFourScalePair.fine.normalizedMass collarState := by
  unfold SlabPhysicalData.normalizedMass
  exact Q'.divPos_pos _ _
    (slabParametricKPhysicalPartition_pos
      afCutoffFourScalePair.fine.coupling_nonnegative
      afCutoffFourScalePair.fine.cutoff
      afCutoffFourScalePair.fine.extent)
    collarState_physicalTerm_pos_afCutoffFour

theorem collarState_positiveIncoherentRowWeight_pos_afCutoffFour :
    (0 : Q') <
      positiveIncoherentRecouplingRowWeight
        afCutoffFourScalePair collarState := by
  unfold positiveIncoherentRecouplingRowWeight
  rw [if_pos collarState_physicalTerm_pos_afCutoffFour]
  rw [if_neg
    collarState_wholeSlabRawRowPartition_not_pos_afCutoffFour]
  exact collarState_normalizedMass_pos_afCutoffFour

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A},
      selected ∈ items → value selected ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative
          value hvalue tail htail
        have htailLe : listQSum value tail ≤
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hvalue head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih htailLe

theorem afCutoffFour_positiveIncoherentRecouplingMass_pos :
    (0 : Q') <
      positiveIncoherentRecouplingMass
        afCutoffFourScalePair := by
  unfold positiveIncoherentRecouplingMass
  exact Q'.pos_of_lt_of_le
    collarState_positiveIncoherentRowWeight_pos_afCutoffFour
    (listQSum_member_le_nonnegative
      (positiveIncoherentRecouplingRowWeight afCutoffFourScalePair)
      (positiveIncoherentRecouplingRowWeight_nonnegative
        afCutoffFourScalePair)
      afCutoffFourScalePair.fine.physicalLabellings
      collarState_mem_afCutoffFour)

theorem afCutoffFour_coherenceFallbackL1_pos :
    (0 : Q') <
      coherenceFallbackL1 afCutoffFourScalePair (by decide) := by
  exact Q'.pos_of_lt_of_le
    afCutoffFour_positiveIncoherentRecouplingMass_pos
    (Q'.ge_of_eqv
      (coherenceFallbackL1_eqv_positiveIncoherentRecouplingMass
        afCutoffFourScalePair (by decide)))

/-- The actual later step in the two-step AF trajectory has nonzero
positive-incoherent source probability. -/
theorem afCofinalTrajectory_depthOne_lastIncoherentMass_pos :
    (0 : Q') <
      positiveIncoherentRecouplingMass
        (lastStep (afCofinalTrajectory 1)).pair := by
  rw [afCofinalTrajectory_depthOne_lastPair]
  exact afCutoffFour_positiveIncoherentRecouplingMass_pos

/-- The exact fallback `L1` producer is genuinely present on that same AF
trajectory step. -/
theorem afCofinalTrajectory_depthOne_lastFallbackL1_pos :
    (0 : Q') <
      coherenceFallbackL1
        (lastStep (afCofinalTrajectory 1)).pair
        (lastStep (afCofinalTrajectory 1)).fineCutoff := by
  change (0 : Q') <
    coherenceFallbackL1 afCutoffFourScalePair (by decide)
  exact afCutoffFour_coherenceFallbackL1_pos

/-! ## Axiom audit -/

#print axioms afCofinalTrajectory_depthOne_lastPair
#print axioms collarState_mem_afCutoffFour
#print axioms collarState_physicalTerm_pos_afCutoffFour
#print axioms no_collarState_jointChannelSelection_afCutoffFour
#print axioms collarState_rawRowMass_not_pos_afCutoffFour
#print axioms afCutoffFour_positiveIncoherentRecouplingMass_pos
#print axioms afCutoffFour_coherenceFallbackL1_pos
#print axioms afCofinalTrajectory_depthOne_lastIncoherentMass_pos
#print axioms afCofinalTrajectory_depthOne_lastFallbackL1_pos

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalFallbackObstruction
