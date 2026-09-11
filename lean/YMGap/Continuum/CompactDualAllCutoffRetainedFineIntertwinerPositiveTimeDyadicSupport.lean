/-
# Dyadic same-object support for the positive-time face event

A coarse physical face is not the same lattice object as one arbitrarily
chosen fine face.  Its exact fine antecedent is the four-face dyadic packet.
This module defines the corresponding packet-occupation event and proves two
facts:

* packet occupation means that at least one of the four injected fine faces
  is occupied;
* at fine cutoff one, the SU(2) pointwise lowering kernel cannot produce a
  positive coarse face from an empty packet.

Consequently the exact coherent raw mismatch between packet occupation and
coarse-face occupation is bounded by the packet-occupation source indicator,
and the normalized coherent mismatch average is bounded by the genuine fine
Gibbs probability of that packet event.  This removes the spurious comparison
between unrelated single faces.  It does not yet bound the packet probability
uniformly or establish reflection positivity, a transfer gap, or a continuum
limit.

## Axiom gate

Finite-list recursion, the checked four-face dyadic geometry, the explicit
SU(2) spin-zero-through-four lowering matrix, and exact rational normalization
only.  No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorOccupation
import YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDyadicSupport

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimePushedOccupation
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeRawMismatch
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact four-face fine antecedent -/

/-- Boolean occupation of the complete four-face dyadic packet over one
coarse physical face. -/
def dyadicFinePacketPositiveB
    (S : SlabScalePair) (coarseFaceId : Nat)
    (fineState : EdgeLabelling) : Bool :=
  decide
    (0 < wholeSlabFinePacketTotalLabelling
      S fineState coarseFaceId)

private theorem listNatWeight_pos_iff_exists_positive_local
    {A : Type} (value : A → Nat) : ∀ items : List A,
    0 < listNatWeight value items ↔
      ∃ item, item ∈ items ∧ 0 < value item
  | [] => by simp [listNatWeight]
  | head :: tail => by
      rw [listNatWeight]
      constructor
      · intro hpositive
        by_cases hhead : 0 < value head
        · exact ⟨head, List.mem_cons_self, hhead⟩
        · have hheadZero : value head = 0 := Nat.eq_zero_of_not_pos hhead
          rw [hheadZero, Nat.zero_add] at hpositive
          obtain ⟨item, hitem, hitemPositive⟩ :=
            (listNatWeight_pos_iff_exists_positive_local value tail).mp
              hpositive
          exact ⟨item, List.mem_cons_of_mem head hitem, hitemPositive⟩
      · rintro ⟨item, hitem, hitemPositive⟩
        rcases List.mem_cons.mp hitem with rfl | htail
        · omega
        · have htailPositive :=
            (listNatWeight_pos_iff_exists_positive_local value tail).mpr
              ⟨item, htail, hitemPositive⟩
          omega

/-- Packet occupation is literally the union of the four injected fine-face
occupation events. -/
theorem dyadicFinePacketPositiveB_true_iff_exists_positive
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    dyadicFinePacketPositiveB S coarseFaceId fineState = true ↔
      ∃ fineFaceId,
        fineFaceId ∈ dyadicCoarseFaceFineFaceIds S coarseFaceId ∧
          0 < fineState fineFaceId := by
  unfold dyadicFinePacketPositiveB
  rw [decide_eq_true_eq]
  rw [wholeSlabFinePacketTotal_eq_fineFaceIdWeight
    S fineState coarseFaceId hcoarseFaceId]
  exact listNatWeight_pos_iff_exists_positive_local
    fineState (dyadicCoarseFaceFineFaceIds S coarseFaceId)

/-! ## 2. The lowering kernel cannot create packet occupation -/

/-- If the fine packet is empty while the coarse target face is positive,
the exact cutoff-one globally glued raw transition weight vanishes. -/
theorem wholeSlabRecouplingRawWeight_eqv_zero_of_emptyPacket_positiveTarget
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : SlabPhysicalSourceEntry S.fine)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges)
    (hempty : dyadicFinePacketPositiveB
      S coarseFaceId source.1 = false)
    (targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (htargetPositive :
      slabPhysicalFacePositiveB coarseFaceId targetState = true) :
    wholeSlabRecouplingRawWeight S source.1 targetState ≈ 0 := by
  have hsourceBound : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      wholeSlabFinePacketTotalLabelling S source.1 faceId ≤ 4 := by
    intro faceId hfaceId
    exact wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff source.2 faceId hfaceId
  have hsourceZero :
      wholeSlabFinePacketTotalLabelling
          S source.1 coarseFaceId = 0 := by
    apply Nat.eq_zero_of_not_pos
    unfold dyadicFinePacketPositiveB at hempty
    exact of_decide_eq_false hempty
  have htargetPos : 0 < targetState coarseFaceId := by
    unfold slabPhysicalFacePositiveB at htargetPositive
    exact of_decide_eq_true htargetPositive
  have hbad : ¬
      (targetState coarseFaceId ≤
          wholeSlabFinePacketTotalLabelling S source.1 coarseFaceId ∧
        targetState coarseFaceId % 2 =
          wholeSlabFinePacketTotalLabelling S source.1 coarseFaceId % 2) := by
    intro hlowering
    rw [hsourceZero] at hlowering
    omega
  exact Q'.eqv_trans _
    (spinFourLoweringWholeSlabRawWeight S
      (wholeSlabFinePacketTotalLabelling S source.1) targetState) _
    (wholeSlabRecouplingRawWeight_eqv_totalLoweringWeight
      S source.1 targetState hfineCutoff source.2 htargetMem)
    (spinFourLoweringWholeSlabRawWeight_eqv_zero_of_bad_face
      S (wholeSlabFinePacketTotalLabelling S source.1) targetState
      hfineCutoff hsourceBound htargetMem coarseFaceId hcoarseFaceId hbad)

/-- The corresponding normalized coherent conditional-kernel entry also
vanishes. -/
theorem coherentConditionalKernel_eqv_zero_of_emptyPacket_positiveTarget
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges)
    (hempty : dyadicFinePacketPositiveB
      S coarseFaceId source.1 = false)
    (targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (htargetPositive :
      slabPhysicalFacePositiveB coarseFaceId targetState = true) :
    wholeSlabRecouplingConditionalKernel
        (coherentSlabRecouplingSourceOfRawPartitionPos
          S source.1 source.2 hpartition) targetState ≈ 0 := by
  let coherent := coherentSlabRecouplingSourceOfRawPartitionPos
    S source.1 source.2 hpartition
  have hraw :=
    wholeSlabRecouplingRawWeight_eqv_zero_of_emptyPacket_positiveTarget
      S hfineCutoff source coarseFaceId hcoarseFaceId hempty
      targetState htargetMem htargetPositive
  unfold wholeSlabRecouplingConditionalKernel Q'.divPos
  change
    wholeSlabRecouplingRawWeight S source.1 targetState *
        Q'.recipPos (wholeSlabRecouplingPartition coherent)
          (wholeSlabRecouplingPartition_pos coherent) ≈ 0
  exact Q'.eqv_trans _
    (0 * Q'.recipPos (wholeSlabRecouplingPartition coherent)
      (wholeSlabRecouplingPartition_pos coherent)) _
    (Q'.mul_eqv_congr_right _ _ _ hraw)
    (Q'.zero_mul_eqv _)

private theorem coherentMoment_eqv_eventMass_local
    (S : SlabScalePair)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (event : EdgeLabelling → Bool) :
    coherentRecouplingEventMoment S source hpartition event ≈
      finiteEventMass
        (wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S source.1 source.2 hpartition))
        S.coarse.physicalLabellings event := by
  unfold coherentRecouplingEventMoment finiteEventMass
  apply listQSum_congr_on
  intro targetState _
  cases hevent : event targetState
  · simp only [rationalBoolIndicator,
      Bool.false_eq_true, if_false]
    exact Q'.mul_zero_eqv _
  · simp only [rationalBoolIndicator, if_true]
    exact Q'.mul_one_eqv _

/-- An empty fine packet gives zero conditional probability of a positive
coarse face. -/
theorem coherentCoarseFacePositiveMoment_eqv_zero_of_emptyPacket
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges)
    (hempty : dyadicFinePacketPositiveB
      S coarseFaceId source.1 = false) :
    coherentRecouplingEventMoment S source hpartition
        (slabPhysicalFacePositiveB coarseFaceId) ≈ 0 := by
  unfold coherentRecouplingEventMoment
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q'))
      S.coarse.physicalLabellings) _ ?_ (listQSum_zero _)
  apply listQSum_congr_on
  intro targetState htargetMem
  cases htargetPositive :
      slabPhysicalFacePositiveB coarseFaceId targetState
  · simp only [rationalBoolIndicator,
      Bool.false_eq_true, if_false]
    exact Q'.mul_zero_eqv _
  · simp only [rationalBoolIndicator, if_true]
    exact Q'.eqv_trans _
      (wholeSlabRecouplingConditionalKernel
        (coherentSlabRecouplingSourceOfRawPartitionPos
          S source.1 source.2 hpartition) targetState) _
      (Q'.mul_one_eqv _)
      (coherentConditionalKernel_eqv_zero_of_emptyPacket_positiveTarget
        S hfineCutoff source hpartition coarseFaceId hcoarseFaceId
        hempty targetState htargetMem htargetPositive)

/-! ## 3. One-sided same-object mismatch control -/

private theorem coherentSelectedRawMismatchRatio_le_one_local
    (S : SlabScalePair)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    coherentSelectedRawMismatchRatio
        S source hpartition fineEvent coarseEvent ≤ 1 := by
  let coherent := coherentSlabRecouplingSourceOfRawPartitionPos
    S source.1 source.2 hpartition
  let mismatch := cylinderPullbackMismatchEvent
    fineEvent coarseEvent source.1
  have heventLe :
      finiteEventMass
          (wholeSlabRecouplingConditionalKernel coherent)
          S.coarse.physicalLabellings mismatch ≤ 1 :=
    finiteEventMass_le_one
      (wholeSlabRecouplingConditionalKernel coherent)
      S.coarse.physicalLabellings mismatch
      (fun targetState _ =>
        wholeSlabRecouplingConditionalKernel_nonnegative
          coherent targetState)
      (wholeSlabRecouplingConditionalKernel_row_normalized coherent)
  have heq := conditionalKernelCylinderMass_eqv_rawCylinderRatio
    coherent mismatch
  unfold coherentSelectedRawMismatchRatio
  exact Q'.le_trans' _
    (finiteEventMass
      (wholeSlabRecouplingConditionalKernel coherent)
      S.coarse.physicalLabellings mismatch) _
    (Q'.ge_of_eqv heq) heventLe

/-- For the causally matched packet/coarse-face pair, the exact row mismatch
is no larger than the fine packet-occupation indicator.  Upward creation is
excluded by the SU(2) lowering support; the only possible mismatch is loss of
an already occupied packet. -/
theorem coherentDyadicFaceRawMismatchRatio_le_packetIndicator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    coherentSelectedRawMismatchRatio S source hpartition
        (dyadicFinePacketPositiveB S coarseFaceId)
        (slabPhysicalFacePositiveB coarseFaceId) ≤
      rationalBoolIndicator
        (dyadicFinePacketPositiveB S coarseFaceId source.1) := by
  cases hpacket : dyadicFinePacketPositiveB
      S coarseFaceId source.1
  · have hmomentZero :=
      coherentCoarseFacePositiveMoment_eqv_zero_of_emptyPacket
        S hfineCutoff source hpartition coarseFaceId hcoarseFaceId hpacket
    have hmomentEvent := coherentMoment_eqv_eventMass_local
      S source hpartition (slabPhysicalFacePositiveB coarseFaceId)
    let coherent := coherentSlabRecouplingSourceOfRawPartitionPos
      S source.1 source.2 hpartition
    have heventZero :
        finiteEventMass
            (wholeSlabRecouplingConditionalKernel coherent)
            S.coarse.physicalLabellings
            (slabPhysicalFacePositiveB coarseFaceId) ≈ 0 :=
      Q'.eqv_trans _
        (coherentRecouplingEventMoment S source hpartition
          (slabPhysicalFacePositiveB coarseFaceId)) _
        (Q'.eqv_symm hmomentEvent) hmomentZero
    have heventRaw := conditionalKernelCylinderMass_eqv_rawCylinderRatio
      coherent (slabPhysicalFacePositiveB coarseFaceId)
    have hrawZero :
        coherentSelectedRawMismatchRatio S source hpartition
            (dyadicFinePacketPositiveB S coarseFaceId)
            (slabPhysicalFacePositiveB coarseFaceId) ≈ 0 := by
      unfold coherentSelectedRawMismatchRatio cylinderPullbackMismatchEvent
      rw [hpacket]
      exact Q'.eqv_trans _
        (finiteEventMass
          (wholeSlabRecouplingConditionalKernel coherent)
          S.coarse.physicalLabellings
          (slabPhysicalFacePositiveB coarseFaceId)) _
        (Q'.eqv_symm heventRaw) heventZero
    simp only [rationalBoolIndicator,
      Bool.false_eq_true, if_false]
    exact Q'.le_of_eqv hrawZero
  · simp only [rationalBoolIndicator, if_true]
    exact coherentSelectedRawMismatchRatio_le_one_local
      S source hpartition
      (dyadicFinePacketPositiveB S coarseFaceId)
      (slabPhysicalFacePositiveB coarseFaceId)

private theorem positiveCoherentWeightedDefectAux_mono_local
    (S : SlabScalePair)
    (value bound :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q')
    (hrow : ∀ source hpartition,
      value source hpartition ≤ bound source hpartition) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      positiveCoherentWeightedDefectAux S value sources ≤
        positiveCoherentWeightedDefectAux S bound sources
  | [] => Q'.le_refl' 0
  | source :: tail => by
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source.1
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1
        · simp only [positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_pos hpartition]
          exact Q'.add_le_add
            (Q'.mul_le_mul_of_nonneg_left _ _
              (S.fine.normalizedMass source.1)
              (hrow source hpartition)
              (S.fine.normalizedMass_nonnegative source.1))
            (positiveCoherentWeightedDefectAux_mono_local
              S value bound hrow tail)
        · simp only [positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_neg hpartition]
          exact positiveCoherentWeightedDefectAux_mono_local
            S value bound hrow tail
      · simp only [positiveCoherentWeightedDefectAux,
          dif_neg hpositive]
        exact positiveCoherentWeightedDefectAux_mono_local
          S value bound hrow tail

/-- The normalized coherent raw mismatch average for a causally matched
dyadic packet/coarse face is bounded by the coherent packet-source mass. -/
theorem coherentDyadicFaceRawMismatchAverage_le_packetSourceMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    coherentEventRawMismatchAverage S
        (dyadicFinePacketPositiveB S coarseFaceId)
        (slabPhysicalFacePositiveB coarseFaceId) ≤
      coherentFineEventSourceMass S
        (dyadicFinePacketPositiveB S coarseFaceId) := by
  unfold coherentEventRawMismatchAverage coherentFineEventSourceMass
    positiveCoherentWeightedDefect
  apply positiveCoherentWeightedDefectAux_mono_local
  intro source hpartition
  exact coherentDyadicFaceRawMismatchRatio_le_packetIndicator
    S hfineCutoff source hpartition coarseFaceId hcoarseFaceId

/-- Canonical finite-law endpoint: the coherent same-object dyadic mismatch
is bounded by the normalized fine Gibbs probability that its four-face packet
is occupied. -/
theorem coherentDyadicFaceRawMismatchAverage_le_normalizedPacketMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    coherentEventRawMismatchAverage S
        (dyadicFinePacketPositiveB S coarseFaceId)
        (slabPhysicalFacePositiveB coarseFaceId) ≤
      normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S coarseFaceId) := by
  exact Q'.le_trans' _
    (coherentFineEventSourceMass S
      (dyadicFinePacketPositiveB S coarseFaceId)) _
    (coherentDyadicFaceRawMismatchAverage_le_packetSourceMass
      S hfineCutoff coarseFaceId hcoarseFaceId)
    (coherentFineEventSourceMass_le_normalizedSlabEventMass
      S (dyadicFinePacketPositiveB S coarseFaceId))

#print axioms dyadicFinePacketPositiveB_true_iff_exists_positive
#print axioms wholeSlabRecouplingRawWeight_eqv_zero_of_emptyPacket_positiveTarget
#print axioms coherentConditionalKernel_eqv_zero_of_emptyPacket_positiveTarget
#print axioms coherentCoarseFacePositiveMoment_eqv_zero_of_emptyPacket
#print axioms coherentDyadicFaceRawMismatchRatio_le_packetIndicator
#print axioms coherentDyadicFaceRawMismatchAverage_le_packetSourceMass
#print axioms coherentDyadicFaceRawMismatchAverage_le_normalizedPacketMass

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDyadicSupport
