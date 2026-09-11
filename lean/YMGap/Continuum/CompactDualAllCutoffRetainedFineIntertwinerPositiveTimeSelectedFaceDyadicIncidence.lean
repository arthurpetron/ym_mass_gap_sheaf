/-
# Selected-face incidence into the dyadic causal packet

The strict `256/425` anchor estimate is initially an estimate for the
four-face fine packet over one coarse face.  The positive-time OS compiler,
however, compares one selected fine face with one selected coarse face (and
their reflected joint event).  This module supplies the exact missing
compiler: if the selected fine face belongs to the causal dyadic packet, then
the actual selected-face raw mismatch is supported on packet occupation.

The same argument treats the joint event without an eight-face union bound.
If the root packet is empty, both the selected fine root and any positive
coarse joint event vanish in the required sense.  Hence the joint mismatch is
also charged to the one root packet and inherits the same strict constant.

The incidence facts are deliberately bundled as data.  Constructing that
bundle from a canonical coordinate choice is the next geometric obligation;
it is not hidden here.

Constructive contract: finite Boolean events, exact SU(2) lowering support,
finite-list recursion, and rational order only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, trusted
external computation, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorPacketOccupation

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeSelectedFaceDyadicIncidence

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorPacketOccupation
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDyadicSupport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
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
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit incidence bundle -/

/-- A positive-time face geometry whose selected fine root and reflected
face are explicitly members of the dyadic packets over their corresponding
coarse faces. -/
structure DyadicEnrichedLowerFaceGeometry (S : SlabScalePair) : Type where
  base : EnrichedLowerFaceGeometry S
  fineRoot_mem_packet :
    base.fineRoot ∈ dyadicCoarseFaceFineFaceIds S base.coarseRoot
  fineReflected_mem_packet :
    base.fineReflected ∈
      dyadicCoarseFaceFineFaceIds S base.coarseReflected

/-- Positivity of a selected fine face contained in a dyadic packet forces
occupation of the complete packet. -/
theorem selectedFineFacePositive_implies_packetPositive
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (fineFaceId coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges)
    (hfineFaceId :
      fineFaceId ∈ dyadicCoarseFaceFineFaceIds S coarseFaceId)
    (hpositive :
      slabPhysicalFacePositiveB fineFaceId fineState = true) :
    dyadicFinePacketPositiveB S coarseFaceId fineState = true := by
  apply (dyadicFinePacketPositiveB_true_iff_exists_positive
    S fineState coarseFaceId hcoarseFaceId).mpr
  refine ⟨fineFaceId, hfineFaceId, ?_⟩
  unfold slabPhysicalFacePositiveB at hpositive
  exact of_decide_eq_true hpositive

/-! ## 2. Generic causal-support compiler -/

/-- If a coarse event implies positivity of one named coarse face, then an
empty causal fine packet gives that coarse event zero conditional moment. -/
theorem coherentRecouplingEventMoment_eqv_zero_of_emptyPacket_of_support
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges)
    (hempty :
      dyadicFinePacketPositiveB S coarseFaceId source.1 = false)
    (coarseEvent : EdgeLabelling → Bool)
    (hcoarseSupport : ∀ targetState,
      coarseEvent targetState = true →
        slabPhysicalFacePositiveB coarseFaceId targetState = true) :
    coherentRecouplingEventMoment S source hpartition coarseEvent ≈ 0 := by
  unfold coherentRecouplingEventMoment
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q'))
      S.coarse.physicalLabellings) _ ?_ (listQSum_zero _)
  apply listQSum_congr_on
  intro targetState htargetMem
  cases htargetEvent : coarseEvent targetState
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
        hempty targetState htargetMem
        (hcoarseSupport targetState htargetEvent))

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

private theorem abs_eqv_zero_of_eqv_zero_local
    {value : Q'} (hvalue : value ≈ 0) : Q'.abs value ≈ 0 := by
  exact Q'.eqv_trans _ (Q'.abs (0 : Q')) _
    (Q'.abs_eqv_congr hvalue)
    (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg (Q'.le_refl' 0)))

/-- General rowwise causal compiler.  If the selected fine event implies
packet occupation and the selected coarse event implies positivity of the
coarse packet face, then the exact raw mismatch is bounded by the packet
indicator. -/
theorem coherentSupportedEventRawMismatchRatio_le_packetIndicator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (hfineSupport : ∀ fineState,
      fineEvent fineState = true →
        dyadicFinePacketPositiveB S coarseFaceId fineState = true)
    (hcoarseSupport : ∀ targetState,
      coarseEvent targetState = true →
        slabPhysicalFacePositiveB coarseFaceId targetState = true) :
    coherentSelectedRawMismatchRatio S source hpartition
        fineEvent coarseEvent ≤
      rationalBoolIndicator
        (dyadicFinePacketPositiveB S coarseFaceId source.1) := by
  cases hpacket : dyadicFinePacketPositiveB S coarseFaceId source.1
  · have hfineFalse : fineEvent source.1 = false := by
      cases hfine : fineEvent source.1
      · rfl
      · exfalso
        have hpacketTrue := hfineSupport source.1 hfine
        exact Bool.noConfusion (hpacket.symm.trans hpacketTrue)
    have hmomentZero :=
      coherentRecouplingEventMoment_eqv_zero_of_emptyPacket_of_support
        S hfineCutoff source hpartition coarseFaceId hcoarseFaceId
        hpacket coarseEvent hcoarseSupport
    have hdefect :=
      coherentRecouplingEventDefect_eqv_selectedRawMismatchRatio
        S source hpartition fineEvent coarseEvent
    have hdifferenceZero :
        coherentRecouplingEventMoment S source hpartition coarseEvent -
            rationalBoolIndicator (fineEvent source.1) ≈ 0 := by
      rw [hfineFalse]
      unfold rationalBoolIndicator
      simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_trans _ ((0 : Q') - 0) _
        (Q'.add_eqv_congr' hmomentZero (Q'.eqv_refl _))
        (by decide)
    have hratioZero :
        coherentSelectedRawMismatchRatio S source hpartition
            fineEvent coarseEvent ≈ 0 :=
      Q'.eqv_trans _
        (Q'.abs
          (coherentRecouplingEventMoment S source hpartition coarseEvent -
            rationalBoolIndicator (fineEvent source.1))) _
        (Q'.eqv_symm hdefect)
        (abs_eqv_zero_of_eqv_zero_local hdifferenceZero)
    unfold rationalBoolIndicator
    simp only [Bool.false_eq_true, if_false]
    exact Q'.le_of_eqv hratioZero
  · unfold rationalBoolIndicator
    simp only [if_true]
    exact coherentSelectedRawMismatchRatio_le_one_local
      S source hpartition fineEvent coarseEvent

/-- Averaged causal compiler: a supported selected-event mismatch is bounded
by the genuine normalized fine-law probability of its causal packet. -/
theorem coherentSupportedEventRawMismatchAverage_le_normalizedPacketMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (hfineSupport : ∀ fineState,
      fineEvent fineState = true →
        dyadicFinePacketPositiveB S coarseFaceId fineState = true)
    (hcoarseSupport : ∀ targetState,
      coarseEvent targetState = true →
        slabPhysicalFacePositiveB coarseFaceId targetState = true) :
    coherentEventRawMismatchAverage S fineEvent coarseEvent ≤
      normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S coarseFaceId) := by
  refine Q'.le_trans' _
    (coherentFineEventSourceMass S
      (dyadicFinePacketPositiveB S coarseFaceId)) _ ?_ ?_
  · unfold coherentEventRawMismatchAverage coherentFineEventSourceMass
    apply positiveCoherentWeightedDefect_mono
    intro source hpartition
    exact coherentSupportedEventRawMismatchRatio_le_packetIndicator
      S hfineCutoff source hpartition coarseFaceId hcoarseFaceId
      fineEvent coarseEvent hfineSupport hcoarseSupport
  · exact coherentFineEventSourceMass_le_normalizedSlabEventMass
      S (dyadicFinePacketPositiveB S coarseFaceId)

/-! ## 3. Compile the actual root, reflected, and joint defects -/

theorem coherentLowerPositiveTimeRawMismatchAverage_le_rootPacketMass
    (S : SlabScalePair) (G : DyadicEnrichedLowerFaceGeometry S)
    (hfineCutoff : S.fine.cutoff = 1) :
    coherentLowerPositiveTimeRawMismatchAverage S G.base ≤
      normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S G.base.coarseRoot) := by
  change coherentEventRawMismatchAverage S
      (slabPhysicalFacePositiveB G.base.fineRoot)
      (slabPhysicalFacePositiveB G.base.coarseRoot) ≤ _
  apply coherentSupportedEventRawMismatchAverage_le_normalizedPacketMass
    S hfineCutoff G.base.coarseRoot
    (by simpa only [SlabPhysicalData.faceEdges] using G.base.coarseRoot_mem)
  · intro fineState hpositive
    exact selectedFineFacePositive_implies_packetPositive
      S fineState G.base.fineRoot G.base.coarseRoot
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseRoot_mem)
      G.fineRoot_mem_packet hpositive
  · intro _ hpositive
    exact hpositive

theorem coherentReflectedPositiveTimeRawMismatchAverage_le_reflectedPacketMass
    (S : SlabScalePair) (G : DyadicEnrichedLowerFaceGeometry S)
    (hfineCutoff : S.fine.cutoff = 1) :
    coherentReflectedPositiveTimeRawMismatchAverage S G.base ≤
      normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S G.base.coarseReflected) := by
  change coherentEventRawMismatchAverage S
      (slabPhysicalFacePositiveB G.base.fineReflected)
      (slabPhysicalFacePositiveB G.base.coarseReflected) ≤ _
  apply coherentSupportedEventRawMismatchAverage_le_normalizedPacketMass
    S hfineCutoff G.base.coarseReflected
    (by simpa only [SlabPhysicalData.faceEdges] using
      G.base.coarseReflected_mem)
  · intro fineState hpositive
    exact selectedFineFacePositive_implies_packetPositive
      S fineState G.base.fineReflected G.base.coarseReflected
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseReflected_mem)
      G.fineReflected_mem_packet hpositive
  · intro _ hpositive
    exact hpositive

/-- The actual joint mismatch is charged to the one root packet.  No union
over root and reflected packets is needed. -/
theorem coherentLowerReflectedPositiveTimeRawMismatchAverage_le_rootPacketMass
    (S : SlabScalePair) (G : DyadicEnrichedLowerFaceGeometry S)
    (hfineCutoff : S.fine.cutoff = 1) :
    coherentLowerReflectedPositiveTimeRawMismatchAverage S G.base ≤
      normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S G.base.coarseRoot) := by
  change coherentEventRawMismatchAverage S
      (slabPhysicalFacePairPositiveB
        G.base.fineRoot G.base.fineReflected)
      (slabPhysicalFacePairPositiveB
        G.base.coarseRoot G.base.coarseReflected) ≤ _
  apply coherentSupportedEventRawMismatchAverage_le_normalizedPacketMass
    S hfineCutoff G.base.coarseRoot
    (by simpa only [SlabPhysicalData.faceEdges] using G.base.coarseRoot_mem)
  · intro fineState hpair
    have hroot := (Bool.and_eq_true _ _).mp hpair |>.1
    exact selectedFineFacePositive_implies_packetPositive
      S fineState G.base.fineRoot G.base.coarseRoot
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseRoot_mem)
      G.fineRoot_mem_packet hroot
  · intro _ hpair
    exact (Bool.and_eq_true _ _).mp hpair |>.1

/-! ## 4. Strict anchor endpoints for the actual three defects -/

theorem coherentLowerPositiveTimeRawMismatchAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    coherentLowerPositiveTimeRawMismatchAverage S G.base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact Q'.le_trans' _ _ _
    (coherentLowerPositiveTimeRawMismatchAverage_le_rootPacketMass
      S G hfineCutoff)
    (normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
      S cutoff half G.base.coarseRoot hfine
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseRoot_mem))

theorem coherentReflectedPositiveTimeRawMismatchAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    coherentReflectedPositiveTimeRawMismatchAverage S G.base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact Q'.le_trans' _ _ _
    (coherentReflectedPositiveTimeRawMismatchAverage_le_reflectedPacketMass
      S G hfineCutoff)
    (normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
      S cutoff half G.base.coarseReflected hfine
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseReflected_mem))

theorem coherentLowerReflectedPositiveTimeRawMismatchAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    coherentLowerReflectedPositiveTimeRawMismatchAverage S G.base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact Q'.le_trans' _ _ _
    (coherentLowerReflectedPositiveTimeRawMismatchAverage_le_rootPacketMass
      S G hfineCutoff)
    (normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
      S cutoff half G.base.coarseRoot hfine
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseRoot_mem))

theorem enrichedLowerPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedLowerPositiveTimeDefectAverage S G.base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (enrichedLowerPositiveTimeDefectAverage_eqv_rawMismatch S G.base))
    (coherentLowerPositiveTimeRawMismatchAverage_le_twoFiftySixFourTwentyFive
      S cutoff half G hfine hfineCutoff)

theorem enrichedReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedReflectedPositiveTimeDefectAverage S G.base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (enrichedReflectedPositiveTimeDefectAverage_eqv_rawMismatch S G.base))
    (coherentReflectedPositiveTimeRawMismatchAverage_le_twoFiftySixFourTwentyFive
      S cutoff half G hfine hfineCutoff)

theorem enrichedLowerReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedLowerReflectedPositiveTimeDefectAverage S G.base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (enrichedLowerReflectedPositiveTimeDefectAverage_eqv_rawMismatch
        S G.base))
    (coherentLowerReflectedPositiveTimeRawMismatchAverage_le_twoFiftySixFourTwentyFive
      S cutoff half G hfine hfineCutoff)

#print axioms selectedFineFacePositive_implies_packetPositive
#print axioms coherentRecouplingEventMoment_eqv_zero_of_emptyPacket_of_support
#print axioms coherentSupportedEventRawMismatchRatio_le_packetIndicator
#print axioms coherentSupportedEventRawMismatchAverage_le_normalizedPacketMass
#print axioms coherentLowerPositiveTimeRawMismatchAverage_le_rootPacketMass
#print axioms coherentLowerReflectedPositiveTimeRawMismatchAverage_le_rootPacketMass
#print axioms enrichedLowerPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
#print axioms enrichedReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
#print axioms enrichedLowerReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeSelectedFaceDyadicIncidence
