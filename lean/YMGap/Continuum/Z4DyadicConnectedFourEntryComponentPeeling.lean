/-
# Canonically peel the connected component in all four accepted entries

One expanded connected witness contains two accepted fine entries and two
accepted coarse entries.  Its observable-rooted target component is a list
of coarse faces; the corresponding fine scan is the union of the four
dyadic children above every face in that component.

This file runs the established deterministic accepted paired peeling on
both scales.  The output retains both terminal-and-trace pairs together with
the two coarse lowering-word pairs.  Both terminals are proved to vanish on
their respective scanned component faces.  This is the concrete two-scale
component-erasure map needed before weighted terminal regrouping.

Constructive contract: computed component lists and deterministic accepted
peeling only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective

namespace YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4DyadicSpinFourLoweringWitnessCarrier
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The coarse component and its fine-child preimage -/

def finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : List Nat :=
  finePacketGlobalConnectedEntryTargetComponent
    S observableFaceId entry.1

def finePacketGlobalNonzeroConnectedEntryFineComponentFaces
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : List Nat :=
  (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
    S orientation observableFaceId entry).flatMap
      (dyadicCoarseFaceFineFaceIds S)

theorem finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (faceId : Nat)
    (hface : faceId ∈
      finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId entry) :
    faceId ∈ slabPhysicalFaceEdges
      (coarseUnitCouplingSlabPhysicalData S).extent := by
  let path := finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry.1
  have hphysical :=
    finePacketObservableTargetSupportComponent_face_mem_physical
      S entry.1.targets observableFaceId hobservableFace
        path.observable_targetStates_ne faceId hface
  simpa only [coarseUnitCouplingSlabPhysicalData] using hphysical

theorem finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (fineFaceId : Nat)
    (hface : fineFaceId ∈
      finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId entry) :
    fineFaceId ∈ slabPhysicalFaceEdges
      (finePacketFineUnitCouplingSlabPhysicalData S).extent := by
  unfold finePacketGlobalNonzeroConnectedEntryFineComponentFaces at hface
  obtain ⟨coarseFaceId, hcomponent, hchild⟩ := List.mem_flatMap.mp hface
  have hcoarse : coarseFaceId ∈ S.coarse.faceEdges := by
    simpa only [coarseUnitCouplingSlabPhysicalData] using
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
        S orientation observableFaceId hobservableFace entry
          coarseFaceId hcomponent)
  have hglobal : fineFaceId ∈ wholeSlabDyadicPacketFineFaceIds S := by
    unfold wholeSlabDyadicPacketFineFaceIds
    exact List.mem_flatMap.mpr ⟨coarseFaceId, hcoarse, hchild⟩
  have hfine := wholeSlabDyadicPacketFineFaceIds_subset_physical S hglobal
  simpa only [finePacketFineUnitCouplingSlabPhysicalData] using hfine

/-! ## 2. Accepted coarse pair and the two deterministic peels -/

def finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
    (S : SlabScalePair)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) :
    SlabAcceptedTwoReplicaState (coarseUnitCouplingSlabPhysicalData S) :=
  (witness.2.1.2, witness.2.2.2)

abbrev FinePacketConnectedFourEntryComponentPeelingOutput
    (S : SlabScalePair) :=
  SlabAcceptedPairedCanonicalPeelingOutput
      (finePacketFineUnitCouplingSlabPhysicalData S) ×
    SlabAcceptedPairedCanonicalPeelingOutput
      (coarseUnitCouplingSlabPhysicalData S)

def finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryComponentPeelingOutput S :=
  (slabAcceptedPairCanonicalPeeling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
        S orientation observableFaceId hobservableFace expanded.1)
      expanded.2.1.1,
    slabAcceptedPairCanonicalPeeling
      (coarseUnitCouplingSlabPhysicalData S)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
        S orientation observableFaceId hobservableFace expanded.1)
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S expanded.2.1))

/-- Both fine terminal fields vanish on every dyadic child above the selected
coarse component. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling_fine_final_zero
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (fineFaceId : Nat)
    (hface : fineFaceId ∈
      finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId expanded.1) :
    let output := finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling
      S orientation observableFaceId hobservableFace expanded
    output.1.1.1.1.1 fineFaceId = 0 ∧
      output.1.1.2.1.1 fineFaceId = 0 := by
  exact slabAcceptedPairCanonicalPeeling_final_zero
    (finePacketFineUnitCouplingSlabPhysicalData S)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId expanded.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace expanded.1)
    expanded.2.1.1 fineFaceId hface

/-- Both coarse terminal fields vanish on every face in the selected target
component. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling_coarse_final_zero
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (coarseFaceId : Nat)
    (hface : coarseFaceId ∈
      finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId expanded.1) :
    let output := finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling
      S orientation observableFaceId hobservableFace expanded
    output.2.1.1.1.1 coarseFaceId = 0 ∧
      output.2.1.2.1.1 coarseFaceId = 0 := by
  exact slabAcceptedPairCanonicalPeeling_final_zero
    (coarseUnitCouplingSlabPhysicalData S)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId expanded.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace expanded.1)
    (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
      S expanded.2.1) coarseFaceId hface

/-! ## 3. Preserve the lowering words beside the two peel traces -/

abbrev FinePacketConnectedFourEntryComponentPeelingCode
    (S : SlabScalePair) :=
  FinePacketConnectedFourEntryComponentPeelingOutput S ×
    (FinePacketLoweringWitnessPair × FinePacketLoweringWitnessPair)

def finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryComponentPeelingCode S :=
  (finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling
      S orientation observableFaceId hobservableFace expanded,
    (expanded.2.1.2.1.1, expanded.2.1.2.2.1))

#print axioms finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
#print axioms finePacketGlobalNonzeroConnectedEntryFineComponentFaces
#print axioms finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
#print axioms finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
#print axioms finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
#print axioms FinePacketConnectedFourEntryComponentPeelingOutput
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling_fine_final_zero
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeeling_coarse_final_zero
#print axioms FinePacketConnectedFourEntryComponentPeelingCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode

end YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
