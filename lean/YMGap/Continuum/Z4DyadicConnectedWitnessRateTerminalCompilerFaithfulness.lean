/-
# Faithfulness of the common-rate terminal compiler

The common-rate canonical peel is the literal terminal object on which the
weighted source telescope lands.  This module proves that its two terminal
states and complete traces, together with the geometric shape-child code and
the two lowering-word pairs, still reconstruct the original four-entry SU(2)
witness.

The proof first uses equality of shape-child codes to identify the fine and
coarse component scan lists.  Canonical-peeling injectivity reconstructs the
two accepted states after rebasing to the common rate.  The coupling-rebase
map is itself injective, so the original unit-coupling accepted states follow.
The retained lowering words then reconstruct the complete joint witness, and
the established observable compiler reconstructs the connected entry.

Constructive contract: deterministic peeling, injective coupling transport,
support equivalence, and proof irrelevance only; no classical choice, proof
hole, trusted external computation, computability escape, heartbeat increase,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeelingFaithfulness
import YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalCompilerFaithfulness

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeelingFaithfulness
open YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The minimal common-rate terminal code -/

abbrev FinePacketConnectedFourEntryRateTerminalCompilerCode
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :=
  Nat × (FinePacketConnectedComponentShapeChildCode ×
    (FinePacketConnectedFourEntryRateCanonicalPeelingOutput
        S rate hrate0 ×
      (FinePacketLoweringWitnessPair × FinePacketLoweringWitnessPair)))

def finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalCompiler
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryRateTerminalCompilerCode
      S rate hrate0 :=
  (finePacketGlobalNonzeroConnectedEntryComponentSize
      S orientation observableFaceId expanded.1,
    (finePacketGlobalNonzeroConnectedEntryShapeChildCode
      S orientation observableFaceId hobservableFace expanded.1,
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded,
    (expanded.2.1.2.1.1, expanded.2.1.2.2.1))))

/-! ## 2. Equal terminal codes reconstruct both accepted pairs -/

private theorem slabAcceptedPairCanonicalPeeling_injective_of_faces_eq
    (D : SlabPhysicalData)
    (leftFaces rightFaces : List Nat)
    (hleftPhysical : ∀ faceId, faceId ∈ leftFaces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (hrightPhysical : ∀ faceId, faceId ∈ rightFaces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (hfaces : leftFaces = rightFaces)
    (leftState rightState : SlabAcceptedTwoReplicaState D)
    (houtput : slabAcceptedPairCanonicalPeeling
        D leftFaces hleftPhysical leftState =
      slabAcceptedPairCanonicalPeeling
        D rightFaces hrightPhysical rightState) :
    leftState = rightState := by
  cases hfaces
  exact slabAcceptedPairCanonicalPeeling_injective
    D leftFaces hleftPhysical leftState rightState (by simpa using houtput)

theorem fineUnitAcceptedState_eq_of_shape_ratePeeling_eq
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hshape : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left.1 =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right.1)
    (hpeeling :
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right) :
    left.2.1.1 = right.2.1.1 := by
  have hfineFaces :=
    finePacketGlobalNonzeroConnectedEntryFineComponentFaces_eq_of_shapeChildCode_eq
      S orientation observableFaceId hobservableFace left.1 right.1 hshape
  have hfineOutput := congrArg
    (fun output : FinePacketConnectedFourEntryRateCanonicalPeelingOutput
        S rate hrate0 => output.1) hpeeling
  change slabAcceptedPairCanonicalPeeling
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId left.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace left.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        rate hrate0 left.2.1.1) =
    slabAcceptedPairCanonicalPeeling
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId right.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace right.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        rate hrate0 right.2.1.1) at hfineOutput
  apply slabAcceptedTwoReplicaStateAtCoupling_injective
    (finePacketFineUnitCouplingSlabPhysicalData S) rate hrate0
  exact slabAcceptedPairCanonicalPeeling_injective_of_faces_eq
    (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId left.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId right.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace left.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace right.1)
    hfineFaces
    (slabAcceptedTwoReplicaStateAtCoupling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      rate hrate0 left.2.1.1)
    (slabAcceptedTwoReplicaStateAtCoupling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      rate hrate0 right.2.1.1)
    hfineOutput

theorem coarseUnitAcceptedState_eq_of_shape_ratePeeling_eq
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hshape : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left.1 =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right.1)
    (hpeeling :
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right) :
    finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S left.2.1 =
      finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S right.2.1 := by
  have hcoarseFaces :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_eq_of_shapeChildCode_eq
      S orientation observableFaceId hobservableFace left.1 right.1 hshape
  have hcoarseOutput := congrArg
    (fun output : FinePacketConnectedFourEntryRateCanonicalPeelingOutput
        S rate hrate0 => output.2) hpeeling
  change slabAcceptedPairCanonicalPeeling
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId left.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace left.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        rate hrate0
        (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
          S left.2.1)) =
    slabAcceptedPairCanonicalPeeling
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId right.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace right.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        rate hrate0
        (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
          S right.2.1)) at hcoarseOutput
  apply slabAcceptedTwoReplicaStateAtCoupling_injective
    (coarseUnitCouplingSlabPhysicalData S) rate hrate0
  exact slabAcceptedPairCanonicalPeeling_injective_of_faces_eq
    (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId left.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId right.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace left.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace right.1)
    hcoarseFaces
    (slabAcceptedTwoReplicaStateAtCoupling
      (coarseUnitCouplingSlabPhysicalData S)
      rate hrate0
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S left.2.1))
    (slabAcceptedTwoReplicaStateAtCoupling
      (coarseUnitCouplingSlabPhysicalData S)
      rate hrate0
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S right.2.1))
    hcoarseOutput

/-! ## 3. The common-rate terminal compiler is injective -/

private theorem jointWitness_eq_of_shape_ratePeeling_lowering_eq
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hshape : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left.1 =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right.1)
    (hpeeling :
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right)
    (hloweringFirst : left.2.1.2.1.1 = right.2.1.2.1.1)
    (hloweringSecond : left.2.1.2.2.1 = right.2.1.2.2.1) :
    left.2.1 = right.2.1 := by
  have hcoarse := coarseUnitAcceptedState_eq_of_shape_ratePeeling_eq
    S rate hrate0 orientation observableFaceId hobservableFace
      left right hshape hpeeling
  have htargetFirst : left.2.1.2.1 = right.2.1.2.1 :=
    Prod.ext hloweringFirst
      (congrArg (fun state : SlabAcceptedTwoReplicaState
          (coarseUnitCouplingSlabPhysicalData S) => state.1) hcoarse)
  have htargetSecond : left.2.1.2.2 = right.2.1.2.2 :=
    Prod.ext hloweringSecond
      (congrArg (fun state : SlabAcceptedTwoReplicaState
          (coarseUnitCouplingSlabPhysicalData S) => state.2) hcoarse)
  exact Prod.ext
    (fineUnitAcceptedState_eq_of_shape_ratePeeling_eq
      S rate hrate0 orientation observableFaceId hobservableFace
        left right hshape hpeeling)
    (Prod.ext htargetFirst htargetSecond)

/-- Component size, shape-child code, the two common-rate terminal states and
their full traces, and the two lowering-word pairs reconstruct the complete
expanded connected witness. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalCompiler_injective
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    Function.Injective
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalCompiler
        S rate hrate0 orientation observableFaceId hobservableFace) := by
  intro left right hcode
  have hsize := congrArg
    (fun code : FinePacketConnectedFourEntryRateTerminalCompilerCode
        S rate hrate0 => code.1) hcode
  have hshape := congrArg
    (fun code : FinePacketConnectedFourEntryRateTerminalCompilerCode
        S rate hrate0 => code.2.1) hcode
  have hpeeling := congrArg
    (fun code : FinePacketConnectedFourEntryRateTerminalCompilerCode
        S rate hrate0 => code.2.2.1) hcode
  have hloweringFirst := congrArg
    (fun code : FinePacketConnectedFourEntryRateTerminalCompilerCode
        S rate hrate0 => code.2.2.2.1) hcode
  have hloweringSecond := congrArg
    (fun code : FinePacketConnectedFourEntryRateTerminalCompilerCode
        S rate hrate0 => code.2.2.2.2) hcode
  have hwitness := jointWitness_eq_of_shape_ratePeeling_lowering_eq
    S rate hrate0 orientation observableFaceId hobservableFace
      left right hshape hpeeling hloweringFirst hloweringSecond
  apply finePacketGlobalNonzeroConnectedExpandedWitnessCompiler_injective
    S orientation observableFaceId hobservableFace
  exact Prod.ext hsize (Prod.ext hshape hwitness)

#print axioms FinePacketConnectedFourEntryRateTerminalCompilerCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalCompiler
#print axioms fineUnitAcceptedState_eq_of_shape_ratePeeling_eq
#print axioms coarseUnitAcceptedState_eq_of_shape_ratePeeling_eq
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalCompiler_injective

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalCompilerFaithfulness
