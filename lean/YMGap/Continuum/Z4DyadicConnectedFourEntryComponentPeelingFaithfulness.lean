/-
# Faithfulness of the four-entry component-peeling compiler

The preceding compiler canonically peels the observable-rooted component
from both accepted fine entries and both accepted coarse entries.  This file
proves that the operation loses no information needed for regrouping.

The shape code first reconstructs the geometric support of the coarse
component.  Filtering the ambient physical face list by that support fixes a
literal common scan order.  Canonical-peeling injectivity then reconstructs
the accepted fine pair and the accepted coarse pair from their terminal
states and traces.  The two retained lowering-word pairs reconstruct the
rest of the joint witness, after which the established literal-witness
compiler reconstructs the complete connected entry.

Constructive contract: support equivalence, the explicit physical
face-coordinate inverse, proof irrelevance, and deterministic peeling only;
no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling

namespace YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeelingFaithfulness

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The shape-child code fixes the geometric component support -/

theorem finePacketGlobalNonzeroConnectedEntryShapeChildCode_eq_sameTargetSupport
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (hcode : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right) :
    sameSupport (L := z4Chain.toLattice)
      (finePacketObservableTargetSupportPlaquettes
        S left.1.targets observableFaceId)
      (finePacketObservableTargetSupportPlaquettes
        S right.1.targets observableFaceId) := by
  have hshape := congrArg FinePacketConnectedComponentShapeChildCode.shape hcode
  have hchild := congrArg
    FinePacketConnectedComponentShapeChildCode.childWord hcode
  have hlocal :
      finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId left =
        finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId right := by
    calc
      finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId left =
        (finePacketGlobalNonzeroConnectedEntryChildCode
          S orientation observableFaceId left).map
            FinePacketComponentChildCode.toLocalCode :=
          (finePacketGlobalNonzeroConnectedEntryChildCode_toLocalCode
            S orientation observableFaceId left).symm
      _ = (finePacketGlobalNonzeroConnectedEntryChildCode
          S orientation observableFaceId right).map
            FinePacketComponentChildCode.toLocalCode :=
          congrArg
            (List.map FinePacketComponentChildCode.toLocalCode) hchild
      _ = finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId right :=
          finePacketGlobalNonzeroConnectedEntryChildCode_toLocalCode
            S orientation observableFaceId right
  apply finePacketGlobalNonzeroConnectedEntryEntropyCode_eq_sameTargetSupport
    S orientation observableFaceId hobservableFace left right
  apply Eq.trans
  · exact congrArg
      (fun shape => FinePacketConnectedComponentEntropyCode.mk shape
        (finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId left)) hshape
  · exact congrArg
      (fun localCode => FinePacketConnectedComponentEntropyCode.mk
        (finePacketGlobalNonzeroConnectedEntryShapeCode
          S orientation observableFaceId hobservableFace right)
        localCode) hlocal

private theorem targetComponent_mem_iff_of_sameTargetSupport
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (finePacketObservableTargetSupportPlaquettes
        S left.1.targets observableFaceId)
      (finePacketObservableTargetSupportPlaquettes
        S right.1.targets observableFaceId))
    (faceId : Nat) (hphysical : faceId ∈ S.coarse.faceEdges) :
    faceId ∈ finePacketGlobalConnectedEntryTargetComponent
        S observableFaceId left.1 ↔
      faceId ∈ finePacketGlobalConnectedEntryTargetComponent
        S observableFaceId right.1 := by
  constructor
  · intro hleft
    have hplaquette := hsupport.1 _
      (slabPlaquetteAt_mem_finePacketObservableTargetSupportPlaquettes
        S left.1.targets observableFaceId faceId hleft)
    let rightFaceId := finePacketObservableTargetSupportFaceValue
      S right.1.targets observableFaceId
        (slabPlaquetteAt S.coarse.extent faceId)
    have hright : rightFaceId ∈
        finePacketGlobalConnectedEntryTargetComponent
          S observableFaceId right.1 :=
      finePacketObservableTargetSupportFaceValue_mem
        S right.1.targets observableFaceId
          (finePacketGlobalConnectedEntry_observable_mem_targetComponent
            S observableFaceId hobservableFace right.1)
          (slabPlaquetteAt S.coarse.extent faceId)
    have heq : slabPlaquetteAt S.coarse.extent rightFaceId =
        slabPlaquetteAt S.coarse.extent faceId :=
      finePacketObservableTargetSupportFaceValue_projection
        S right.1.targets observableFaceId
          (slabPlaquetteAt S.coarse.extent faceId) hplaquette
    have hrightPhysical : rightFaceId ∈ S.coarse.faceEdges :=
      finePacketObservableTargetSupportComponent_face_mem_physical
        S right.1.targets observableFaceId hobservableFace
          (finePacketGlobalConnectedEntryPath
            S observableFaceId hobservableFace right.1).observable_targetStates_ne
          rightFaceId hright
    have hid : rightFaceId = faceId :=
      slabPlaquetteAt_injective_on_physical hrightPhysical hphysical heq
    rw [← hid]
    exact hright
  · intro hright
    have hplaquette := hsupport.2 _
      (slabPlaquetteAt_mem_finePacketObservableTargetSupportPlaquettes
        S right.1.targets observableFaceId faceId hright)
    let leftFaceId := finePacketObservableTargetSupportFaceValue
      S left.1.targets observableFaceId
        (slabPlaquetteAt S.coarse.extent faceId)
    have hleft : leftFaceId ∈
        finePacketGlobalConnectedEntryTargetComponent
          S observableFaceId left.1 :=
      finePacketObservableTargetSupportFaceValue_mem
        S left.1.targets observableFaceId
          (finePacketGlobalConnectedEntry_observable_mem_targetComponent
            S observableFaceId hobservableFace left.1)
          (slabPlaquetteAt S.coarse.extent faceId)
    have heq : slabPlaquetteAt S.coarse.extent leftFaceId =
        slabPlaquetteAt S.coarse.extent faceId :=
      finePacketObservableTargetSupportFaceValue_projection
        S left.1.targets observableFaceId
          (slabPlaquetteAt S.coarse.extent faceId) hplaquette
    have hleftPhysical : leftFaceId ∈ S.coarse.faceEdges :=
      finePacketObservableTargetSupportComponent_face_mem_physical
        S left.1.targets observableFaceId hobservableFace
          (finePacketGlobalConnectedEntryPath
            S observableFaceId hobservableFace left.1).observable_targetStates_ne
          leftFaceId hleft
    have hid : leftFaceId = faceId :=
      slabPlaquetteAt_injective_on_physical hleftPhysical hphysical heq
    rw [← hid]
    exact hleft

/-- Equal shape-child codes give the identical coarse scan list, not merely
the same unordered support.  The order is inherited from the fixed ambient
physical face list. -/
theorem finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_eq_of_shapeChildCode_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (hcode : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right) :
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId left =
      finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId right := by
  have hsupport :=
    finePacketGlobalNonzeroConnectedEntryShapeChildCode_eq_sameTargetSupport
      S orientation observableFaceId hobservableFace left right hcode
  unfold finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
  apply List.filter_congr
  intro faceId hphysical
  have hiff := targetComponent_mem_iff_of_sameTargetSupport
    S orientation observableFaceId hobservableFace left right
      hsupport faceId hphysical
  by_cases hleft : faceId ∈ finePacketGlobalConnectedEntryTargetComponent
      S observableFaceId left.1
  · have hright := hiff.mp hleft
    simp [hleft, hright]
  · have hright : faceId ∉ finePacketGlobalConnectedEntryTargetComponent
        S observableFaceId right.1 := by
      intro hmem
      exact hleft (hiff.mpr hmem)
    simp [hleft, hright]

theorem finePacketGlobalNonzeroConnectedEntryFineComponentFaces_eq_of_shapeChildCode_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (hcode : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right) :
    finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId left =
      finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId right := by
  unfold finePacketGlobalNonzeroConnectedEntryFineComponentFaces
  rw [finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_eq_of_shapeChildCode_eq
    S orientation observableFaceId hobservableFace left right hcode]

/-! ## 2. The terminal compiler is injective -/

abbrev FinePacketConnectedFourEntryTerminalCompilerCode
    (S : SlabScalePair) :=
  Nat × (FinePacketConnectedComponentShapeChildCode ×
    FinePacketConnectedFourEntryComponentPeelingCode S)

def finePacketGlobalNonzeroConnectedExpandedWitnessTerminalCompiler
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryTerminalCompilerCode S :=
  (finePacketGlobalNonzeroConnectedEntryComponentSize
      S orientation observableFaceId expanded.1,
    (finePacketGlobalNonzeroConnectedEntryShapeChildCode
      S orientation observableFaceId hobservableFace expanded.1,
    finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
      S orientation observableFaceId hobservableFace expanded))

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

private theorem fineAcceptedState_eq_of_shape_peeling_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hshape : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left.1 =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right.1)
    (hpeeling :
      finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
          S orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
          S orientation observableFaceId hobservableFace right) :
    left.2.1.1 = right.2.1.1 := by
  have hfineFaces :=
    finePacketGlobalNonzeroConnectedEntryFineComponentFaces_eq_of_shapeChildCode_eq
      S orientation observableFaceId hobservableFace left.1 right.1 hshape
  have hfineOutput := congrArg
    (fun code : FinePacketConnectedFourEntryComponentPeelingCode S =>
      code.1.1) hpeeling
  change slabAcceptedPairCanonicalPeeling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId left.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
        S orientation observableFaceId hobservableFace left.1)
      left.2.1.1 =
    slabAcceptedPairCanonicalPeeling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId right.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
        S orientation observableFaceId hobservableFace right.1)
      right.2.1.1 at hfineOutput
  exact slabAcceptedPairCanonicalPeeling_injective_of_faces_eq
    (finePacketFineUnitCouplingSlabPhysicalData S)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId left.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId right.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace left.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace right.1)
    hfineFaces left.2.1.1 right.2.1.1 hfineOutput

private theorem coarseAcceptedState_eq_of_shape_peeling_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hshape : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left.1 =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right.1)
    (hpeeling :
      finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
          S orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
          S orientation observableFaceId hobservableFace right) :
    finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S left.2.1 =
      finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S right.2.1 := by
  have hcoarseFaces :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_eq_of_shapeChildCode_eq
      S orientation observableFaceId hobservableFace left.1 right.1 hshape
  have hcoarseOutput := congrArg
    (fun code : FinePacketConnectedFourEntryComponentPeelingCode S =>
      code.1.2) hpeeling
  change slabAcceptedPairCanonicalPeeling
      (coarseUnitCouplingSlabPhysicalData S)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId left.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
        S orientation observableFaceId hobservableFace left.1)
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S left.2.1) =
    slabAcceptedPairCanonicalPeeling
      (coarseUnitCouplingSlabPhysicalData S)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId right.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
        S orientation observableFaceId hobservableFace right.1)
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S right.2.1) at hcoarseOutput
  exact slabAcceptedPairCanonicalPeeling_injective_of_faces_eq
    (coarseUnitCouplingSlabPhysicalData S)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId left.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId right.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace left.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace right.1)
    hcoarseFaces
    (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
      S left.2.1)
    (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
      S right.2.1) hcoarseOutput

private theorem jointWitness_eq_of_shape_peeling_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hshape : finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace left.1 =
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace right.1)
    (hpeeling :
      finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
          S orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessComponentPeelingCode
          S orientation observableFaceId hobservableFace right) :
    left.2.1 = right.2.1 := by
  have htargetFirst : left.2.1.2.1 = right.2.1.2.1 :=
    Prod.ext
      (congrArg
        (fun code : FinePacketConnectedFourEntryComponentPeelingCode S =>
          code.2.1) hpeeling)
      (congrArg (fun state : SlabAcceptedTwoReplicaState
          (coarseUnitCouplingSlabPhysicalData S) => state.1)
        (coarseAcceptedState_eq_of_shape_peeling_eq
          S orientation observableFaceId hobservableFace
            left right hshape hpeeling))
  have htargetSecond : left.2.1.2.2 = right.2.1.2.2 :=
    Prod.ext
      (congrArg
        (fun code : FinePacketConnectedFourEntryComponentPeelingCode S =>
          code.2.2) hpeeling)
      (congrArg (fun state : SlabAcceptedTwoReplicaState
          (coarseUnitCouplingSlabPhysicalData S) => state.2)
        (coarseAcceptedState_eq_of_shape_peeling_eq
          S orientation observableFaceId hobservableFace
            left right hshape hpeeling))
  exact Prod.ext
    (fineAcceptedState_eq_of_shape_peeling_eq
      S orientation observableFaceId hobservableFace
        left right hshape hpeeling)
    (Prod.ext htargetFirst htargetSecond)

/-- Terminal states, complete peel traces, and the two lowering-word pairs
reconstruct the complete expanded connected witness. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessTerminalCompiler_injective
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    Function.Injective
      (finePacketGlobalNonzeroConnectedExpandedWitnessTerminalCompiler
        S orientation observableFaceId hobservableFace) := by
  intro left right hcode
  have hsize := congrArg
    (fun code : FinePacketConnectedFourEntryTerminalCompilerCode S => code.1)
    hcode
  have hshape := congrArg
    (fun code : FinePacketConnectedFourEntryTerminalCompilerCode S => code.2.1)
    hcode
  have hpeeling := congrArg
    (fun code : FinePacketConnectedFourEntryTerminalCompilerCode S => code.2.2)
    hcode
  have hwitness := jointWitness_eq_of_shape_peeling_eq
    S orientation observableFaceId hobservableFace
      left right hshape hpeeling
  apply finePacketGlobalNonzeroConnectedExpandedWitnessCompiler_injective
    S orientation observableFaceId hobservableFace
  exact Prod.ext hsize (Prod.ext hshape hwitness)

#print axioms finePacketGlobalNonzeroConnectedEntryShapeChildCode_eq_sameTargetSupport
#print axioms finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_eq_of_shapeChildCode_eq
#print axioms finePacketGlobalNonzeroConnectedEntryFineComponentFaces_eq_of_shapeChildCode_eq
#print axioms FinePacketConnectedFourEntryTerminalCompilerCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessTerminalCompiler
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessTerminalCompiler_injective

end YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeelingFaithfulness
