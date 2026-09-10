/-
# Faithfulness of the connected expanded-witness compiler

The flattened connected carrier retains a shape-child code and a literal
four-entry SU(2) witness.  Before it can be regrouped by a terminal-removal
map, the latter must be shown to remember the physical source and target
labels from which its dependent fiber was built.

This file proves those four projection identities and packages the natural
compiler `(component size, shape-child code, literal witness)`.  Equality of
compiled codes reconstructs the complete proof-carrying connected entry and
its attached witness.  Thus the compiler is injective without classical
choice or any cardinality argument.

Constructive contract: dependent membership elimination and proof
irrelevance only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier

namespace YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4DyadicPhysicalTermExpandedWitnessFiber

/-! ## 1. The literal witness remembers both fine sources -/

theorem finePacketOrientedJointUnitExpandedWitness_fineFirst_physical_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings)
    (witness : FinePacketOrientedJointUnitExpandedWitness S)
    (hwitness : witness ∈
      finePacketOrientedJointUnitExpandedWitnessCarrier
        S orientation first second pair hleft hright) :
    witness.1.1.1.1 = first.1 := by
  have hjoint := (mem_cartesian_iff _ _ witness).mp hwitness
  have hfine := (mem_cartesian_iff _ _ witness.1).mp hjoint.1
  exact slabPhysicalExpandedEntryBlock_physical_eq
    (finePacketFineUnitCouplingSlabPhysicalData S) first.1
    (finePhysical_mem_unitCoupling S first.1 first.2.1)
    witness.1.1 hfine.1

theorem finePacketOrientedJointUnitExpandedWitness_fineSecond_physical_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings)
    (witness : FinePacketOrientedJointUnitExpandedWitness S)
    (hwitness : witness ∈
      finePacketOrientedJointUnitExpandedWitnessCarrier
        S orientation first second pair hleft hright) :
    witness.1.2.1.1 = second.1 := by
  have hjoint := (mem_cartesian_iff _ _ witness).mp hwitness
  have hfine := (mem_cartesian_iff _ _ witness.1).mp hjoint.1
  exact slabPhysicalExpandedEntryBlock_physical_eq
    (finePacketFineUnitCouplingSlabPhysicalData S) second.1
    (finePhysical_mem_unitCoupling S second.1 second.2.1)
    witness.1.2 hfine.2

/-! ## 2. The literal witness remembers both coarse targets -/

theorem finePacketOrientedJointUnitExpandedWitness_coarseFirst_physical_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings)
    (witness : FinePacketOrientedJointUnitExpandedWitness S)
    (hwitness : witness ∈
      finePacketOrientedJointUnitExpandedWitnessCarrier
        S orientation first second pair hleft hright) :
    witness.2.1.2.1.1 = pair.1 := by
  have hjoint := (mem_cartesian_iff _ _ witness).mp hwitness
  cases orientation with
  | forward =>
      have htarget := (mem_cartesian_iff _ _ witness.2).mp hjoint.2
      exact finePacketLocalizedUnitTargetExpandedWitness_physical_eq
        S first.1 first.1 second.1 pair.1 hleft witness.2.1 htarget.1
  | reverse =>
      have htarget := (mem_cartesian_iff _ _ witness.2).mp hjoint.2
      exact finePacketLocalizedUnitTargetExpandedWitness_physical_eq
        S second.1 first.1 second.1 pair.1 hleft witness.2.1 htarget.1

theorem finePacketOrientedJointUnitExpandedWitness_coarseSecond_physical_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings)
    (witness : FinePacketOrientedJointUnitExpandedWitness S)
    (hwitness : witness ∈
      finePacketOrientedJointUnitExpandedWitnessCarrier
        S orientation first second pair hleft hright) :
    witness.2.2.2.1.1 = pair.2 := by
  have hjoint := (mem_cartesian_iff _ _ witness).mp hwitness
  cases orientation with
  | forward =>
      have htarget := (mem_cartesian_iff _ _ witness.2).mp hjoint.2
      exact finePacketLocalizedUnitTargetExpandedWitness_physical_eq
        S second.1 first.1 second.1 pair.2 hright witness.2.2 htarget.2
  | reverse =>
      have htarget := (mem_cartesian_iff _ _ witness.2).mp hjoint.2
      exact finePacketLocalizedUnitTargetExpandedWitness_physical_eq
        S first.1 first.1 second.1 pair.2 hright witness.2.2 htarget.2

/-! ## 3. An injective observable compiler -/

abbrev FinePacketConnectedExpandedWitnessCompilerCode
    (S : SlabScalePair) :=
  Nat × (FinePacketConnectedComponentShapeChildCode ×
    FinePacketOrientedJointUnitExpandedWitness S)

private theorem finePacketGlobalConnectedEntry_eq_of_sources_targets_eq
    {S : SlabScalePair} {observableFaceId : Nat}
    {left right : FinePacketGlobalConnectedEntry S observableFaceId}
    (hsources : left.sources = right.sources)
    (htargets : left.targets = right.targets) :
    left = right := by
  cases left with
  | mk leftSources leftTargets leftMem =>
      cases right with
      | mk rightSources rightTargets rightMem =>
          dsimp only at hsources htargets
          cases hsources
          cases htargets
          rfl

def finePacketGlobalNonzeroConnectedExpandedWitnessCompiler
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedExpandedWitnessCompilerCode S :=
  (finePacketGlobalNonzeroConnectedEntryComponentSize
      S orientation observableFaceId expanded.1,
    (finePacketGlobalNonzeroConnectedEntryShapeChildCode
      S orientation observableFaceId hobservableFace expanded.1,
    expanded.2.1))

/-- The literal four-entry witness reconstructs both physical source rows
and both physical target rows.  The shape-child field remains available for
the later weighted counting argument, but no extra reconstruction assumption
is needed. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessCompiler_injective
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    Function.Injective
      (finePacketGlobalNonzeroConnectedExpandedWitnessCompiler
        S orientation observableFaceId hobservableFace) := by
  intro left right hcode
  have hwitness : left.2.1 = right.2.1 :=
    congrArg (fun code : FinePacketConnectedExpandedWitnessCompilerCode S =>
      code.2.2) hcode
  have hsourceFirst : left.1.1.sources.1.1 = right.1.1.sources.1.1 := by
    calc
      left.1.1.sources.1.1 = left.2.1.1.1.1.1 :=
        (finePacketOrientedJointUnitExpandedWitness_fineFirst_physical_eq
          S orientation left.1.1.sources.1 left.1.1.sources.2
            left.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId left.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId left.1)
            left.2.1 left.2.2).symm
      _ = right.2.1.1.1.1.1 := congrArg (fun witness => witness.1.1.1.1) hwitness
      _ = right.1.1.sources.1.1 :=
        finePacketOrientedJointUnitExpandedWitness_fineFirst_physical_eq
          S orientation right.1.1.sources.1 right.1.1.sources.2
            right.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId right.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId right.1)
            right.2.1 right.2.2
  have hsourceSecond : left.1.1.sources.2.1 = right.1.1.sources.2.1 := by
    calc
      left.1.1.sources.2.1 = left.2.1.1.2.1.1 :=
        (finePacketOrientedJointUnitExpandedWitness_fineSecond_physical_eq
          S orientation left.1.1.sources.1 left.1.1.sources.2
            left.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId left.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId left.1)
            left.2.1 left.2.2).symm
      _ = right.2.1.1.2.1.1 := congrArg (fun witness => witness.1.2.1.1) hwitness
      _ = right.1.1.sources.2.1 :=
        finePacketOrientedJointUnitExpandedWitness_fineSecond_physical_eq
          S orientation right.1.1.sources.1 right.1.1.sources.2
            right.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId right.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId right.1)
            right.2.1 right.2.2
  have htargetFirst : left.1.1.targets.1 = right.1.1.targets.1 := by
    calc
      left.1.1.targets.1 = left.2.1.2.1.2.1.1 :=
        (finePacketOrientedJointUnitExpandedWitness_coarseFirst_physical_eq
          S orientation left.1.1.sources.1 left.1.1.sources.2
            left.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId left.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId left.1)
            left.2.1 left.2.2).symm
      _ = right.2.1.2.1.2.1.1 :=
        congrArg (fun witness => witness.2.1.2.1.1) hwitness
      _ = right.1.1.targets.1 :=
        finePacketOrientedJointUnitExpandedWitness_coarseFirst_physical_eq
          S orientation right.1.1.sources.1 right.1.1.sources.2
            right.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId right.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId right.1)
            right.2.1 right.2.2
  have htargetSecond : left.1.1.targets.2 = right.1.1.targets.2 := by
    calc
      left.1.1.targets.2 = left.2.1.2.2.2.1.1 :=
        (finePacketOrientedJointUnitExpandedWitness_coarseSecond_physical_eq
          S orientation left.1.1.sources.1 left.1.1.sources.2
            left.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId left.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId left.1)
            left.2.1 left.2.2).symm
      _ = right.2.1.2.2.2.1.1 :=
        congrArg (fun witness => witness.2.2.2.1.1) hwitness
      _ = right.1.1.targets.2 :=
        finePacketOrientedJointUnitExpandedWitness_coarseSecond_physical_eq
          S orientation right.1.1.sources.1 right.1.1.sources.2
            right.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId right.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId right.1)
            right.2.1 right.2.2
  have hsources : left.1.1.sources = right.1.1.sources := by
    exact Prod.ext (Subtype.ext hsourceFirst) (Subtype.ext hsourceSecond)
  have htargets : left.1.1.targets = right.1.1.targets :=
    Prod.ext htargetFirst htargetSecond
  have hentryValue : left.1.1 = right.1.1 :=
    finePacketGlobalConnectedEntry_eq_of_sources_targets_eq hsources htargets
  have hentry : left.1 = right.1 := Subtype.ext hentryValue
  cases left with
  | mk leftEntry leftWitness =>
      cases right with
      | mk rightEntry rightWitness =>
          dsimp only at hentry hwitness ⊢
          cases hentry
          have hwitnessSubtype : leftWitness = rightWitness :=
            Subtype.ext hwitness
          cases hwitnessSubtype
          rfl

#print axioms finePacketOrientedJointUnitExpandedWitness_fineFirst_physical_eq
#print axioms finePacketOrientedJointUnitExpandedWitness_fineSecond_physical_eq
#print axioms finePacketOrientedJointUnitExpandedWitness_coarseFirst_physical_eq
#print axioms finePacketOrientedJointUnitExpandedWitness_coarseSecond_physical_eq
#print axioms FinePacketConnectedExpandedWitnessCompilerCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessCompiler
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessCompiler_injective

end YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness
