/-
# Count one terminal-skeleton row fiber by its adaptive traces

At a fixed terminal-skeleton row, a structural code can vary only through
the adaptive words in its fine and coarse peeling traces.  This module makes
that statement literal: the structural fiber maps injectively to the product
of the two dependent trace carriers.  The carrier theorem therefore gives
the exact two-scale entropy count

  componentAdaptiveEntropyBase ^ (fineMass + coarseMass).

Physical target words in the row code are load-bearing.  Together with the
source words they reconstruct the connected physical entry, and hence its
component size and shape-child code; no separate geometric multiplicity is
introduced at this layer.

Constructive contract: finite filtering, first-witness search already proved
in the preceding module, and explicit dependent trace carriers only; no
classical choice, proof hole, trusted external computation, computability
escape, heartbeat increase, or new trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.FiniteBoolGraphSimplePaths.FiniteListBound
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness

/-! ## 1. The literal structural row fiber and its trace compiler -/

def finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    List FinePacketConnectedRateProfiledStructuralCode :=
  (finePacketConnectedRateProfiledStructuralCodes
      S rate hrate0 orientation observableFaceId hobservableFace).filter
    (fun structural => decide
      (row = finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace structural))

theorem finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow_eq_filter
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row =
      (finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace).filter
      (fun structural => decide
        (row = finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace structural)) := by
  rfl

theorem finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow_nodup
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row).Nodup := by
  unfold finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
  exact List.filter_sublist.nodup
    (finePacketConnectedRateProfiledStructuralCodes_nodup
      S rate hrate0 orientation observableFaceId hobservableFace)

theorem finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row) :
    structural ∈ finePacketConnectedRateProfiledStructuralCodes
      S rate hrate0 orientation observableFaceId hobservableFace :=
  (List.mem_filter.mp hstructural).1

theorem finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row) :
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace structural = row :=
  (of_decide_eq_true (List.mem_filter.mp hstructural).2).symm

/-- The only intended variable coordinates in one row fiber. -/
def finePacketConnectedRateProfiledStructuralTracePair
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    List SlabAcceptedPairedPeelRecord × List SlabAcceptedPairedPeelRecord :=
  (structural.fineProfile.2.1, structural.coarseProfile.2.1)

/-! ## 2. Source/target row words reconstruct the physical entry -/

private theorem finePacketGlobalConnectedEntry_eq_of_sources_targets_eq_local
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

private theorem canonicalRepresentatives_entry_eq_of_row_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketConnectedRateProfiledStructuralCode)
    (leftReference rightReference :
      FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
        S orientation observableFaceId)
    (hleftOption :
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
        S rate hrate0 orientation observableFaceId hobservableFace left =
          some leftReference)
    (hrightOption :
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
        S rate hrate0 orientation observableFaceId hobservableFace right =
          some rightReference)
    (hleftStructural : left =
      finePacketConnectedRateProfiledStructuralCompiler
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace
            leftReference))
    (hrightStructural : right =
      finePacketConnectedRateProfiledStructuralCompiler
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace
            rightReference))
    (hrow :
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace left =
        finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace right) :
    leftReference.1 = rightReference.1 := by
  have hleftSourceCode := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.leftSource hrow
  have hrightSourceCode := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.rightSource hrow
  have hleftTargetWord := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.leftTarget hrow
  have hrightTargetWord := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.rightTarget hrow
  have hsourceFirst : leftReference.1.1.sources.1 =
      rightReference.1.1.sources.1 := by
    apply positivePhysicalSource_eq_of_finiteKey_eq S
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_leftSource,
      hleftStructural, hrightStructural,
      finePacketConnectedRateProfiledStructuralCompiler,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
      using hleftSourceCode
  have hsourceSecond : leftReference.1.1.sources.2 =
      rightReference.1.1.sources.2 := by
    apply positivePhysicalSource_eq_of_finiteKey_eq S
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_rightSource,
      hleftStructural, hrightStructural,
      finePacketConnectedRateProfiledStructuralCompiler,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
      using hrightSourceCode
  have htargetFirstWord :
      finiteEdgeLabellingWord S.coarse.faceEdges
          leftReference.1.1.targets.1 =
        finiteEdgeLabellingWord S.coarse.faceEdges
          rightReference.1.1.targets.1 := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_leftTarget,
      finePacketConnectedRateProfiledStructuralTargetWords,
      hleftOption, hrightOption] using hleftTargetWord
  have htargetSecondWord :
      finiteEdgeLabellingWord S.coarse.faceEdges
          leftReference.1.1.targets.2 =
        finiteEdgeLabellingWord S.coarse.faceEdges
          rightReference.1.1.targets.2 := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_rightTarget,
      finePacketConnectedRateProfiledStructuralTargetWords,
      hleftOption, hrightOption] using hrightTargetWord
  have htargetFirst : leftReference.1.1.targets.1 =
      rightReference.1.1.targets.1 := by
    apply edgeLabelling_eq_of_word_eq_of_supported S.coarse.faceEdges
    · exact (boundedEdgeLabellings_sound S.coarse.cutoff
        S.coarse.faceEdges leftReference.1.1.targets.1
          (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
            S orientation observableFaceId leftReference.1)).2
    · exact (boundedEdgeLabellings_sound S.coarse.cutoff
        S.coarse.faceEdges rightReference.1.1.targets.1
          (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
            S orientation observableFaceId rightReference.1)).2
    · exact htargetFirstWord
  have htargetSecond : leftReference.1.1.targets.2 =
      rightReference.1.1.targets.2 := by
    apply edgeLabelling_eq_of_word_eq_of_supported S.coarse.faceEdges
    · exact (boundedEdgeLabellings_sound S.coarse.cutoff
        S.coarse.faceEdges leftReference.1.1.targets.2
          (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
            S orientation observableFaceId leftReference.1)).2
    · exact (boundedEdgeLabellings_sound S.coarse.cutoff
        S.coarse.faceEdges rightReference.1.1.targets.2
          (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
            S orientation observableFaceId rightReference.1)).2
    · exact htargetSecondWord
  exact Subtype.ext
    (finePacketGlobalConnectedEntry_eq_of_sources_targets_eq_local
      (Prod.ext hsourceFirst hsourceSecond)
      (Prod.ext htargetFirst htargetSecond))

/-! ## 3. The trace pair is injective on a fixed row fiber -/

theorem finePacketConnectedRateProfiledStructuralTracePair_injective_on_row
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (left : FinePacketConnectedRateProfiledStructuralCode)
    (hleft : left ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row)
    (right : FinePacketConnectedRateProfiledStructuralCode)
    (hright : right ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row)
    (htrace : finePacketConnectedRateProfiledStructuralTracePair left =
      finePacketConnectedRateProfiledStructuralTracePair right) :
    left = right := by
  have hrowLeft :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row left hleft
  have hrowRight :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row right hright
  have hrow := hrowLeft.trans hrowRight.symm
  obtain ⟨leftReference, hleftOption, _hleftReferenceMem,
      hleftStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace left
        (finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row left hleft)
  obtain ⟨rightReference, hrightOption, _hrightReferenceMem,
      hrightStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace right
        (finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row right hright)
  have hentry := canonicalRepresentatives_entry_eq_of_row_eq
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace left right leftReference rightReference hleftOption
        hrightOption hleftStructural hrightStructural hrow
  have hleftSource := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.leftSource hrow
  have hrightSource := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.rightSource hrow
  have hfineTerminal := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineTerminal hrow
  have hfineExterior := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineExterior hrow
  have hfineCore := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineCore hrow
  have hcoarseTerminal := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseTerminal hrow
  have hcoarseExterior := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseExterior hrow
  have hcoarseCore := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseCore hrow
  have hfineTrace := congrArg Prod.fst htrace
  have hcoarseTrace := congrArg Prod.snd htrace
  have hcomponentSize : left.componentSize = right.componentSize := by
    have hleftComponent := congrArg
      FinePacketConnectedRateProfiledStructuralCode.componentSize
        hleftStructural
    have hrightComponent := congrArg
      FinePacketConnectedRateProfiledStructuralCode.componentSize
        hrightStructural
    have hreferenceComponent := congrArg
      (finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId) hentry
    have hleftComponent' : left.componentSize =
        finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId leftReference.1 := by
      simpa only [finePacketConnectedRateProfiledStructuralCompiler,
        finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
        using hleftComponent
    have hrightComponent' : right.componentSize =
        finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId rightReference.1 := by
      simpa only [finePacketConnectedRateProfiledStructuralCompiler,
        finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
        using hrightComponent
    exact hleftComponent'.trans
      (hreferenceComponent.trans hrightComponent'.symm)
  have hshapeChild : left.shapeChild = right.shapeChild := by
    have hleftShape := congrArg
      FinePacketConnectedRateProfiledStructuralCode.shapeChild hleftStructural
    have hrightShape := congrArg
      FinePacketConnectedRateProfiledStructuralCode.shapeChild hrightStructural
    have hreferenceShape := congrArg
      (finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace) hentry
    have hleftShape' : left.shapeChild =
        finePacketGlobalNonzeroConnectedEntryShapeChildCode
          S orientation observableFaceId hobservableFace leftReference.1 := by
      simpa only [finePacketConnectedRateProfiledStructuralCompiler,
        finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
        using hleftShape
    have hrightShape' : right.shapeChild =
        finePacketGlobalNonzeroConnectedEntryShapeChildCode
          S orientation observableFaceId hobservableFace rightReference.1 := by
      simpa only [finePacketConnectedRateProfiledStructuralCompiler,
        finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
        using hrightShape
    exact hleftShape'.trans (hreferenceShape.trans hrightShape'.symm)
  have hleftSource' : left.leftSource = right.leftSource := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_leftSource]
      using hleftSource
  have hrightSource' : left.rightSource = right.rightSource := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_rightSource]
      using hrightSource
  have hfineProfile : left.fineProfile = right.fineProfile := by
    apply Prod.ext
    · simpa only [
        finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineTerminal]
        using hfineTerminal
    · apply Prod.ext
      · exact hfineTrace
      · exact Prod.ext
          (by simpa only
            [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineExterior]
            using hfineExterior)
          (by simpa only
            [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineCore]
            using hfineCore)
  have hcoarseProfile : left.coarseProfile = right.coarseProfile := by
    apply Prod.ext
    · simpa only [
        finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseTerminal]
        using hcoarseTerminal
    · apply Prod.ext
      · exact hcoarseTrace
      · exact Prod.ext
          (by simpa only
            [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseExterior]
            using hcoarseExterior)
          (by simpa only
            [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseCore]
            using hcoarseCore)
  cases left
  cases right
  dsimp only at hleftSource' hrightSource' hcomponentSize hshapeChild hfineProfile hcoarseProfile
  cases hleftSource'
  cases hrightSource'
  cases hcomponentSize
  cases hshapeChild
  cases hfineProfile
  cases hcoarseProfile
  rfl

/-! ## 4. Both traces lie in their exact dependent carriers -/

theorem finePacketConnectedRateProfiledStructural_fineTrace_valid
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    ∀ record, record ∈ structural.fineProfile.2.1 →
      record.Valid
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0).extent := by
  obtain ⟨reference, _hreferenceOption, _hreferenceMem,
      hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  have hprofile := congrArg
    FinePacketConnectedRateProfiledStructuralCode.fineProfile
      hreferenceStructural
  change structural.fineProfile =
    slabAcceptedPairedHighSpinProfileExactKey
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace
          reference).1 at hprofile
  have htrace := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.1) hprofile
  change structural.fineProfile.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).1.2.1
    at htrace
  intro record hrecord
  rw [htrace] at hrecord
  exact slabAcceptedPairCanonicalHighSpinProfile_trace_valid
    (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
    (anchorPaidExteriorThreshold rate)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId reference.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace reference.1)
    (slabAcceptedTwoReplicaStateAtCoupling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      rate hrate0 reference.2.1.1) record hrecord

theorem finePacketConnectedRateProfiledStructural_coarseTrace_valid
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    ∀ record, record ∈ structural.coarseProfile.2.1 →
      record.Valid
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0).extent := by
  obtain ⟨reference, _hreferenceOption, _hreferenceMem,
      hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  have hprofile := congrArg
    FinePacketConnectedRateProfiledStructuralCode.coarseProfile
      hreferenceStructural
  change structural.coarseProfile =
    slabAcceptedPairedHighSpinProfileExactKey
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace
          reference).2 at hprofile
  have htrace := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.1) hprofile
  change structural.coarseProfile.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).2.2.1
    at htrace
  intro record hrecord
  rw [htrace] at hrecord
  exact slabAcceptedPairCanonicalHighSpinProfile_trace_valid
    (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
    (anchorPaidExteriorThreshold rate)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId reference.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace reference.1)
    (slabAcceptedTwoReplicaStateAtCoupling
      (coarseUnitCouplingSlabPhysicalData S)
      rate hrate0
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S reference.2.1)) record hrecord

theorem finePacketConnectedRateProfiledStructural_fineSkeleton_eq_row
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row) :
    structural.fineProfile.2.1.map SlabAcceptedPairedPeelRecord.skeleton =
      row.fineSkeletons := by
  have hrow :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row structural hstructural
  exact congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineSkeletons hrow

theorem finePacketConnectedRateProfiledStructural_coarseSkeleton_eq_row
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row) :
    structural.coarseProfile.2.1.map SlabAcceptedPairedPeelRecord.skeleton =
      row.coarseSkeletons := by
  have hrow :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row structural hstructural
  exact congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseSkeletons hrow

private theorem cartesian_length_local {A B : Type}
    (left : List A) (right : List B) :
    (cartesian left right).length = left.length * right.length := by
  induction left with
  | nil =>
      unfold cartesian
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head tail ih =>
      rw [cartesian]
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons]
      change right.length + (cartesian tail right).length =
        (tail.length + 1) * right.length
      rw [ih, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- Product of the exact fine and coarse dependent trace carriers attached to
a terminal-skeleton row. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    List (List SlabAcceptedPairedPeelRecord ×
      List SlabAcceptedPairedPeelRecord) :=
  cartesian
    (slabAcceptedPairedPeelTraceCarrier
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0).extent
      row.fineSkeletons)
    (slabAcceptedPairedPeelTraceCarrier
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0).extent
      row.coarseSkeletons)

theorem finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier_length
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
      S rate hrate0 row).length =
      (slabAcceptedPairedPeelTraceCarrier
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0).extent
        row.fineSkeletons).length *
      (slabAcceptedPairedPeelTraceCarrier
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0).extent
        row.coarseSkeletons).length := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
  exact cartesian_length_local _ _

theorem finePacketConnectedRateProfiledStructuralTracePair_mem_rowCarrier
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row) :
    finePacketConnectedRateProfiledStructuralTracePair structural ∈
      finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
        S rate hrate0 row := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · have hmem := slabAcceptedPairedPeelTrace_mem_carrier
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0).extent
      structural.fineProfile.2.1
      (finePacketConnectedRateProfiledStructural_fineTrace_valid
        S rate hrate0 orientation observableFaceId hobservableFace structural
          (finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row structural hstructural))
    rw [finePacketConnectedRateProfiledStructural_fineSkeleton_eq_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural] at hmem
    exact hmem
  · have hmem := slabAcceptedPairedPeelTrace_mem_carrier
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0).extent
      structural.coarseProfile.2.1
      (finePacketConnectedRateProfiledStructural_coarseTrace_valid
        S rate hrate0 orientation observableFaceId hobservableFace structural
          (finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row structural hstructural))
    rw [finePacketConnectedRateProfiledStructural_coarseSkeleton_eq_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural] at hmem
    exact hmem

/-! ## 5. Count the row fiber -/

private theorem nodup_map_of_injOn_local {A B : Type} (f : A → B) :
    ∀ (items : List A), items.Nodup →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        f left = f right → left = right) →
      (items.map f).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
        have hheadEq := hinjective head List.mem_cons_self other
          (List.mem_cons_of_mem head hother) heq.symm
        exact hparts.1 (hheadEq ▸ hother)
      · exact nodup_map_of_injOn_local f tail hparts.2
          (fun left hleft right hright =>
            hinjective left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright))

def finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :=
  (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row).map
    finePacketConnectedRateProfiledStructuralTracePair

theorem finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow_nodup
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row).Nodup := by
  unfold
    finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
  apply nodup_map_of_injOn_local
  · exact
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow_nodup
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row
  · exact
      finePacketConnectedRateProfiledStructuralTracePair_injective_on_row
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row

theorem finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow_subset
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    ∀ pair, pair ∈
      finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row →
      pair ∈
        finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
          S rate hrate0 row := by
  intro pair hpair
  unfold
    finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
    at hpair
  obtain ⟨structural, hstructural, rfl⟩ := List.mem_map.mp hpair
  exact finePacketConnectedRateProfiledStructuralTracePair_mem_rowCarrier
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row structural hstructural

/-- The full two-scale adaptive ambiguity at one row costs one entropy-base
power at the sum of the fine and coarse skeleton masses. -/
theorem finePacketConnectedRateProfiledStructuralRowFiber_length_le
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row).length ≤
      componentAdaptiveEntropyBase ^
        (slabAcceptedPairedPeelSkeletonMass row.fineSkeletons +
          slabAcceptedPairedPeelSkeletonMass row.coarseSkeletons) := by
  have hsubset :=
    YMGap.Continuum.FiniteBoolGraphSimplePaths.FiniteListBound.nodup_subset_length_le
    (finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row)
    (finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
      S rate hrate0 row)
    (finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow_nodup
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row)
    (finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow_subset
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row)
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier_length]
    at hsubset
  have hfine := slabAcceptedPairedPeelTraceCarrier_length_le
    (finePacketFineRateCouplingSlabPhysicalData S rate hrate0).extent
      row.fineSkeletons
  have hcoarse := slabAcceptedPairedPeelTraceCarrier_length_le
    (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0).extent
      row.coarseSkeletons
  have hmapLength :
      (finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace row).length =
        (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row).length := by
    unfold
      finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
    exact List.length_map _
  rw [hmapLength] at hsubset
  exact Nat.le_trans hsubset
    (Nat.le_trans (Nat.mul_le_mul hfine hcoarse) (by
      rw [Nat.pow_add]
      exact Nat.le_refl _))

/-! ## 6. For realized rows, skeleton mass is the named profile mass -/

theorem finePacketConnectedRateProfiledStructural_fineSkeletonMass_eq
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    slabAcceptedPairedPeelSkeletonMass
        (structural.fineProfile.2.1.map
          SlabAcceptedPairedPeelRecord.skeleton) =
      structural.fineProfile.2.2.1 + structural.fineProfile.2.2.2 := by
  obtain ⟨reference, _hreferenceOption, _hreferenceMem,
      hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  have hprofile := congrArg
    FinePacketConnectedRateProfiledStructuralCode.fineProfile
      hreferenceStructural
  change structural.fineProfile =
    slabAcceptedPairedHighSpinProfileExactKey
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace
          reference).1 at hprofile
  have htrace := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.1) hprofile
  have hexterior := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.2.1) hprofile
  have hcore := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.2.2) hprofile
  change structural.fineProfile.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).1.2.1
    at htrace
  change structural.fineProfile.2.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).1.2.2.1
    at hexterior
  change structural.fineProfile.2.2.2 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).1.2.2.2
    at hcore
  rw [slabAcceptedPairedPeelTrace_skeletonMass, htrace, hexterior, hcore]
  exact slabAcceptedPairCanonicalHighSpinProfile_traceMass
    (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
    (anchorPaidExteriorThreshold rate)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId reference.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace reference.1)
    (slabAcceptedTwoReplicaStateAtCoupling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      rate hrate0 reference.2.1.1)

theorem finePacketConnectedRateProfiledStructural_coarseSkeletonMass_eq
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    slabAcceptedPairedPeelSkeletonMass
        (structural.coarseProfile.2.1.map
          SlabAcceptedPairedPeelRecord.skeleton) =
      structural.coarseProfile.2.2.1 + structural.coarseProfile.2.2.2 := by
  obtain ⟨reference, _hreferenceOption, _hreferenceMem,
      hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  have hprofile := congrArg
    FinePacketConnectedRateProfiledStructuralCode.coarseProfile
      hreferenceStructural
  change structural.coarseProfile =
    slabAcceptedPairedHighSpinProfileExactKey
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace
          reference).2 at hprofile
  have htrace := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.1) hprofile
  have hexterior := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.2.1) hprofile
  have hcore := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.2.2) hprofile
  change structural.coarseProfile.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).2.2.1
    at htrace
  change structural.coarseProfile.2.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).2.2.2.1
    at hexterior
  change structural.coarseProfile.2.2.2 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).2.2.2.2
    at hcore
  rw [slabAcceptedPairedPeelTrace_skeletonMass, htrace, hexterior, hcore]
  exact slabAcceptedPairCanonicalHighSpinProfile_traceMass
    (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
    (anchorPaidExteriorThreshold rate)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId reference.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace reference.1)
    (slabAcceptedTwoReplicaStateAtCoupling
      (coarseUnitCouplingSlabPhysicalData S)
      rate hrate0
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S reference.2.1))

theorem finePacketConnectedRateProfiledTerminalSkeletonRow_skeletonMass_eq_of_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace) :
    slabAcceptedPairedPeelSkeletonMass row.fineSkeletons +
        slabAcceptedPairedPeelSkeletonMass row.coarseSkeletons =
      (row.fineExterior + row.fineCore) +
        (row.coarseExterior + row.coarseCore) := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowCodes at hrow
  have hmapped := List.mem_eraseDups.mp hrow
  obtain ⟨structural, hstructural, hcompiler⟩ := List.mem_map.mp hmapped
  have hfine := finePacketConnectedRateProfiledStructural_fineSkeletonMass_eq
    S rate hrate0 orientation observableFaceId hobservableFace structural
      hstructural
  have hcoarse :=
    finePacketConnectedRateProfiledStructural_coarseSkeletonMass_eq
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  have hsum :
      slabAcceptedPairedPeelSkeletonMass
          (structural.fineProfile.2.1.map
            SlabAcceptedPairedPeelRecord.skeleton) +
        slabAcceptedPairedPeelSkeletonMass
          (structural.coarseProfile.2.1.map
            SlabAcceptedPairedPeelRecord.skeleton) =
      (structural.fineProfile.2.2.1 + structural.fineProfile.2.2.2) +
        (structural.coarseProfile.2.2.1 +
          structural.coarseProfile.2.2.2) := by
    rw [hfine, hcoarse]
  rw [← hcompiler]
  simpa only [
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineSkeletons,
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseSkeletons,
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineExterior,
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineCore,
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseExterior,
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseCore]
    using hsum

theorem finePacketConnectedRateProfiledStructuralRowFiber_length_le_profileMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace) :
    (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row).length ≤
      componentAdaptiveEntropyBase ^
        ((row.fineExterior + row.fineCore) +
          (row.coarseExterior + row.coarseCore)) := by
  have hbound := finePacketConnectedRateProfiledStructuralRowFiber_length_le
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row
  rw [finePacketConnectedRateProfiledTerminalSkeletonRow_skeletonMass_eq_of_mem
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row hrow] at hbound
  exact hbound

#print axioms finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
#print axioms finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow_eq_filter
#print axioms finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow_nodup
#print axioms finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
#print axioms finePacketConnectedRateProfiledStructuralTracePair
#print axioms finePacketConnectedRateProfiledStructuralTracePair_injective_on_row
#print axioms finePacketConnectedRateProfiledStructural_fineTrace_valid
#print axioms finePacketConnectedRateProfiledStructural_coarseTrace_valid
#print axioms finePacketConnectedRateProfiledStructural_fineSkeleton_eq_row
#print axioms finePacketConnectedRateProfiledStructural_coarseSkeleton_eq_row
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowTracePairCarrier_length
#print axioms finePacketConnectedRateProfiledStructuralTracePair_mem_rowCarrier
#print axioms finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow
#print axioms finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow_nodup
#print axioms finePacketConnectedRateProfiledStructuralTracePairsAtTerminalSkeletonRow_subset
#print axioms finePacketConnectedRateProfiledStructuralRowFiber_length_le
#print axioms finePacketConnectedRateProfiledStructural_fineSkeletonMass_eq
#print axioms finePacketConnectedRateProfiledStructural_coarseSkeletonMass_eq
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRow_skeletonMass_eq_of_mem
#print axioms finePacketConnectedRateProfiledStructuralRowFiber_length_le_profileMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
