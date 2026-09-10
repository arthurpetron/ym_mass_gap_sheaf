/-
# Rigidity of the retained terminal-history normalization coordinates

Rows in one terminal-history normalization fiber have the same physical
fine-source words, coarse-target words, and accepted terminal states.  This
module proves that those finite words reconstruct the same connected physical
entry for the canonical literal representatives of any two rows in the
fiber.  Thus the remaining binary-history adequacy problem does not contain
an unaccounted physical component or endpoint choice: it is internal to the
two canonical peeling histories and their profile split.

Constructive contract: finite-key reconstruction and explicit selected
representatives only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new trusted
principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonBinaryHistoryCandidate

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationRigidity

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonHistoryMassFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

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

/-! ## 1. Shallow projections of the normalization compiler -/

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_leftSource
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row).key.leftSource = row.leftSource := by
  rfl

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_rightSource
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row).key.rightSource = row.rightSource := by
  rfl

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_leftTarget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row).key.leftTarget = row.leftTarget := by
  rfl

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_rightTarget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row).key.rightTarget = row.rightTarget := by
  rfl

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_fineTerminal
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row).key.fineTerminal = row.fineTerminal := by
  rfl

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_coarseTerminal
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row).key.coarseTerminal = row.coarseTerminal := by
  rfl

/-! ## 2. Source and target coordinates reconstruct the physical entry -/

theorem finePacketConnectedRateProfiledTerminalSkeletonCanonicalReferences_entry_eq_of_normalization_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (leftRow rightRow : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (leftStructural rightStructural :
      FinePacketConnectedRateProfiledStructuralCode)
    (hleftStructural : leftStructural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace leftRow)
    (hrightStructural : rightStructural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace rightRow)
    (leftReference rightReference :
      FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
        S orientation observableFaceId)
    (hleftOption :
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
        S rate hrate0 orientation observableFaceId hobservableFace
          leftStructural = some leftReference)
    (hrightOption :
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
        S rate hrate0 orientation observableFaceId hobservableFace
          rightStructural = some rightReference)
    (hleftReferenceStructural : leftStructural =
      finePacketConnectedRateProfiledStructuralCompiler
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace
            leftReference))
    (hrightReferenceStructural : rightStructural =
      finePacketConnectedRateProfiledStructuralCompiler
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace
            rightReference))
    (hnormalization :
      finePacketConnectedRateTerminalSkeletonNormalizationCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace leftRow =
        finePacketConnectedRateTerminalSkeletonNormalizationCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace rightRow) :
    leftReference.1 = rightReference.1 := by
  have hleftCompiled :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace leftRow leftStructural hleftStructural
  have hrightCompiled :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace rightRow rightStructural hrightStructural
  have hleftSourceRow := congrArg
    (fun code : FinePacketConnectedRateTerminalSkeletonNormalizationCode =>
      code.key.leftSource) hnormalization
  have hrightSourceRow := congrArg
    (fun code : FinePacketConnectedRateTerminalSkeletonNormalizationCode =>
      code.key.rightSource) hnormalization
  have hleftTargetRow := congrArg
    (fun code : FinePacketConnectedRateTerminalSkeletonNormalizationCode =>
      code.key.leftTarget) hnormalization
  have hrightTargetRow := congrArg
    (fun code : FinePacketConnectedRateTerminalSkeletonNormalizationCode =>
      code.key.rightTarget) hnormalization
  change
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace leftRow).key.leftSource =
      (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace rightRow).key.leftSource at hleftSourceRow
  change
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace leftRow).key.rightSource =
      (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace rightRow).key.rightSource at hrightSourceRow
  change
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace leftRow).key.leftTarget =
      (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace rightRow).key.leftTarget at hleftTargetRow
  change
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace leftRow).key.rightTarget =
      (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace rightRow).key.rightTarget at hrightTargetRow
  rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_leftSource,
    finePacketConnectedRateTerminalSkeletonNormalizationCompiler_leftSource]
    at hleftSourceRow
  rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_rightSource,
    finePacketConnectedRateTerminalSkeletonNormalizationCompiler_rightSource]
    at hrightSourceRow
  rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_leftTarget,
    finePacketConnectedRateTerminalSkeletonNormalizationCompiler_leftTarget]
    at hleftTargetRow
  rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_rightTarget,
    finePacketConnectedRateTerminalSkeletonNormalizationCompiler_rightTarget]
    at hrightTargetRow
  have hleftStructuralSource := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.leftSource
      hleftCompiled
  have hrightStructuralSource := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.leftSource
      hrightCompiled
  have hleftStructuralRightSource := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.rightSource
      hleftCompiled
  have hrightStructuralRightSource := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.rightSource
      hrightCompiled
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_leftSource]
    at hleftStructuralSource hrightStructuralSource
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_rightSource]
    at hleftStructuralRightSource hrightStructuralRightSource
  have hsourceFirstStructural :
      leftStructural.leftSource = rightStructural.leftSource :=
    hleftStructuralSource.trans
      (hleftSourceRow.trans hrightStructuralSource.symm)
  have hsourceSecondStructural :
      leftStructural.rightSource = rightStructural.rightSource :=
    hleftStructuralRightSource.trans
      (hrightSourceRow.trans hrightStructuralRightSource.symm)
  have hsourceFirst : leftReference.1.1.sources.1 =
      rightReference.1.1.sources.1 := by
    apply positivePhysicalSource_eq_of_finiteKey_eq S
    simpa only [hleftReferenceStructural, hrightReferenceStructural,
      finePacketConnectedRateProfiledStructuralCompiler,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
      using hsourceFirstStructural
  have hsourceSecond : leftReference.1.1.sources.2 =
      rightReference.1.1.sources.2 := by
    apply positivePhysicalSource_eq_of_finiteKey_eq S
    simpa only [hleftReferenceStructural, hrightReferenceStructural,
      finePacketConnectedRateProfiledStructuralCompiler,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
      using hsourceSecondStructural
  have hleftStructuralTarget := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.leftTarget
      hleftCompiled
  have hrightStructuralTarget := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.leftTarget
      hrightCompiled
  have hleftStructuralRightTarget := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.rightTarget
      hleftCompiled
  have hrightStructuralRightTarget := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.rightTarget
      hrightCompiled
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_leftTarget]
    at hleftStructuralTarget hrightStructuralTarget
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_rightTarget]
    at hleftStructuralRightTarget hrightStructuralRightTarget
  have htargetFirstStructural :
      (finePacketConnectedRateProfiledStructuralTargetWords
        S rate hrate0 orientation observableFaceId hobservableFace
          leftStructural).1 =
      (finePacketConnectedRateProfiledStructuralTargetWords
        S rate hrate0 orientation observableFaceId hobservableFace
          rightStructural).1 :=
    hleftStructuralTarget.trans
      (hleftTargetRow.trans hrightStructuralTarget.symm)
  have htargetSecondStructural :
      (finePacketConnectedRateProfiledStructuralTargetWords
        S rate hrate0 orientation observableFaceId hobservableFace
          leftStructural).2 =
      (finePacketConnectedRateProfiledStructuralTargetWords
        S rate hrate0 orientation observableFaceId hobservableFace
          rightStructural).2 :=
    hleftStructuralRightTarget.trans
      (hrightTargetRow.trans hrightStructuralRightTarget.symm)
  have htargetFirstWord :
      finiteEdgeLabellingWord S.coarse.faceEdges
          leftReference.1.1.targets.1 =
        finiteEdgeLabellingWord S.coarse.faceEdges
          rightReference.1.1.targets.1 := by
    simpa only [finePacketConnectedRateProfiledStructuralTargetWords,
      hleftOption, hrightOption] using htargetFirstStructural
  have htargetSecondWord :
      finiteEdgeLabellingWord S.coarse.faceEdges
          leftReference.1.1.targets.2 =
        finiteEdgeLabellingWord S.coarse.faceEdges
          rightReference.1.1.targets.2 := by
    simpa only [finePacketConnectedRateProfiledStructuralTargetWords,
      hleftOption, hrightOption] using htargetSecondStructural
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

/-! ## 3. Every normalization-fiber pair has equal physical entries -/

theorem finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode_canonicalEntries_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (leftRow rightRow : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hleftRow : leftRow ∈
      finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code)
    (hrightRow : rightRow ∈
      finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code) :
    ∃ leftStructural rightStructural leftReference rightReference,
      leftStructural ∈
          finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace leftRow ∧
      rightStructural ∈
          finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace rightRow ∧
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
          S rate hrate0 orientation observableFaceId hobservableFace
            leftStructural = some leftReference ∧
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
          S rate hrate0 orientation observableFaceId hobservableFace
            rightStructural = some rightReference ∧
      leftReference.1 = rightReference.1 := by
  have hleftGlobal := (List.mem_filter.mp hleftRow).1
  have hrightGlobal := (List.mem_filter.mp hrightRow).1
  obtain ⟨leftStructural, _hleftFirst, hleftStructural⟩ :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace leftRow hleftGlobal
  obtain ⟨rightStructural, _hrightFirst, hrightStructural⟩ :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace rightRow hrightGlobal
  have hleftCarrier :=
    finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace leftRow leftStructural hleftStructural
  have hrightCarrier :=
    finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace rightRow rightStructural hrightStructural
  obtain ⟨leftReference, hleftOption, _hleftReferenceMem,
      hleftReferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace
        leftStructural hleftCarrier
  obtain ⟨rightReference, hrightOption, _hrightReferenceMem,
      hrightReferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace
        rightStructural hrightCarrier
  have hleftCode := of_decide_eq_true (List.mem_filter.mp hleftRow).2
  have hrightCode := of_decide_eq_true (List.mem_filter.mp hrightRow).2
  have hnormalization :
      finePacketConnectedRateTerminalSkeletonNormalizationCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace leftRow =
        finePacketConnectedRateTerminalSkeletonNormalizationCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace rightRow :=
    hleftCode.symm.trans hrightCode
  refine ⟨leftStructural, rightStructural, leftReference, rightReference,
    hleftStructural, hrightStructural, hleftOption, hrightOption, ?_⟩
  exact
    finePacketConnectedRateProfiledTerminalSkeletonCanonicalReferences_entry_eq_of_normalization_eq
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace leftRow rightRow leftStructural rightStructural
          hleftStructural hrightStructural leftReference rightReference
            hleftOption hrightOption hleftReferenceStructural
              hrightReferenceStructural hnormalization

#print axioms finePacketConnectedRateProfiledTerminalSkeletonCanonicalReferences_entry_eq_of_normalization_eq
#print axioms finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode_canonicalEntries_eq

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationRigidity
