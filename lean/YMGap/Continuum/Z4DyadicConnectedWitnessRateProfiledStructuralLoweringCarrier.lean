/-
# The exact lowering carrier inside a structural terminal fiber

The structural terminal code deliberately forgets the four lowering words.
To contract that ambiguity by tilted-Gibbs normalization, rather than by a
volume-dependent cardinality estimate, it must first be identified with the
literal product of the two localized lowering carriers already present in the
joint witness.

This module proves the required rigidity statement.  Equality of structural
codes reconstructs the physical source pair, the connected four-entry row,
and both accepted fine/coarse states.  Consequently every lowering code in
the corresponding structural fiber lies in one explicit oriented product of
localized lowering carriers over those fixed physical rows.

Constructive contract: exact finite keys, dependent carrier membership, and
proof irrelevance only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new trusted
principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralLoweringCarrier

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness

/-! ## 1. A structural code fixes the underlying physical row -/

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

/-- Equality of structural terminal codes fixes the connected four-entry
row.  No equality of lowering words is used. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitness_entry_eq_of_structural_eq
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hstructural :
      finePacketConnectedRateProfiledStructuralCompiler
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace left) =
        finePacketConnectedRateProfiledStructuralCompiler
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace right)) :
    left.1 = right.1 := by
  have hleftSourceKey := congrArg
    FinePacketConnectedRateProfiledStructuralCode.leftSource hstructural
  have hrightSourceKey := congrArg
    FinePacketConnectedRateProfiledStructuralCode.rightSource hstructural
  have hsourceFirst : left.1.1.sources.1 = right.1.1.sources.1 :=
    positivePhysicalSource_eq_of_finiteKey_eq
      S left.1.1.sources.1 right.1.1.sources.1 (by
        simpa only [finePacketConnectedRateProfiledStructuralCompiler,
          finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
          using hleftSourceKey)
  have hsourceSecond : left.1.1.sources.2 = right.1.1.sources.2 :=
    positivePhysicalSource_eq_of_finiteKey_eq
      S left.1.1.sources.2 right.1.1.sources.2 (by
        simpa only [finePacketConnectedRateProfiledStructuralCompiler,
          finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
          using hrightSourceKey)
  have hshape := congrArg
    FinePacketConnectedRateProfiledStructuralCode.shapeChild hstructural
  have hshape' :
      finePacketGlobalNonzeroConnectedEntryShapeChildCode
          S orientation observableFaceId hobservableFace left.1 =
        finePacketGlobalNonzeroConnectedEntryShapeChildCode
          S orientation observableFaceId hobservableFace right.1 := by
    simpa only [finePacketConnectedRateProfiledStructuralCompiler,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
      using hshape
  have hfineProfileKey := congrArg
    FinePacketConnectedRateProfiledStructuralCode.fineProfile hstructural
  have hcoarseProfileKey := congrArg
    FinePacketConnectedRateProfiledStructuralCode.coarseProfile hstructural
  have hprofile :
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right := by
    apply Prod.ext
    · apply slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      simpa only [finePacketConnectedRateProfiledStructuralCompiler,
        finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
        using hfineProfileKey
    · apply slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      simpa only [finePacketConnectedRateProfiledStructuralCompiler,
        finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler]
        using hcoarseProfileKey
  have hforgetLeft :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling_terminal_trace
      S rate hrate0 orientation observableFaceId hobservableFace left
  have hforgetRight :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling_terminal_trace
      S rate hrate0 orientation observableFaceId hobservableFace right
  have hfineProfile := congrArg
    (fun output : FinePacketConnectedFourEntryRateProfiledPeelingOutput
        S rate hrate0 => (output.1.1, output.1.2.1)) hprofile
  have hcoarseProfile := congrArg
    (fun output : FinePacketConnectedFourEntryRateProfiledPeelingOutput
        S rate hrate0 => (output.2.1, output.2.2.1)) hprofile
  have hcanonical :
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right :=
    Prod.ext
      (hforgetLeft.1.symm.trans (hfineProfile.trans hforgetRight.1))
      (hforgetLeft.2.symm.trans (hcoarseProfile.trans hforgetRight.2))
  have hcoarse := coarseUnitAcceptedState_eq_of_shape_ratePeeling_eq
    S rate hrate0 orientation observableFaceId hobservableFace
      left right hshape' hcanonical
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
        congrArg (fun state => state.1.1.1) hcoarse
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
        congrArg (fun state => state.2.1.1) hcoarse
      _ = right.1.1.targets.2 :=
        finePacketOrientedJointUnitExpandedWitness_coarseSecond_physical_eq
          S orientation right.1.1.sources.1 right.1.1.sources.2
            right.1.1.targets
            (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
              S orientation observableFaceId right.1)
            (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
              S orientation observableFaceId right.1)
            right.2.1 right.2.2
  have hsources : left.1.1.sources = right.1.1.sources :=
    Prod.ext hsourceFirst hsourceSecond
  have htargets : left.1.1.targets = right.1.1.targets :=
    Prod.ext htargetFirst htargetSecond
  exact Subtype.ext
    (finePacketGlobalConnectedEntry_eq_of_sources_targets_eq_local
      hsources htargets)

/-! ## 2. The oriented product of the two lowering rows -/

/-- The exact four-word carrier obtained by retaining the two localized
lowering pairs and forgetting only the accepted coarse entries. -/
def finePacketOrientedLoweringCodeCarrier
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (targets : EdgeLabelling × EdgeLabelling) :
    List FinePacketConnectedRateProfiledLoweringCode :=
  match orientation with
  | .forward =>
      cartesian
        (finePacketLocalizedLoweringWitnessPairCarrier
          S first first second targets.1)
        (finePacketLocalizedLoweringWitnessPairCarrier
          S second first second targets.2)
  | .reverse =>
      cartesian
        (finePacketLocalizedLoweringWitnessPairCarrier
          S second first second targets.1)
        (finePacketLocalizedLoweringWitnessPairCarrier
          S first first second targets.2)

/-- The lowering coordinates of every attached expanded witness lie in the
oriented lowering carrier determined by its physical source and target row. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitness_lowering_mem_orientedCarrier
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    (expanded.2.1.2.1.1, expanded.2.1.2.2.1) ∈
      finePacketOrientedLoweringCodeCarrier
        S orientation expanded.1.1.sources.1.1 expanded.1.1.sources.2.1
          expanded.1.1.targets := by
  have hjoint := (mem_cartesian_iff _ _ expanded.2.1).mp expanded.2.2
  cases orientation with
  | forward =>
      have htargets := (mem_cartesian_iff _ _ expanded.2.1.2).mp hjoint.2
      apply (mem_cartesian_iff _ _ _).mpr
      constructor
      · exact (mem_cartesian_iff _ _ expanded.2.1.2.1).mp htargets.1 |>.1
      · exact (mem_cartesian_iff _ _ expanded.2.1.2.2).mp htargets.2 |>.1
  | reverse =>
      have htargets := (mem_cartesian_iff _ _ expanded.2.1.2).mp hjoint.2
      apply (mem_cartesian_iff _ _ _).mpr
      constructor
      · exact (mem_cartesian_iff _ _ expanded.2.1.2.1).mp htargets.1 |>.1
      · exact (mem_cartesian_iff _ _ expanded.2.1.2.2).mp htargets.2 |>.1

theorem finePacketOrientedLoweringCodeCarrier_nodup
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (targets : EdgeLabelling × EdgeLabelling) :
    (finePacketOrientedLoweringCodeCarrier
      S orientation first second targets).Nodup := by
  cases orientation with
  | forward =>
      exact cartesian_nodup _ _
        (finePacketLocalizedLoweringWitnessPairCarrier_nodup
          S first first second targets.1)
        (finePacketLocalizedLoweringWitnessPairCarrier_nodup
          S second first second targets.2)
  | reverse =>
      exact cartesian_nodup _ _
        (finePacketLocalizedLoweringWitnessPairCarrier_nodup
          S second first second targets.1)
        (finePacketLocalizedLoweringWitnessPairCarrier_nodup
          S first first second targets.2)

private theorem cartesian_length_local
    {A B : Type} (left : List A) (right : List B) :
    (cartesian left right).length = left.length * right.length := by
  induction left with
  | nil => simp [cartesian]
  | cons head tail ih =>
      unfold cartesian at ih ⊢
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- The exact number of realized four-word slots in the oriented lowering
carrier.  Its exterior factors are intentionally displayed rather than
bounded by the component profile mass. -/
theorem finePacketOrientedLoweringCodeCarrier_length
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (targets : EdgeLabelling × EdgeLabelling) :
    (finePacketOrientedLoweringCodeCarrier
        S orientation first second targets).length =
      match orientation with
      | .forward =>
          (finePacketCommonExteriorMultiplicityProduct
              S first second targets.1 *
            finePacketDisagreementMultiplicityProduct
              S first first second targets.1) *
          (finePacketCommonExteriorMultiplicityProduct
              S first second targets.2 *
            finePacketDisagreementMultiplicityProduct
              S second first second targets.2)
      | .reverse =>
          (finePacketCommonExteriorMultiplicityProduct
              S first second targets.1 *
            finePacketDisagreementMultiplicityProduct
              S second first second targets.1) *
          (finePacketCommonExteriorMultiplicityProduct
              S first second targets.2 *
            finePacketDisagreementMultiplicityProduct
              S first first second targets.2) := by
  cases orientation with
  | forward =>
      simp only [finePacketOrientedLoweringCodeCarrier]
      rw [cartesian_length_local,
        finePacketLocalizedLoweringWitnessPairCarrier_length,
        finePacketLocalizedLoweringWitnessPairCarrier_length]
  | reverse =>
      simp only [finePacketOrientedLoweringCodeCarrier]
      rw [cartesian_length_local,
        finePacketLocalizedLoweringWitnessPairCarrier_length,
        finePacketLocalizedLoweringWitnessPairCarrier_length]

/-! ## 3. Every realized structural-fiber code lies in that carrier -/

/-- The structural code realized by one expanded witness, named opaquely so
subsequent dependent fiber statements do not repeatedly normalize its full
compiler expression. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedRateProfiledStructuralCode :=
  finePacketConnectedRateProfiledStructuralCompiler
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
      S rate hrate0 orientation observableFaceId hobservableFace expanded)

/-- The lowering carrier determined by the physical row of one expanded
connected witness. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    List FinePacketConnectedRateProfiledLoweringCode :=
  finePacketOrientedLoweringCodeCarrier
    S orientation expanded.1.1.sources.1.1 expanded.1.1.sources.2.1
      expanded.1.1.targets

/-- A realized terminal code with the same structural projection as an
expanded witness can vary only through a member of that witness's exact
oriented lowering carrier.  The two premises are the unfolded content of
membership in its structural fiber, kept separate to make the dependent
interface tractable for later finite-sum lemmas. -/
theorem finePacketConnectedRateProfiledLoweringCode_mem_orientedCarrier_of_terminal_mem_of_structural_eq
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (code : FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
      S rate hrate0)
    (hcode : code ∈
      finePacketConnectedRateProfiledNormalizedTerminalCodes
        S rate hrate0 orientation observableFaceId hobservableFace)
    (hstructuralCode :
      finePacketConnectedRateProfiledStructuralCompiler code =
        finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
          S rate hrate0 orientation observableFaceId hobservableFace
            reference) :
    finePacketConnectedRateProfiledLoweringCompiler code ∈
      finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
        S orientation observableFaceId reference := by
  unfold finePacketConnectedRateProfiledNormalizedTerminalCodes at hcode
  obtain ⟨expanded, hexpanded, hcompiled⟩ :=
    List.mem_map.mp hcode
  have hstructural :
      finePacketConnectedRateProfiledStructuralCompiler
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace expanded) =
        finePacketConnectedRateProfiledStructuralCompiler
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace reference) := by
    unfold finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode at hstructuralCode
    exact (congrArg finePacketConnectedRateProfiledStructuralCompiler
      hcompiled).trans hstructuralCode
  have hentry :=
    finePacketGlobalNonzeroConnectedExpandedWitness_entry_eq_of_structural_eq
      S rate hrate0 orientation observableFaceId hobservableFace
        expanded reference hstructural
  have hlowering :
      finePacketConnectedRateProfiledLoweringCompiler code =
        (expanded.2.1.2.1.1, expanded.2.1.2.2.1) := by
    exact (congrArg finePacketConnectedRateProfiledLoweringCompiler
      hcompiled).symm
  rw [hlowering]
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
  have hmem :=
    finePacketGlobalNonzeroConnectedExpandedWitness_lowering_mem_orientedCarrier
      S orientation observableFaceId expanded
  have hsourceFirst := congrArg
    (fun entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId => entry.1.sources.1.1) hentry
  have hsourceSecond := congrArg
    (fun entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId => entry.1.sources.2.1) hentry
  have htargets := congrArg
    (fun entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId => entry.1.targets) hentry
  change expanded.1.1.sources.1.1 = reference.1.1.sources.1.1 at hsourceFirst
  change expanded.1.1.sources.2.1 = reference.1.1.sources.2.1 at hsourceSecond
  change expanded.1.1.targets = reference.1.1.targets at htargets
  rw [hsourceFirst, hsourceSecond, htargets] at hmem
  exact hmem

/-! ## 4. Structural-fiber cardinality is controlled by the row carrier -/

private theorem nodup_map_of_injOn_local {A B : Type} (f : A → B) :
    ∀ (items : List A), items.Nodup →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        f left = f right → left = right) →
      (items.map f).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      refine List.nodup_cons.mpr ⟨?_,
        nodup_map_of_injOn_local f tail hparts.2
          (fun left hleft right hright =>
            hinjective left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright))⟩
      intro hmem
      obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
      have hhead := hinjective head List.mem_cons_self other
        (List.mem_cons_of_mem head hother) heq.symm
      exact hparts.1 (hhead ▸ hother)

private def finePacketConnectedRateProfiledLoweringCodeDecidableEq :
    DecidableEq FinePacketConnectedRateProfiledLoweringCode := by
  letI : DecidableEq
      YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel.PairChannelState :=
    inferInstance
  letI : DecidableEq
      (List
        YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel.PairChannelState) :=
    inferInstance
  letI : DecidableEq FinePacketLoweringWitnessPair :=
    @instDecidableEqProd _ _ inferInstance inferInstance
  exact @instDecidableEqProd _ _ inferInstance inferInstance

/-- The lowering projection remains duplicate-free on every structural fiber.
This is the finite injectivity statement proved in the preceding module,
recast as a property of the enumerated lowering-code list. -/
theorem finePacketConnectedRateProfiledStructuralFiberLoweringCodes_nodup
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    (finePacketConnectedRateProfiledStructuralFiberLoweringCodes
      S rate hrate0 orientation observableFaceId hobservableFace
        structural).Nodup := by
  unfold finePacketConnectedRateProfiledStructuralFiberLoweringCodes
  apply nodup_map_of_injOn_local
  · unfold finePacketConnectedRateProfiledStructuralFiberCodes
    exact List.filter_sublist.nodup
      (finePacketConnectedRateProfiledNormalizedTerminalCodes_nodup
        S rate hrate0 orientation observableFaceId hobservableFace)
  · intro left hleft right hright hlowering
    exact
      finePacketConnectedRateProfiledLoweringCompiler_injective_on_structuralFiber
        S rate hrate0 orientation observableFaceId hobservableFace structural
          left right hleft hright hlowering

/-- The lowering-code list over the structural projection of one reference
witness, named opaquely to keep later finite-list statements elaboration-stable. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    List FinePacketConnectedRateProfiledLoweringCode :=
  finePacketConnectedRateProfiledStructuralFiberLoweringCodes
    S rate hrate0 orientation observableFaceId hobservableFace
      (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
        S rate hrate0 orientation observableFaceId hobservableFace reference)

theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_nodup
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes
      S rate hrate0 orientation observableFaceId hobservableFace
        reference).Nodup := by
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes
  exact finePacketConnectedRateProfiledStructuralFiberLoweringCodes_nodup
    S rate hrate0 orientation observableFaceId hobservableFace
      (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
        S rate hrate0 orientation observableFaceId hobservableFace reference)

/-- Every lowering code in the reference structural fiber belongs to the
single exact oriented row carrier fixed by that reference. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_subset_carrier
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    ∀ lowering,
      lowering ∈
          finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes
            S rate hrate0 orientation observableFaceId hobservableFace reference →
        lowering ∈
          finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
            S orientation observableFaceId reference := by
  intro lowering hlowering
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes
      at hlowering
  unfold finePacketConnectedRateProfiledStructuralFiberLoweringCodes at hlowering
  obtain ⟨code, hcode, hcompiled⟩ := List.mem_map.mp hlowering
  have hparts := List.mem_filter.mp hcode
  have hstructural := of_decide_eq_true hparts.2
  rw [← hcompiled]
  exact
    finePacketConnectedRateProfiledLoweringCode_mem_orientedCarrier_of_terminal_mem_of_structural_eq
      S rate hrate0 orientation observableFaceId hobservableFace reference code
        hparts.1 hstructural.symm

/-- The realized lowering ambiguity of a structural fiber is no larger than
the exact source-row carrier already used by the normalized joint law. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_length_le_carrier
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes
        S rate hrate0 orientation observableFaceId hobservableFace
          reference).length ≤
      (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
        S orientation observableFaceId reference).length := by
  letI : DecidableEq FinePacketConnectedRateProfiledLoweringCode :=
    finePacketConnectedRateProfiledLoweringCodeDecidableEq
  exact
    YMGap.Continuum.FiniteBoolGraphSimplePaths.FiniteListBound.nodup_subset_length_le
      _ _
      (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_nodup
        S rate hrate0 orientation observableFaceId hobservableFace reference)
      (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_subset_carrier
        S rate hrate0 orientation observableFaceId hobservableFace reference)

/-- Consequently the whole terminal-code structural fiber has at most the
explicit oriented lowering-carrier cardinality. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberCardinality_le_carrier
    (S : SlabScalePair) (rate : YMGap.Constructive.Q')
    (hrate0 : (0 : YMGap.Constructive.Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    (finePacketConnectedRateProfiledStructuralFiberCodes
        S rate hrate0 orientation observableFaceId hobservableFace
          (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
            S rate hrate0 orientation observableFaceId hobservableFace
              reference)).length ≤
      (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
        S orientation observableFaceId reference).length := by
  rw [finePacketConnectedRateProfiledStructuralFiberCardinality_eq_loweringCodes_length]
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_length_le_carrier
      S rate hrate0 orientation observableFaceId hobservableFace reference

#print axioms finePacketGlobalNonzeroConnectedExpandedWitness_entry_eq_of_structural_eq
#print axioms finePacketOrientedLoweringCodeCarrier
#print axioms finePacketGlobalNonzeroConnectedExpandedWitness_lowering_mem_orientedCarrier
#print axioms finePacketOrientedLoweringCodeCarrier_nodup
#print axioms finePacketOrientedLoweringCodeCarrier_length
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
#print axioms finePacketConnectedRateProfiledLoweringCode_mem_orientedCarrier_of_terminal_mem_of_structural_eq
#print axioms finePacketConnectedRateProfiledStructuralFiberLoweringCodes_nodup
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_nodup
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_subset_carrier
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberLoweringCodes_length_le_carrier
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberCardinality_le_carrier

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralLoweringCarrier
