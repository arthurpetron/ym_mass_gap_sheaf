/-
# Exact fibers of the normalization-visible profiled compiler

The expanded connected witness carrier is duplicate-free, and the profiled
terminal compiler retaining the two normalization rows is injective.  Hence
its literal image list is already duplicate-free: no `eraseDups` quotient is
needed.  More strongly, the complete inverse fiber over the code of a source
is exactly the singleton containing that source.

This file turns that bijection into two exact finite Fubini identities.  One
reindexes the normalized terminal residual; the other reindexes the spatially
weighted terminal residual that bounds the connected witness mass.  This
removes inverse-fiber multiplicity from the next summation problem, but does
not yet bound the resulting terminal-code sum.

Constructive contract: duplicate-free finite lists, injectivity, filtering,
and exact rational finite sums only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.CompactDualSlabExpandedTargetKey
import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem nodup_map_of_injective_local {A B : Type}
    (map : A → B) (hinjective : Function.Injective map) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective_local map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective heq.symm) ▸ hitem)

private theorem filter_decide_code_eq_empty
    {Source Target : Type} [DecidableEq Target]
    (target : Target) (code : Source → Target) :
    ∀ source : List Source,
      (∀ item, item ∈ source → target ≠ code item) →
      source.filter (fun item => decide (target = code item)) = []
  | [], _ => rfl
  | head :: tail, houtside => by
      have hhead : target ≠ code head :=
        houtside head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → target ≠ code item :=
        fun item hitem =>
          houtside item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, decide_eq_false hhead,
        Bool.false_eq_true, if_false]
      exact filter_decide_code_eq_empty target code tail htail

private theorem filter_code_eq_singleton_of_injective_nodup
    {Source Target : Type} [DecidableEq Target]
    (code : Source → Target) (selected : Source) :
    ∀ source : List Source,
      source.Nodup → selected ∈ source →
      Function.Injective code →
      source.filter
          (fun item => decide (code selected = code item)) =
        [selected]
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem, hinjective => by
      have hnodupParts := List.nodup_cons.mp hnodup
      by_cases hhead : code selected = code head
      · have hselected : selected = head := hinjective hhead
        subst selected
        have houtside : ∀ item, item ∈ tail →
            code head ≠ code item := by
          intro item hitem hcode
          have heq : head = item := hinjective hcode
          subst item
          exact hnodupParts.1 hitem
        rw [List.filter_cons,
          filter_decide_code_eq_empty (code head) code tail houtside]
        simp
      · have hselectedTail : selected ∈ tail := by
          rcases List.mem_cons.mp hmem with hselectedHead | htail
          · exact False.elim (hhead (congrArg code hselectedHead))
          · exact htail
        simp only [List.filter_cons, decide_eq_false hhead,
          Bool.false_eq_true, if_false]
        exact filter_code_eq_singleton_of_injective_nodup
          code selected tail hnodupParts.2 hselectedTail hinjective

/-! ## 1. Exact decidable keys for the raw compiler code -/

/-- The physical row is read on its complete finite slab support. -/
def positivePhysicalSourceFiniteKey
    (S : SlabScalePair) (source : PositivePhysicalSource S) : List Nat :=
  finiteEdgeLabellingWord S.fine.faceEdges source.1

theorem positivePhysicalSource_eq_of_finiteKey_eq
    (S : SlabScalePair) (left right : PositivePhysicalSource S)
    (hkey : positivePhysicalSourceFiniteKey S left =
      positivePhysicalSourceFiniteKey S right) :
    left = right := by
  apply Subtype.ext
  apply edgeLabelling_eq_of_word_eq_of_supported S.fine.faceEdges
  · exact (boundedEdgeLabellings_sound S.fine.cutoff S.fine.faceEdges
      left.1 left.2.1).2
  · exact (boundedEdgeLabellings_sound S.fine.cutoff S.fine.faceEdges
      right.1 right.2.1).2
  · exact hkey

abbrev SlabAcceptedPairedHighSpinProfileExactKey :=
  (SlabExpandedFineTargetKey × SlabExpandedFineTargetKey) ×
    (List SlabAcceptedPairedPeelRecord × Nat × Nat)

def slabAcceptedPairedHighSpinProfileExactKey
    (D : SlabPhysicalData)
    (output : SlabAcceptedPairedHighSpinProfileOutput D) :
    SlabAcceptedPairedHighSpinProfileExactKey :=
  ((output.1.1.key, output.1.2.key),
    (output.2.1, output.2.2.1, output.2.2.2))

theorem slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
    (D : SlabPhysicalData)
    (left right : SlabAcceptedPairedHighSpinProfileOutput D)
    (hkey : slabAcceptedPairedHighSpinProfileExactKey D left =
      slabAcceptedPairedHighSpinProfileExactKey D right) :
    left = right := by
  have hstateKeys := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.1) hkey
  have hleftEntryKey := congrArg
    (fun keys : SlabExpandedFineTargetKey × SlabExpandedFineTargetKey =>
      keys.1) hstateKeys
  have hrightEntryKey := congrArg
    (fun keys : SlabExpandedFineTargetKey × SlabExpandedFineTargetKey =>
      keys.2) hstateKeys
  have hstate : left.1 = right.1 := Prod.ext
    (SlabExpandedFineSourceEntry.eq_of_key_eq hleftEntryKey)
    (SlabExpandedFineSourceEntry.eq_of_key_eq hrightEntryKey)
  have htrace := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.1) hkey
  have hexterior := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.2.1) hkey
  have hcore := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.2.2) hkey
  exact Prod.ext hstate (Prod.ext htrace (Prod.ext hexterior hcore))

structure FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey :
    Type where
  leftSource : List Nat
  rightSource : List Nat
  componentSize : Nat
  shapeChild : FinePacketConnectedComponentShapeChildCode
  fineProfile : SlabAcceptedPairedHighSpinProfileExactKey
  coarseProfile : SlabAcceptedPairedHighSpinProfileExactKey
  fineLowering : FinePacketLoweringWitnessPair
  coarseLowering : FinePacketLoweringWitnessPair
deriving DecidableEq

def finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
    {S : SlabScalePair} {rate : Q'} {hrate0 : (0 : Q') ≤ rate}
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) :
    FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey :=
  { leftSource := positivePhysicalSourceFiniteKey S code.1.1
    rightSource := positivePhysicalSourceFiniteKey S code.1.2
    componentSize := code.2.1
    shapeChild := code.2.2.1
    fineProfile := slabAcceptedPairedHighSpinProfileExactKey
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      code.2.2.2.1.1
    coarseProfile := slabAcceptedPairedHighSpinProfileExactKey
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      code.2.2.2.1.2
    fineLowering := code.2.2.2.2.1
    coarseLowering := code.2.2.2.2.2 }

theorem finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode_eq_of_exactKey_eq
    {S : SlabScalePair} {rate : Q'} {hrate0 : (0 : Q') ≤ rate}
    (left right :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hkey :
      finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
          left =
        finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
          right) :
    left = right := by
  have hsource : left.1 = right.1 := Prod.ext
    (positivePhysicalSource_eq_of_finiteKey_eq S left.1.1 right.1.1
      (congrArg
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.leftSource
        hkey))
    (positivePhysicalSource_eq_of_finiteKey_eq S left.1.2 right.1.2
      (congrArg
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.rightSource
        hkey))
  have hsize := congrArg
    FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.componentSize
    hkey
  have hshape := congrArg
    FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.shapeChild
    hkey
  have hprofile : left.2.2.2.1 = right.2.2.2.1 := Prod.ext
    (slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      left.2.2.2.1.1 right.2.2.2.1.1
      (congrArg
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.fineProfile
        hkey))
    (slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      left.2.2.2.1.2 right.2.2.2.1.2
      (congrArg
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.coarseProfile
        hkey))
  have hlowering : left.2.2.2.2 = right.2.2.2.2 := Prod.ext
    (congrArg
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.fineLowering
      hkey)
    (congrArg
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey.coarseLowering
      hkey)
  exact Prod.ext hsource
    (Prod.ext hsize (Prod.ext hshape (Prod.ext hprofile hlowering)))

private def profiledNormalizedTerminalCompilerCodeDecidableEq
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :
    DecidableEq
      (FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) :=
  fun left right =>
    if hkey :
        finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
            left =
          finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
            right then
      isTrue
        (finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode_eq_of_exactKey_eq
          left right hkey)
    else
      isFalse (fun heq => hkey (congrArg
        finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
        heq))

local instance (S : SlabScalePair) (rate : Q')
    (hrate0 : (0 : Q') ≤ rate) :
    DecidableEq
      (FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) :=
  profiledNormalizedTerminalCompilerCodeDecidableEq S rate hrate0

/-! ## 2. The literal realized-code carrier -/

def finePacketConnectedRateProfiledNormalizedTerminalCodes
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    List (FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
      S rate hrate0) :=
  (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId).map
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
      S rate hrate0 orientation observableFaceId hobservableFace)

theorem finePacketConnectedRateProfiledNormalizedTerminalCodes_nodup
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace).Nodup := by
  unfold finePacketConnectedRateProfiledNormalizedTerminalCodes
  apply nodup_map_of_injective_local
  · exact
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler_injective
        S rate hrate0 orientation observableFaceId hobservableFace
  · exact finePacketGlobalNonzeroConnectedExpandedWitnessEntries_nodup
      S orientation observableFaceId

theorem finePacketConnectedRateProfiledNormalizedTerminalCode_mem
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hexpanded : expanded ∈
      finePacketGlobalNonzeroConnectedExpandedWitnessEntries
        S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
        S rate hrate0 orientation observableFaceId hobservableFace expanded ∈
      finePacketConnectedRateProfiledNormalizedTerminalCodes
        S rate hrate0 orientation observableFaceId hobservableFace := by
  exact List.mem_map.mpr ⟨expanded, hexpanded, rfl⟩

/-! ## 3. Every realized compiler fiber is exactly one source -/

theorem finePacketConnectedRateProfiledNormalizedTerminalFiber_eq_singleton
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hexpanded : expanded ∈
      finePacketGlobalNonzeroConnectedExpandedWitnessEntries
        S orientation observableFaceId) :
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
        S orientation observableFaceId).filter
      (fun item => decide
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace expanded =
          finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace item)) =
      [expanded] := by
  exact filter_code_eq_singleton_of_injective_nodup
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
      S rate hrate0 orientation observableFaceId hobservableFace)
    expanded
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId)
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries_nodup
      S orientation observableFaceId)
    hexpanded
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler_injective
      S rate hrate0 orientation observableFaceId hobservableFace)

theorem finePacketConnectedRateProfiledNormalizedTerminalFiber_length_eq_one
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hexpanded : expanded ∈
      finePacketGlobalNonzeroConnectedExpandedWitnessEntries
        S orientation observableFaceId) :
    ((finePacketGlobalNonzeroConnectedExpandedWitnessEntries
        S orientation observableFaceId).filter
      (fun item => decide
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace expanded =
          finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace item))).length = 1 := by
  rw [finePacketConnectedRateProfiledNormalizedTerminalFiber_eq_singleton
    S rate hrate0 orientation observableFaceId hobservableFace expanded hexpanded]
  rfl

/-! ## 4. Exact residual fibers and finite Fubini -/

theorem finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_at_source
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hexpanded : expanded ∈
      finePacketGlobalNonzeroConnectedExpandedWitnessEntries
        S orientation observableFaceId) :
    fiberWeight
        (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
          S orientation observableFaceId)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace expanded) ≈
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded := by
  unfold fiberWeight
  rw [finePacketConnectedRateProfiledNormalizedTerminalFiber_eq_singleton
    S rate hrate0 orientation observableFaceId hobservableFace expanded hexpanded]
  exact Q'.eqv_of_eq (Q'.add_zero' _)

theorem finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_eqv_codeResidual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hexpanded : expanded ∈
      finePacketGlobalNonzeroConnectedExpandedWitnessEntries
        S orientation observableFaceId) :
    fiberWeight
        (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
          S orientation observableFaceId)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace expanded) ≈
      finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace expanded) := by
  exact Q'.eqv_trans _ _ _
    (finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_at_source
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded hexpanded)
    (Q'.eqv_symm
      (finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual_compiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded))

theorem finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_eqv_codeResidual_of_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hcode : code ∈
      finePacketConnectedRateProfiledNormalizedTerminalCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    fiberWeight
        (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
          S orientation observableFaceId)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace)
        code ≈
      finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0 code := by
  unfold finePacketConnectedRateProfiledNormalizedTerminalCodes at hcode
  obtain ⟨expanded, hexpanded, rfl⟩ := List.mem_map.mp hcode
  exact
    finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_eqv_codeResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded hexpanded

theorem finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (fiberWeight
          (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
            S orientation observableFaceId)
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
              hobservableFace)
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace))
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace) ≈
      listQSum
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
          S orientation observableFaceId) := by
  exact fiberWeight_total
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId)
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledNormalizedTerminalCodes_nodup
      S rate hrate0 orientation observableFaceId hobservableFace)
    (fun expanded hexpanded =>
      finePacketConnectedRateProfiledNormalizedTerminalCode_mem
        S rate hrate0 orientation observableFaceId hobservableFace
          expanded hexpanded)

/-- Exact compiler-coordinate Fubini for the normalized terminal residual.
The injective code changes the indexing set but neither loses nor duplicates
any residual mass. -/
theorem finePacketConnectedRateProfiledNormalizedTerminalCodeResidual_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0)
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace) ≈
      listQSum
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
          S orientation observableFaceId) := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr_on
      (finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0)
      (fiberWeight
        (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
          S orientation observableFaceId)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace))
      (finePacketConnectedRateProfiledNormalizedTerminalCodes
        S rate hrate0 orientation observableFaceId hobservableFace)
      (fun code hcode => Q'.eqv_symm
        (finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_eqv_codeResidual_of_mem
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace code hcode)))
    (finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_total
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

/-! ## 5. The spatial residual also reindexes with no loss -/

def finePacketConnectedRateDistanceTerminalResidualWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  anchorFaceCoefficient ^
      finePacketGlobalNonzeroConnectedEntryDistance
        S orientation observableFaceId hobservableFace expanded.1 *
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded

theorem finePacketConnectedRateDistanceTerminalResidualFiber_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (fiberWeight
          (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
            S orientation observableFaceId)
          (finePacketConnectedRateDistanceTerminalResidualWeight
            S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
              hobservableFace)
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace))
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace) ≈
      finePacketGlobalNonzeroConnectedExpandedWitnessRateDistanceTerminalResidualMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  have htotal := fiberWeight_total
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId)
    (finePacketConnectedRateDistanceTerminalResidualWeight
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledNormalizedTerminalCodes_nodup
      S rate hrate0 orientation observableFaceId hobservableFace)
    (fun expanded hexpanded =>
      finePacketConnectedRateProfiledNormalizedTerminalCode_mem
        S rate hrate0 orientation observableFaceId hobservableFace
          expanded hexpanded)
  simpa only [finePacketConnectedRateDistanceTerminalResidualWeight,
    finePacketGlobalNonzeroConnectedExpandedWitnessRateDistanceTerminalResidualMass,
    finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler]
    using htotal

#print axioms positivePhysicalSourceFiniteKey
#print axioms positivePhysicalSource_eq_of_finiteKey_eq
#print axioms SlabAcceptedPairedHighSpinProfileExactKey
#print axioms slabAcceptedPairedHighSpinProfileExactKey
#print axioms slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
#print axioms FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
#print axioms finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerExactKey
#print axioms finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode_eq_of_exactKey_eq
#print axioms finePacketConnectedRateProfiledNormalizedTerminalCodes
#print axioms finePacketConnectedRateProfiledNormalizedTerminalCodes_nodup
#print axioms finePacketConnectedRateProfiledNormalizedTerminalCode_mem
#print axioms finePacketConnectedRateProfiledNormalizedTerminalFiber_eq_singleton
#print axioms finePacketConnectedRateProfiledNormalizedTerminalFiber_length_eq_one
#print axioms finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_at_source
#print axioms finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_eqv_codeResidual
#print axioms finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_eqv_codeResidual_of_mem
#print axioms finePacketConnectedRateProfiledNormalizedTerminalResidualFiber_total
#print axioms finePacketConnectedRateProfiledNormalizedTerminalCodeResidual_total
#print axioms finePacketConnectedRateDistanceTerminalResidualWeight
#print axioms finePacketConnectedRateDistanceTerminalResidualFiber_total

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
