/-
# Separate structural entropy from lowering-word multiplicity

The terminal-summary fiber contains two mathematically different sources of
multiplicity.  Component shapes and canonical peeling profiles are local
entropy paid by the retained profile power.  The four SU(2) lowering words,
in contrast, expand the source-dependent tilted Gibbs rows and must remain
with their exact row normalization.

This module inserts the missing quotient between the faithful terminal code
and its coarse terminal summary.  The structural code retains both source
rows, the component size and shape-child word, and the complete fine/coarse
profiled peeling outputs, but forgets exactly the two lowering-word pairs.
It proves:

* structural equality plus lowering equality reconstructs the faithful code;
* the terminal summand is constant on every structural fiber;
* exact finite Fubini reindexes the full code mass over structural fibers; and
* the structural fiber injects into the realized lowering-pair codes.

Thus no volume-dependent exterior lowering count is silently charged to the
local profile exponent.  The next normalization step can sum those words as
the literal tilted Gibbs multiplicities they represent.

Constructive contract: exact finite keys, projection equalities, finite-list
Fubini, and proof irrelevance only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new
trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSummaryFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSummaryFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filterTrueLocal {A : Type} : ∀ items : List A,
    items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

/-! ## 1. Forget exactly the lowering-word coordinates -/

structure FinePacketConnectedRateProfiledStructuralCode : Type where
  leftSource : List Nat
  rightSource : List Nat
  componentSize : Nat
  shapeChild : FinePacketConnectedComponentShapeChildCode
  fineProfile : SlabAcceptedPairedHighSpinProfileExactKey
  coarseProfile : SlabAcceptedPairedHighSpinProfileExactKey
deriving DecidableEq

abbrev FinePacketConnectedRateProfiledLoweringCode :=
  FinePacketLoweringWitnessPair × FinePacketLoweringWitnessPair

def finePacketConnectedRateProfiledStructuralCompiler
    {S : SlabScalePair} {rate : Q'} {hrate0 : (0 : Q') ≤ rate}
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) : FinePacketConnectedRateProfiledStructuralCode where
  leftSource := positivePhysicalSourceFiniteKey S code.1.1
  rightSource := positivePhysicalSourceFiniteKey S code.1.2
  componentSize := code.2.1
  shapeChild := code.2.2.1
  fineProfile := slabAcceptedPairedHighSpinProfileExactKey
    (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
    code.2.2.2.1.1
  coarseProfile := slabAcceptedPairedHighSpinProfileExactKey
    (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
    code.2.2.2.1.2

def finePacketConnectedRateProfiledLoweringCompiler
    {S : SlabScalePair} {rate : Q'} {hrate0 : (0 : Q') ≤ rate}
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) : FinePacketConnectedRateProfiledLoweringCode :=
  code.2.2.2.2

private def normalizedTerminalResidualOfStructuralParts
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (sources : PositivePhysicalSource S × PositivePhysicalSource S)
    (profiled : FinePacketConnectedFourEntryRateProfiledPeelingOutput
      S rate hrate0) : Q' :=
  Q'.divPos
    (slabAcceptedTwoReplicaStateWeight
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        profiled.1.1 *
      slabAcceptedTwoReplicaStateWeight
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        profiled.2.1)
    (finePacketOrientedEnvelopeNormalizationMass S sources.1 sources.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling sources.1 sources.2)

private theorem codeNormalizedTerminalResidual_eqv_structuralParts
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) :
    finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0 code ≈
      normalizedTerminalResidualOfStructuralParts
        S hfineCutoff hcoarseCoupling rate hrate0 code.1 code.2.2.2.1 := by
  exact Q'.eqv_refl _

/-- The structural code forgets exactly the two lowering-word pairs: putting
those pairs back makes the existing faithful exact key complete. -/
theorem finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode_eq_of_structural_eq_of_lowering_eq
    {S : SlabScalePair} {rate : Q'} {hrate0 : (0 : Q') ≤ rate}
    (left right :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hstructural :
      finePacketConnectedRateProfiledStructuralCompiler left =
        finePacketConnectedRateProfiledStructuralCompiler right)
    (hlowering :
      finePacketConnectedRateProfiledLoweringCompiler left =
        finePacketConnectedRateProfiledLoweringCompiler right) :
    left = right := by
  have hsource : left.1 = right.1 := Prod.ext
    (positivePhysicalSource_eq_of_finiteKey_eq S left.1.1 right.1.1
      (congrArg FinePacketConnectedRateProfiledStructuralCode.leftSource
        hstructural))
    (positivePhysicalSource_eq_of_finiteKey_eq S left.1.2 right.1.2
      (congrArg FinePacketConnectedRateProfiledStructuralCode.rightSource
        hstructural))
  have hsize : left.2.1 = right.2.1 :=
    congrArg FinePacketConnectedRateProfiledStructuralCode.componentSize
      hstructural
  have hshape : left.2.2.1 = right.2.2.1 :=
    congrArg FinePacketConnectedRateProfiledStructuralCode.shapeChild
      hstructural
  have hprofile : left.2.2.2.1 = right.2.2.2.1 := Prod.ext
    (slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      left.2.2.2.1.1 right.2.2.2.1.1
      (congrArg FinePacketConnectedRateProfiledStructuralCode.fineProfile
        hstructural))
    (slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      left.2.2.2.1.2 right.2.2.2.1.2
      (congrArg FinePacketConnectedRateProfiledStructuralCode.coarseProfile
        hstructural))
  exact Prod.ext hsource
    (Prod.ext hsize (Prod.ext hshape (Prod.ext hprofile hlowering)))

/-! ## 2. The terminal weight factors through the structural code -/

theorem finePacketConnectedRateProfiledTerminalCodeWeight_eqv_of_structural_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (left right :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hstructural :
      finePacketConnectedRateProfiledStructuralCompiler left =
        finePacketConnectedRateProfiledStructuralCompiler right) :
    finePacketConnectedRateProfiledTerminalCodeWeight
        S hfineCutoff hcoarseCoupling rate hrate0 left ≈
      finePacketConnectedRateProfiledTerminalCodeWeight
        S hfineCutoff hcoarseCoupling rate hrate0 right := by
  have hsource : left.1 = right.1 := Prod.ext
    (positivePhysicalSource_eq_of_finiteKey_eq S left.1.1 right.1.1
      (congrArg FinePacketConnectedRateProfiledStructuralCode.leftSource
        hstructural))
    (positivePhysicalSource_eq_of_finiteKey_eq S left.1.2 right.1.2
      (congrArg FinePacketConnectedRateProfiledStructuralCode.rightSource
        hstructural))
  have hprofile : left.2.2.2.1 = right.2.2.2.1 := Prod.ext
    (slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      left.2.2.2.1.1 right.2.2.2.1.1
      (congrArg FinePacketConnectedRateProfiledStructuralCode.fineProfile
        hstructural))
    (slabAcceptedPairedHighSpinProfileOutput_eq_of_exactKey_eq
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      left.2.2.2.1.2 right.2.2.2.1.2
      (congrArg FinePacketConnectedRateProfiledStructuralCode.coarseProfile
        hstructural))
  have hmass :
      finePacketConnectedFourEntryRateProfiledCompilerCodeMass left =
        finePacketConnectedFourEntryRateProfiledCompilerCodeMass right := by
    unfold finePacketConnectedFourEntryRateProfiledCompilerCodeMass
    rw [hprofile]
  have hresidual :
      finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 left ≈
        finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 right := by
    refine Q'.eqv_trans _
      (normalizedTerminalResidualOfStructuralParts
        S hfineCutoff hcoarseCoupling rate hrate0 left.1 left.2.2.2.1) _
      (codeNormalizedTerminalResidual_eqv_structuralParts
        S hfineCutoff hcoarseCoupling rate hrate0 left) ?_
    rw [hsource, hprofile]
    exact Q'.eqv_symm
      (codeNormalizedTerminalResidual_eqv_structuralParts
        S hfineCutoff hcoarseCoupling rate hrate0 right)
  unfold finePacketConnectedRateProfiledTerminalCodeWeight
  rw [hmass]
  exact Q'.mul_eqv_congr_left _ _ _ hresidual

/-! ## 3. Exact structural Fubini -/

def finePacketConnectedRateProfiledStructuralCodes
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    List FinePacketConnectedRateProfiledStructuralCode :=
  ((finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace).map
    finePacketConnectedRateProfiledStructuralCompiler).eraseDups

theorem finePacketConnectedRateProfiledStructuralCodes_nodup
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    (finePacketConnectedRateProfiledStructuralCodes
      S rate hrate0 orientation observableFaceId hobservableFace).Nodup := by
  unfold finePacketConnectedRateProfiledStructuralCodes
  exact eraseDupsNodupLocal _

theorem finePacketConnectedRateProfiledStructuralCode_mem
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hcode : code ∈
      finePacketConnectedRateProfiledNormalizedTerminalCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    finePacketConnectedRateProfiledStructuralCompiler code ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace := by
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨code, hcode, rfl⟩

theorem finePacketConnectedRateProfiledStructuralFiber_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (fiberWeight
          (finePacketConnectedRateProfiledNormalizedTerminalCodes
            S rate hrate0 orientation observableFaceId hobservableFace)
          (finePacketConnectedRateProfiledTerminalCodeWeight
            S hfineCutoff hcoarseCoupling rate hrate0)
          finePacketConnectedRateProfiledStructuralCompiler)
        (finePacketConnectedRateProfiledStructuralCodes
          S rate hrate0 orientation observableFaceId hobservableFace) ≈
      finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  exact fiberWeight_total
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledTerminalCodeWeight
      S hfineCutoff hcoarseCoupling rate hrate0)
    finePacketConnectedRateProfiledStructuralCompiler
    (finePacketConnectedRateProfiledStructuralCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledStructuralCodes_nodup
      S rate hrate0 orientation observableFaceId hobservableFace)
    (fun code hcode =>
      finePacketConnectedRateProfiledStructuralCode_mem
        S rate hrate0 orientation observableFaceId hobservableFace code hcode)

/-! ## 4. A structural fiber has only lowering-word ambiguity -/

def finePacketConnectedRateProfiledStructuralFiberCodes
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    List (FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
      S rate hrate0) :=
  (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace).filter
    (fun code => decide
      (structural = finePacketConnectedRateProfiledStructuralCompiler code))

def finePacketConnectedRateProfiledStructuralFiberLoweringCodes
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    List FinePacketConnectedRateProfiledLoweringCode :=
  (finePacketConnectedRateProfiledStructuralFiberCodes
    S rate hrate0 orientation observableFaceId hobservableFace structural).map
      finePacketConnectedRateProfiledLoweringCompiler

theorem finePacketConnectedRateProfiledLoweringCompiler_injective_on_structuralFiber
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (left right :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hleft : left ∈ finePacketConnectedRateProfiledStructuralFiberCodes
      S rate hrate0 orientation observableFaceId hobservableFace structural)
    (hright : right ∈ finePacketConnectedRateProfiledStructuralFiberCodes
      S rate hrate0 orientation observableFaceId hobservableFace structural)
    (hlowering :
      finePacketConnectedRateProfiledLoweringCompiler left =
        finePacketConnectedRateProfiledLoweringCompiler right) :
    left = right := by
  have hleftStructural :=
    of_decide_eq_true (List.mem_filter.mp hleft).2
  have hrightStructural :=
    of_decide_eq_true (List.mem_filter.mp hright).2
  apply
    finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode_eq_of_structural_eq_of_lowering_eq
      left right
  · exact hleftStructural.symm.trans hrightStructural
  · exact hlowering

theorem finePacketConnectedRateProfiledStructuralFiberCardinality_eq_loweringCodes_length
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    (finePacketConnectedRateProfiledStructuralFiberCodes
        S rate hrate0 orientation observableFaceId hobservableFace structural).length =
      (finePacketConnectedRateProfiledStructuralFiberLoweringCodes
        S rate hrate0 orientation observableFaceId hobservableFace structural).length := by
  unfold finePacketConnectedRateProfiledStructuralFiberLoweringCodes
  rw [List.length_map]

/-! ## 5. Axiom audit -/

#print axioms FinePacketConnectedRateProfiledStructuralCode
#print axioms finePacketConnectedRateProfiledStructuralCompiler
#print axioms finePacketConnectedRateProfiledLoweringCompiler
#print axioms finePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode_eq_of_structural_eq_of_lowering_eq
#print axioms finePacketConnectedRateProfiledTerminalCodeWeight_eqv_of_structural_eq
#print axioms finePacketConnectedRateProfiledStructuralCodes
#print axioms finePacketConnectedRateProfiledStructuralCodes_nodup
#print axioms finePacketConnectedRateProfiledStructuralFiber_total
#print axioms finePacketConnectedRateProfiledStructuralFiberCodes
#print axioms finePacketConnectedRateProfiledStructuralFiberLoweringCodes
#print axioms finePacketConnectedRateProfiledLoweringCompiler_injective_on_structuralFiber
#print axioms finePacketConnectedRateProfiledStructuralFiberCardinality_eq_loweringCodes_length

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
