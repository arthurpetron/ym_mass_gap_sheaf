/-
# A faithful profiled compiler retaining the normalization rows

The common-rate terminal compiler is injective, but its canonical peeling
output forgets the exterior/core counters used by the corridor contraction,
and its code does not display the physical source rows that determine the
normalization denominator.

This file refines that compiler.  Its code records

  * the two physical source rows,
  * component size and the weighted shape-child code,
  * the complete fine/coarse profiled peeling outputs, and
  * both lowering-word pairs.

Forgetting profile counters recovers the already-faithful canonical terminal
compiler, so the refinement is injective.  Moreover, both the total profile
mass and the normalized terminal residual are literal functions of the new
code.  This is the exact deterministic key needed for subsequent inverse-fiber
Fubini: no normalization is hidden outside the compiler.

Constructive contract: projection equality, the existing canonical compiler
faithfulness, and proof irrelevance only; no classical choice, proof hole,
trusted external computation, computability escape, heartbeat increase, or
new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual
import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalCompilerFaithfulness

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfileCorridor
open YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The normalization-visible profiled code -/

abbrev FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :=
  (PositivePhysicalSource S × PositivePhysicalSource S) ×
    (Nat × (FinePacketConnectedComponentShapeChildCode ×
      (FinePacketConnectedFourEntryRateProfiledPeelingOutput
          S rate hrate0 ×
        (FinePacketLoweringWitnessPair × FinePacketLoweringWitnessPair))))

def finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
      S rate hrate0 :=
  (expanded.1.1.sources,
    (finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId expanded.1,
      (finePacketGlobalNonzeroConnectedEntryShapeChildCode
          S orientation observableFaceId hobservableFace expanded.1,
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
            S rate hrate0 orientation observableFaceId hobservableFace expanded,
          (expanded.2.1.2.1.1, expanded.2.1.2.2.1)))))

/-! ## 2. Forgetting counters recovers the faithful canonical compiler -/

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler_injective
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    Function.Injective
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
        S rate hrate0 orientation observableFaceId hobservableFace) := by
  intro left right hcode
  have hsize := congrArg
    (fun code :
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
          S rate hrate0 => code.2.1) hcode
  have hshape := congrArg
    (fun code :
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
          S rate hrate0 => code.2.2.1) hcode
  have hprofile := congrArg
    (fun code :
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
          S rate hrate0 => code.2.2.2.1) hcode
  have hlowering := congrArg
    (fun code :
        FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
          S rate hrate0 => code.2.2.2.2) hcode
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
  have hfineCanonical :
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left).1 =
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right).1 :=
    hforgetLeft.1.symm.trans (hfineProfile.trans hforgetRight.1)
  have hcoarseCanonical :
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left).2 =
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right).2 :=
    hforgetLeft.2.symm.trans (hcoarseProfile.trans hforgetRight.2)
  have hcanonical :
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace left =
        finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
          S rate hrate0 orientation observableFaceId hobservableFace right :=
    Prod.ext hfineCanonical hcoarseCanonical
  apply
    finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalCompiler_injective
      S rate hrate0 orientation observableFaceId hobservableFace
  exact Prod.ext hsize (Prod.ext hshape (Prod.ext hcanonical hlowering))

/-! ## 3. Profile mass and normalized terminal residual factor through code -/

def finePacketConnectedFourEntryRateProfiledCompilerCodeMass
    {S : SlabScalePair} {rate : Q'} {hrate0 : (0 : Q') ≤ rate}
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) : Nat :=
  let profiled := code.2.2.2.1
  (profiled.1.2.2.1 + profiled.1.2.2.2) +
    (profiled.2.2.2.1 + profiled.2.2.2.2)

theorem finePacketConnectedFourEntryRateProfiledCompilerCodeMass_compiler
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketConnectedFourEntryRateProfiledCompilerCodeMass
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace expanded) =
      finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
        S rate hrate0 orientation observableFaceId hobservableFace expanded := by
  rfl

def finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) : Q' :=
  let profiled := code.2.2.2.1
  Q'.divPos
    (slabAcceptedTwoReplicaStateWeight
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        profiled.1.1 *
      slabAcceptedTwoReplicaStateWeight
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        profiled.2.1)
    (finePacketOrientedEnvelopeNormalizationMass S code.1.1 code.1.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling code.1.1 code.1.2)

theorem finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual_compiler
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace expanded) ≈
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded := by
  exact Q'.eqv_refl _

#print axioms FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler_injective
#print axioms finePacketConnectedFourEntryRateProfiledCompilerCodeMass
#print axioms finePacketConnectedFourEntryRateProfiledCompilerCodeMass_compiler
#print axioms finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
#print axioms finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual_compiler

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
