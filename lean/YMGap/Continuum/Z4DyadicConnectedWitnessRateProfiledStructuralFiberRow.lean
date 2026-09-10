/-
# Reassemble one structural terminal fiber into its lowering row

The structural compiler forgets exactly the four lowering words.  The
preceding rigidity theorem places every realized lowering code in one exact,
duplicate-free oriented row carrier fixed by the reference physical witness.
This module upgrades that set-theoretic statement to the weighted statement
needed by the Gibbs normalization: the entire structural fiber is bounded by
the sum of its unchanged terminal weight over that row carrier.

No cardinality surrogate is inserted.  The proof is a literal weighted
injection, so the next contraction can sum the row by its existing exact
normalization theorem.

Constructive contract: finite-list injection, exact rational order, and the
explicit positive normalization witness only; no classical choice, proof
hole, trusted external computation, computability escape, heartbeat increase,
or new trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralLoweringCarrier

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralLoweringCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Positivity and the reference row weight -/

/-- The compiled profile-weighted terminal weight is nonnegative for every
code.  In particular, it is a valid target weight for a constructive weighted
injection. -/
theorem finePacketConnectedRateProfiledTerminalCodeWeight_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) :
    (0 : Q') ≤
      finePacketConnectedRateProfiledTerminalCodeWeight
        S hfineCutoff hcoarseCoupling rate hrate0 code := by
  unfold finePacketConnectedRateProfiledTerminalCodeWeight
  apply Q'.mul_nonneg
  · exact Q'.pow_nonneg anchorFaceCoefficient (by decide) _
  · unfold
      finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
      Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (slabAcceptedTwoReplicaStateWeight_nonnegative _ _)
        (slabAcceptedTwoReplicaStateWeight_nonnegative _ _))
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (finePacketOrientedEnvelopeNormalizationMass_pos
            S hfineCutoff hcoarseCoupling code.1.1 code.1.2)))

/-- The faithful terminal code of the chosen reference expanded witness. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
      S rate hrate0 :=
  finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
    S rate hrate0 orientation observableFaceId hobservableFace reference

/-- Every lowering word in the reference row carries the same structural
terminal-code weight.  Keeping this as a named function lets the following
weighted injection compose directly with later finite Fubini statements. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (_lowering : FinePacketConnectedRateProfiledLoweringCode) : Q' :=
  finePacketConnectedRateProfiledTerminalCodeWeight
    S hfineCutoff hcoarseCoupling rate hrate0
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
        S rate hrate0 orientation observableFaceId hobservableFace reference)

theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (lowering : FinePacketConnectedRateProfiledLoweringCode) :
    (0 : Q') ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace reference lowering := by
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
  exact finePacketConnectedRateProfiledTerminalCodeWeight_nonnegative
    S hfineCutoff hcoarseCoupling rate hrate0 _

/-! ## 2. Weighted structural-fiber injection -/

/-- **Structural-fiber row reassembly.**  The full weight over all terminal
codes with the reference structural projection is bounded by the exact sum
over the reference's oriented lowering row.  The encoding is the literal
lowering compiler, and its injectivity is supplied by full-code
faithfulness. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberWeight_le_loweringRow
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    fiberWeight
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledTerminalCodeWeight
          S hfineCutoff hcoarseCoupling rate hrate0)
        finePacketConnectedRateProfiledStructuralCompiler
        (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
          S rate hrate0 orientation observableFaceId hobservableFace
            reference) ≤
      listQSum
        (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace reference)
        (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
          S orientation observableFaceId reference) := by
  unfold fiberWeight
  change
    listQSum
        (finePacketConnectedRateProfiledTerminalCodeWeight
          S hfineCutoff hcoarseCoupling rate hrate0)
        (finePacketConnectedRateProfiledStructuralFiberCodes
          S rate hrate0 orientation observableFaceId hobservableFace
            (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
              S rate hrate0 orientation observableFaceId hobservableFace
                reference)) ≤ _
  apply listQSum_le_of_injective_nodup
    (finePacketConnectedRateProfiledStructuralFiberCodes
      S rate hrate0 orientation observableFaceId hobservableFace
        (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
          S rate hrate0 orientation observableFaceId hobservableFace reference))
    (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
      S orientation observableFaceId reference)
    (finePacketConnectedRateProfiledTerminalCodeWeight
      S hfineCutoff hcoarseCoupling rate hrate0)
    (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace reference)
    finePacketConnectedRateProfiledLoweringCompiler
  · unfold finePacketConnectedRateProfiledStructuralFiberCodes
    exact List.filter_sublist.nodup
      (finePacketConnectedRateProfiledNormalizedTerminalCodes_nodup
        S rate hrate0 orientation observableFaceId hobservableFace)
  · exact finePacketOrientedLoweringCodeCarrier_nodup
      S orientation reference.1.1.sources.1.1 reference.1.1.sources.2.1
        reference.1.1.targets
  · intro code hcode
    have hparts := List.mem_filter.mp hcode
    have hstructural := of_decide_eq_true hparts.2
    exact
      finePacketConnectedRateProfiledLoweringCode_mem_orientedCarrier_of_terminal_mem_of_structural_eq
        S rate hrate0 orientation observableFaceId hobservableFace reference
          code hparts.1 hstructural.symm
  · intro left hleft right hright hlowering
    exact
      finePacketConnectedRateProfiledLoweringCompiler_injective_on_structuralFiber
        S rate hrate0 orientation observableFaceId hobservableFace
          (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode
            S rate hrate0 orientation observableFaceId hobservableFace reference)
          left right hleft hright hlowering
  · intro code hcode
    have hstructural :=
      of_decide_eq_true (List.mem_filter.mp hcode).2
    apply Q'.le_of_eqv
    unfold
      finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
    apply finePacketConnectedRateProfiledTerminalCodeWeight_eqv_of_structural_eq
      S hfineCutoff hcoarseCoupling rate hrate0
    unfold finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode at hstructural
    exact hstructural.symm
  · intro lowering _
    exact
      finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight_nonnegative
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace reference lowering

#print axioms finePacketConnectedRateProfiledTerminalCodeWeight_nonnegative
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight_nonnegative
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberWeight_le_loweringRow

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow
