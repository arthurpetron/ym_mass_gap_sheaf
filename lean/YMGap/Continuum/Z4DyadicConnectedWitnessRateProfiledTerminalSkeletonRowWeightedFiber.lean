/-
# Pay the adaptive terminal-skeleton row fiber

The terminal-skeleton row code stores the exact lowering-row weight.  Hence
that weight is constant on its structural fiber.  Combining this literal
factorization with the two-scale adaptive trace count gives

  fiberWeight <= componentAdaptiveEntropyBase^profileMass * rowWeight.

This is the weighted form of the inverse-fiber theorem needed to combine the
adaptive multiplicity with the already-retained anchor coefficient.  The
next layer will factor that coefficient and sum the remaining lowering rows
through the source-dependent Gibbs normalization.

Constructive contract: exact finite sums, explicit nonnegativity, and the
kernel-checked row-fiber cardinality only; no classical choice, proof hole,
trusted external computation, computability escape, heartbeat increase, or
new trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowWeightedFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini

/-! ## 1. Positivity and exact constancy of the row weight -/

theorem finePacketConnectedRateProfiledStructuralLoweringRowEnvelope_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    (0 : Q') ≤
      finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace structural := by
  unfold finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
  split
  · exact Q'.le_refl' 0
  · rename_i reference hreference
    apply listQSum_nonnegative_on
    intro lowering _hlowering
    exact
      finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight_nonnegative
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace reference lowering

theorem finePacketConnectedRateProfiledStructuralLoweringRowEnvelope_eq_rowWeight_of_mem
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
    finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace structural = row.weight := by
  have hcompiler :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace row structural hstructural
  have hweight := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.weight hcompiler
  simpa only [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler,
    weightedTerminalSkeletonRowCode_weight] using hweight

theorem finePacketConnectedRateProfiledTerminalSkeletonRowWeight_nonnegative_of_mem
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
    (0 : Q') ≤ row.weight := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowCodes at hrow
  have hmapped := List.mem_eraseDups.mp hrow
  obtain ⟨structural, hstructural, hcompiler⟩ := List.mem_map.mp hmapped
  have hnonnegative :=
    finePacketConnectedRateProfiledStructuralLoweringRowEnvelope_nonnegative
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace structural
  have hweight := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.weight hcompiler
  have hweight' :
      finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace structural = row.weight := by
    simpa only [finePacketConnectedRateProfiledTerminalSkeletonRowCompiler,
      weightedTerminalSkeletonRowCode_weight] using hweight
  rw [← hweight']
  exact hnonnegative

/-! ## 2. Weighted inverse-fiber estimate -/

theorem finePacketConnectedRateProfiledStructuralRowEnvelopeMass_le_length_mul
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
    listQSum
        (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row) ≤
      Q'.ofNat
          (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row).length *
        row.weight := by
  have hrowNonnegative :=
    finePacketConnectedRateProfiledTerminalSkeletonRowWeight_nonnegative_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  exact listQSum_le_length_mul
    (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace)
    hrowNonnegative _ (fun structural hstructural => by
      rw [finePacketConnectedRateProfiledStructuralLoweringRowEnvelope_eq_rowWeight_of_mem
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row structural hstructural]
      exact Q'.le_refl' row.weight)

theorem finePacketConnectedRateProfiledStructuralRowEnvelopeMass_le_profileMultiplicity
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
    listQSum
        (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row) ≤
      Q'.ofNat
          (componentAdaptiveEntropyBase ^
            ((row.fineExterior + row.fineCore) +
              (row.coarseExterior + row.coarseCore))) *
        row.weight := by
  have hsum :=
    finePacketConnectedRateProfiledStructuralRowEnvelopeMass_le_length_mul
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hcardinality :=
    finePacketConnectedRateProfiledStructuralRowFiber_length_le_profileMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hcardinalityQ : Q'.ofNat
        (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row).length ≤
      Q'.ofNat
        (componentAdaptiveEntropyBase ^
          ((row.fineExterior + row.fineCore) +
            (row.coarseExterior + row.coarseCore))) :=
    Q'.ofNat_le_ofNat hcardinality
  have hrowNonnegative :=
    finePacketConnectedRateProfiledTerminalSkeletonRowWeight_nonnegative_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
    hcardinalityQ hrowNonnegative
  exact Q'.le_trans' _ _ _ hsum hscale

/-- Every terminal-skeleton row fiber pays only the exact adaptive entropy
base at its named total fine/coarse profile mass. -/
theorem finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le
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
    fiberWeight
        (finePacketConnectedRateProfiledStructuralCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace)
        row ≤
      Q'.ofNat
          (componentAdaptiveEntropyBase ^
            ((row.fineExterior + row.fineCore) +
              (row.coarseExterior + row.coarseCore))) *
        row.weight := by
  unfold fiberWeight
  rw [←
    finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow_eq_filter
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row]
  exact
    finePacketConnectedRateProfiledStructuralRowEnvelopeMass_le_profileMultiplicity
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow

#print axioms finePacketConnectedRateProfiledStructuralLoweringRowEnvelope_nonnegative
#print axioms finePacketConnectedRateProfiledStructuralLoweringRowEnvelope_eq_rowWeight_of_mem
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowWeight_nonnegative_of_mem
#print axioms finePacketConnectedRateProfiledStructuralRowEnvelopeMass_le_length_mul
#print axioms finePacketConnectedRateProfiledStructuralRowEnvelopeMass_le_profileMultiplicity
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowWeightedFiber
