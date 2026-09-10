/-
# Contract adaptive row entropy against the SU(2) anchor coefficient

The terminal-skeleton row estimate pays one adaptive entropy factor for every
unit of fine/coarse profile mass.  The exact terminal weight pays one
`anchorFaceCoefficient` at the same exponent.  This module exposes the
remaining normalized lowering-row residual and contracts the two powers:

  10240000^M * (1/32000000)^M = (8/25)^M.

The result is still a finite, source-dependent statement.  No thermodynamic,
continuum, or completed-Hilbert-space claim is made here.

Constructive contract: exact rational finite sums and explicit finite search
only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowWeightedFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowAdaptiveAnchor

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralLoweringCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowWeightedFiber
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_pow_eqv_local (base : Nat) : ∀ exponent : Nat,
    Q'.ofNat (base ^ exponent) ≈ (Q'.ofNat base) ^ exponent
  | 0 => by
      rfl
  | exponent + 1 => by
      rw [Nat.pow_succ, Nat.mul_comm]
      show Q'.ofNat (base * base ^ exponent) ≈
        Q'.ofNat base * (Q'.ofNat base) ^ exponent
      exact Q'.eqv_trans _ _ _
        (ofNat_mul_eqv base (base ^ exponent))
        (Q'.mul_eqv_congr_left (Q'.ofNat base) _ _
          (ofNat_pow_eqv_local base exponent))

private theorem mul_pow_eqv_local (left right : Q') : ∀ exponent : Nat,
    (left * right) ^ exponent ≈ left ^ exponent * right ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have hinductive := mul_pow_eqv_local left right exponent
      show
        (left * right) * (left * right) ^ exponent ≈
          (left * left ^ exponent) * (right * right ^ exponent)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left * right) _ _ hinductive) ?_
      calc
        (left * right) * (left ^ exponent * right ^ exponent) ≈
            left * (right * (left ^ exponent * right ^ exponent)) :=
          Q'.mul_assoc_eqv _ _ _
        _ ≈ left * ((right * left ^ exponent) * right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        _ ≈ left * ((left ^ exponent * right) * right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        _ ≈ left *
              (left ^ exponent * (right * right ^ exponent)) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_assoc_eqv _ _ _)
        _ ≈ (left * left ^ exponent) *
              (right * right ^ exponent) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem pow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : ∀ exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right left right (left ^ exponent) h)
        (Q'.mul_eqv_congr_left right _ _
          (pow_eqv_congr_local h exponent))

/-! ## 1. Exact arithmetic contraction -/

theorem componentAdaptiveMultiplicityAnchorPower_eqv
    (mass : Nat) (residual : Q') :
    Q'.ofNat (componentAdaptiveEntropyBase ^ mass) *
        (anchorFaceCoefficient ^ mass * residual) ≈
      componentAdaptiveEntropyAnchorRatio ^ mass * residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (ofNat_pow_eqv_local componentAdaptiveEntropyBase mass)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ residual
    (Q'.eqv_symm
      (mul_pow_eqv_local
        (Q'.ofNat componentAdaptiveEntropyBase)
        anchorFaceCoefficient mass))

theorem componentAdaptiveMultiplicityAnchorPower_eqv_eightTwentyFifths
    (mass : Nat) (residual : Q') :
    Q'.ofNat (componentAdaptiveEntropyBase ^ mass) *
        (anchorFaceCoefficient ^ mass * residual) ≈
      (Q'.mkPos 8 25 (by decide)) ^ mass * residual := by
  exact Q'.eqv_trans _ _ _
    (componentAdaptiveMultiplicityAnchorPower_eqv mass residual)
    (Q'.mul_eqv_congr_right _ _ residual
      (pow_eqv_congr_local componentAdaptiveEntropyAnchorRatio_eqv mass))

/-! ## 2. The exact normalized residual of one lowering row -/

/-- Remove only the common anchor power from the constant terminal weight on
one physical lowering row. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidualWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (_lowering : FinePacketConnectedRateProfiledLoweringCode) : Q' :=
  finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
    S hfineCutoff hcoarseCoupling rate hrate0
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
        S rate hrate0 orientation observableFaceId hobservableFace reference)

/-- The source-dependent residual row sum left after extracting the common
anchor power. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidualWeight
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace reference)
    (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
      S orientation observableFaceId reference)

theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRow_eqv_anchor_mul_residual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    listQSum
        (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace reference)
        (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
          S orientation observableFaceId reference) ≈
      anchorFaceCoefficient ^
          finePacketConnectedFourEntryRateProfiledCompilerCodeMass
            (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
              S rate hrate0 orientation observableFaceId hobservableFace reference) *
        finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace reference := by
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
    finePacketConnectedRateProfiledTerminalCodeWeight
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidualWeight
  exact listQSum_mul_left _ _ _

/-! ## 3. A realized terminal/skeleton row receives the strict `8/25` power -/

theorem finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le_eightTwentyFifths_mul_residual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hreference :
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
        S rate hrate0 orientation observableFaceId hobservableFace structural =
          some reference)
    (hreferenceStructural : structural =
      finePacketConnectedRateProfiledStructuralCompiler
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace reference)) :
    fiberWeight
        (finePacketConnectedRateProfiledStructuralCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        row ≤
      (Q'.mkPos 8 25 (by decide)) ^
          ((row.fineExterior + row.fineCore) +
            (row.coarseExterior + row.coarseCore)) *
        finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace reference := by
  let mass := (row.fineExterior + row.fineCore) +
    (row.coarseExterior + row.coarseCore)
  have hweighted :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hrowWeight :=
    finePacketConnectedRateProfiledStructuralLoweringRowEnvelope_eq_rowWeight_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  have hcompiledRow :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  have hfineExterior := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineExterior
      hcompiledRow
  have hfineCore := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineCore hcompiledRow
  have hcoarseExterior := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseExterior
      hcompiledRow
  have hcoarseCore := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseCore hcompiledRow
  have hfineExterior' : structural.fineProfile.2.2.1 = row.fineExterior := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineExterior]
      using hfineExterior
  have hfineCore' : structural.fineProfile.2.2.2 = row.fineCore := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineCore]
      using hfineCore
  have hcoarseExterior' : structural.coarseProfile.2.2.1 =
      row.coarseExterior := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseExterior]
      using hcoarseExterior
  have hcoarseCore' : structural.coarseProfile.2.2.2 = row.coarseCore := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseCore]
      using hcoarseCore
  have hmassStructural :
      finePacketConnectedFourEntryRateProfiledCompilerCodeMass
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
            S rate hrate0 orientation observableFaceId hobservableFace reference) =
        (structural.fineProfile.2.2.1 + structural.fineProfile.2.2.2) +
          (structural.coarseProfile.2.2.1 +
            structural.coarseProfile.2.2.2) := by
    rw [hreferenceStructural]
    rfl
  have hmass :
      finePacketConnectedFourEntryRateProfiledCompilerCodeMass
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
            S rate hrate0 orientation observableFaceId hobservableFace reference) =
        mass := by
    rw [hmassStructural, hfineExterior', hfineCore', hcoarseExterior',
      hcoarseCore']
  have hfactor :=
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRow_eqv_anchor_mul_residual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace reference
  unfold finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
    at hrowWeight
  rw [hreference] at hrowWeight
  have hrowFactor : row.weight ≈
      anchorFaceCoefficient ^ mass *
        finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace reference := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq hrowWeight.symm)
      (by simpa only [hmass] using hfactor)
  have hcontracted :
      Q'.ofNat (componentAdaptiveEntropyBase ^ mass) * row.weight ≈
        (Q'.mkPos 8 25 (by decide)) ^ mass *
          finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
              hobservableFace reference := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hrowFactor)
      (componentAdaptiveMultiplicityAnchorPower_eqv_eightTwentyFifths mass _)
  change _ ≤ Q'.ofNat (componentAdaptiveEntropyBase ^ mass) * row.weight at hweighted
  change _ ≤ (Q'.mkPos 8 25 (by decide)) ^ mass * _
  exact Q'.le_trans' _ _ _ hweighted (Q'.le_of_eqv hcontracted)

#print axioms componentAdaptiveMultiplicityAnchorPower_eqv
#print axioms componentAdaptiveMultiplicityAnchorPower_eqv_eightTwentyFifths
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidualWeight
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRow_eqv_anchor_mul_residual
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le_eightTwentyFifths_mul_residual

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowAdaptiveAnchor
