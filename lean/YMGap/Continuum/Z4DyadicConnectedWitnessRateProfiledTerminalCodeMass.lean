/-
# Retain the complete profile payment on terminal compiler codes

The spatial residual bound weakens the complete profile exponent to the
observable separation.  That is useful only after the remaining compiler
coordinates have been summed: the surplus profile power is the resource that
must pay their entropy.

This file therefore keeps the exact exponent on the faithful,
normalization-visible terminal code.  The source-side anchor-profile terminal
budget is exactly reindexed as a finite code sum

  anchorFaceCoefficient ^ code.profileMass * code.terminalResidual.

Consequently the connected expanded-witness mass is bounded by that code sum
on the explicitly named SU(2) strong-coupling corridor.  No terminal-code
count or posterior fraction is bounded here.

Constructive contract: compiler projection equalities, exact rational
congruence, and finite map reindexing only; no classical choice, proof hole,
trusted external computation, computability escape, heartbeat increase, or
new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfileCorridor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The profile-weighted terminal code -/

def finePacketConnectedRateProfiledTerminalCodeWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) : Q' :=
  anchorFaceCoefficient ^
      finePacketConnectedFourEntryRateProfiledCompilerCodeMass code *
    finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
      S hfineCutoff hcoarseCoupling rate hrate0 code

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget_eqv_compilerCodeWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded ≈
      finePacketConnectedRateProfiledTerminalCodeWeight
        S hfineCutoff hcoarseCoupling rate hrate0
        (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
          S rate hrate0 orientation observableFaceId hobservableFace expanded) := by
  have hsource :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget_eqv_power_mul_residual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded
  have hcode :
      finePacketConnectedRateProfiledTerminalCodeWeight
          S hfineCutoff hcoarseCoupling rate hrate0
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace expanded) ≈
        anchorFaceCoefficient ^
            finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
              S rate hrate0 orientation observableFaceId hobservableFace expanded *
          finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
              hobservableFace expanded := by
    unfold finePacketConnectedRateProfiledTerminalCodeWeight
    rw [finePacketConnectedFourEntryRateProfiledCompilerCodeMass_compiler]
    exact Q'.mul_eqv_congr_left _ _ _
      (finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual_compiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded)
  exact Q'.eqv_trans _ _ _ hsource (Q'.eqv_symm hcode)

/-! ## 2. Exact code reindexing and the connected-mass bound -/

def finePacketConnectedRateProfiledTerminalCodeMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketConnectedRateProfiledTerminalCodeWeight
      S hfineCutoff hcoarseCoupling rate hrate0)
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass_eqv_compilerCodeMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≈
      finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass
    finePacketConnectedRateProfiledTerminalCodeMass
    finePacketConnectedRateProfiledNormalizedTerminalCodes
  rw [listQSum_map]
  apply listQSum_congr
  intro expanded
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget_eqv_compilerCodeWeight
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded

/-- The complete connected expanded-witness mass is bounded by the faithful
profile-weighted terminal-code sum.  All coupling hypotheses remain explicit;
no beta-, cutoff-, volume-, or spacing-uniformity is claimed. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateProfiledTerminalCodeMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedAnchorProfileTerminalBudgetMass
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate hrateAnchor
        orientation observableFaceId hobservableFace)
    (Q'.le_of_eqv
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass_eqv_compilerCodeMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace))

#print axioms finePacketConnectedRateProfiledTerminalCodeWeight
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget_eqv_compilerCodeWeight
#print axioms finePacketConnectedRateProfiledTerminalCodeMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass_eqv_compilerCodeMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateProfiledTerminalCodeMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
