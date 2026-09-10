/-
# Split terminal-row contraction into distance and entropy surplus

The spatial weakening to `(8/25)^distance` is useful as a final estimate, but
it spends the profile power that must still sum the remaining canonical
peeling histories.  This module retains that resource exactly.  For every
realized terminal/skeleton row, the proved distance floor gives

  profileMass = distance + (profileMass - distance),

and hence the strict row factor splits as

  (8/25)^profileMass
    = (8/25)^distance * (8/25)^(profileMass - distance).

The second factor is the explicit entropy surplus for the next Gibbs/history
normalization.  All strong-coupling hypotheses remain visible in the final
expanded-witness theorem.

Constructive contract: natural subtraction under a proved order witness and
exact rational power factorization only; no classical choice, proof hole,
trusted external computation, computability escape, heartbeat increase, or
new trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceContraction

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact profile and surplus exponents -/

def finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Nat :=
  (row.fineExterior + row.fineCore) +
    (row.coarseExterior + row.coarseCore)

def finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Nat :=
  finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row -
    finePacketConnectedRateProfiledTerminalSkeletonRowDistance
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row

theorem finePacketConnectedRateProfiledTerminalSkeletonRowDistance_add_profileSurplus_eq_profileMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    finePacketConnectedRateProfiledTerminalSkeletonRowDistance
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row +
        finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row =
      finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
  exact Nat.add_sub_of_le
    (finePacketConnectedRateProfiledTerminalSkeletonRowDistance_le_profileMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow)

/-! ## 2. Exact termwise distance/surplus factorization -/

theorem finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_eqv_distanceSurplusTerm
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    (Q'.mkPos 8 25 (by decide)) ^
          finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row *
        finePacketConnectedRateProfiledTerminalSkeletonRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row ≈
      (Q'.mkPos 8 25 (by decide)) ^
          (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) *
        ((Q'.mkPos 8 25 (by decide)) ^
            (finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
              S hfineCutoff hcoarseCoupling rate hrate0 orientation
                observableFaceId hobservableFace row) *
          finePacketConnectedRateProfiledTerminalSkeletonRowResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) := by
  have hsum :=
    finePacketConnectedRateProfiledTerminalSkeletonRowDistance_add_profileSurplus_eq_profileMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  rw [← hsum]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.pow_add_eqv (Q'.mkPos 8 25 (by decide)) _ _))
    (Q'.mul_assoc_eqv _ _ _)

/-- The residual still available after reserving the physical distance
factor.  Its exponent is nonnegative by construction and measures precisely
the profile mass not forced by separation. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowSpatialResidual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  (Q'.mkPos 8 25 (by decide)) ^
      (finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row) *
    finePacketConnectedRateProfiledTerminalSkeletonRowResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row

/-- Exact distance-reserved form of the complete contracted row mass. -/
def finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (fun row =>
      (Q'.mkPos 8 25 (by decide)) ^
          (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) *
        finePacketConnectedRateProfiledTerminalSkeletonRowSpatialResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row)
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

theorem finePacketConnectedRateProfiledTerminalSkeletonContractedMass_eqv_distanceSurplusMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalSkeletonContractedMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≈
      finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonContractedMass
    finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
    finePacketConnectedRateProfiledTerminalSkeletonRowSpatialResidual
  apply listQSum_congr_on
  intro row hrow
  simpa only [
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass] using
    finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_eqv_distanceSurplusTerm
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow

/-! ## 3. Complete strong-coupling chain with the surplus retained -/

theorem finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonDistanceSurplusMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  exact Q'.le_trans' _ _ _
    (finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonContractedMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (Q'.le_of_eqv
      (finePacketConnectedRateProfiledTerminalSkeletonContractedMass_eqv_distanceSurplusMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace))

/-- The connected expanded-witness mass reaches the exact distance/surplus
row sum on the explicitly named SU(2) strong-coupling corridor. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateTerminalSkeletonDistanceSurplusMass
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
      finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateProfiledTerminalCodeMass
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate hrateAnchor
        orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonDistanceSurplusMass
      S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
        hobservableFace)

#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowDistance_add_profileSurplus_eq_profileMass
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_eqv_distanceSurplusTerm
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowSpatialResidual
#print axioms finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
#print axioms finePacketConnectedRateProfiledTerminalSkeletonContractedMass_eqv_distanceSurplusMass
#print axioms finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonDistanceSurplusMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateTerminalSkeletonDistanceSurplusMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
