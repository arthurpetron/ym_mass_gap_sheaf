/-
# Split strict terminal-row contraction into spatial and history rates

The exact distance/surplus split reserves no history payment when a row has
minimal profile mass equal to its physical distance.  For summing all
canonical histories it is safer to factor the strict SU(2) row rate itself:

  8/25 = (4/5) * (2/5).

For `distance <= profileMass`, this gives

  (8/25)^profileMass
    <= (4/5)^distance * (2/5)^profileMass.

Thus every row, including a minimal one, retains a strict history fugacity.
The core theorem is parameterized by any nonnegative factorization
`8/25 ~= spatialRate * historyRate` with `spatialRate <= 1`; the displayed
`4/5, 2/5` choice is an exact constructive rational instance.

Constructive contract: exact rational factorization, power algebra, and the
proved physical-distance floor only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new
trusted principle.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateSplit

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
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem pow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : ∀ exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right left right (left ^ exponent) h)
        (Q'.mul_eqv_congr_left right _ _
          (pow_eqv_congr_local h exponent))

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
        _ ≈ left * (left ^ exponent * (right * right ^ exponent)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)
        _ ≈ (left * left ^ exponent) *
              (right * right ^ exponent) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Parameterized two-rate split -/

theorem finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_le_twoRateTerm
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q')
    (hfactor : Q'.mkPos 8 25 (by decide) ≈ spatialRate * historyRate)
    (hspatial0 : (0 : Q') ≤ spatialRate)
    (hspatial1 : spatialRate ≤ (1 : Q'))
    (hhistory0 : (0 : Q') ≤ historyRate)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    (Q'.mkPos 8 25 (by decide)) ^
          finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row *
        finePacketConnectedRateProfiledTerminalSkeletonRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row ≤
      spatialRate ^
          (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) *
        (historyRate ^
            finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row *
          finePacketConnectedRateProfiledTerminalSkeletonRowResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) := by
  let mass :=
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row
  let distance :=
    finePacketConnectedRateProfiledTerminalSkeletonRowDistance
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row
  let residual :=
    finePacketConnectedRateProfiledTerminalSkeletonRowResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row
  have hresidual : (0 : Q') ≤ residual :=
    finePacketConnectedRateProfiledTerminalSkeletonRowResidual_nonnegative
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row
  have htail : (0 : Q') ≤ historyRate ^ mass * residual :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg historyRate hhistory0 mass) hresidual
  have hdistance : distance ≤ mass := by
    exact
      finePacketConnectedRateProfiledTerminalSkeletonRowDistance_le_profileMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row hrow
  have hpower : spatialRate ^ mass ≤ spatialRate ^ distance :=
    YMGap.Continuum.HKConvGen.pow_base_antitone
      hspatial0 hspatial1 hdistance
  have hfactorized :
      (Q'.mkPos 8 25 (by decide)) ^ mass * residual ≈
        spatialRate ^ mass * (historyRate ^ mass * residual) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ residual
        (pow_eqv_congr_local hfactor mass)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ residual
        (mul_pow_eqv_local spatialRate historyRate mass)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactorized)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hpower htail)

def finePacketConnectedRateTerminalSkeletonTwoRateMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q') : Q' :=
  listQSum
    (fun row =>
      spatialRate ^
          (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) *
        (historyRate ^
            finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row *
          finePacketConnectedRateProfiledTerminalSkeletonRowResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row))
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

theorem finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_twoRateMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q')
    (hfactor : Q'.mkPos 8 25 (by decide) ≈ spatialRate * historyRate)
    (hspatial0 : (0 : Q') ≤ spatialRate)
    (hspatial1 : spatialRate ≤ (1 : Q'))
    (hhistory0 : (0 : Q') ≤ historyRate) :
    finePacketConnectedRateProfiledTerminalSkeletonContractedMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateTerminalSkeletonTwoRateMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonContractedMass
    finePacketConnectedRateTerminalSkeletonTwoRateMass
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass
  apply listQSum_le_termwise_local
  intro row hrow
  simpa only [
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass] using
      finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_le_twoRateTerm
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate hfactor hspatial0 hspatial1
            hhistory0 row hrow

/-! ## 2. Explicit `4/5` spatial and `2/5` history rates -/

theorem eightTwentyFifths_eqv_fourFifths_mul_twoFifths :
    Q'.mkPos 8 25 (by decide) ≈
      Q'.mkPos 4 5 (by decide) * Q'.mkPos 2 5 (by decide) := by
  decide

theorem finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_fourFifthsDistance_twoFifthsHistoryMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalSkeletonContractedMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateTerminalSkeletonTwoRateMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace (Q'.mkPos 4 5 (by decide))
            (Q'.mkPos 2 5 (by decide)) := by
  exact
    finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_twoRateMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace (Q'.mkPos 4 5 (by decide))
          (Q'.mkPos 2 5 (by decide))
          eightTwentyFifths_eqv_fourFifths_mul_twoFifths
          (by decide) (by decide) (by decide)

/-! ## 3. Complete connected-mass chain on the explicit corridor -/

theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsHistoryMass
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
      finePacketConnectedRateTerminalSkeletonTwoRateMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace (Q'.mkPos 4 5 (by decide))
            (Q'.mkPos 2 5 (by decide)) := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateProfiledTerminalCodeMass
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate hrateAnchor
        orientation observableFaceId hobservableFace)
    (Q'.le_trans' _ _ _
      (finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonContractedMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace)
      (finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_fourFifthsDistance_twoFifthsHistoryMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace))

#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_le_twoRateTerm
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateMass
#print axioms finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_twoRateMass
#print axioms eightTwentyFifths_eqv_fourFifths_mul_twoFifths
#print axioms finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_fourFifthsDistance_twoFifthsHistoryMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsHistoryMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateSplit
