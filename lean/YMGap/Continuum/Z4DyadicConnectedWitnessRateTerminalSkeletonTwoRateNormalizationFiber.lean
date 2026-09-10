/-
# Normalize the two-rate terminal history fiber

The spatial/history split leaves the complete row weight

  spatialRate^distance * (historyRate^profileMass * rowResidual).

The normalization compiler already forgets precisely the skeleton and profile
counters while retaining the physical endpoints, accepted terminal states,
distance, and residual.  This module applies exact finite Fubini to the new
weight and isolates the remaining history sum as

  sum normalizationCode,
    spatialRate^distance *
      (historyPowerFugacity historyRate code * residual).

Unlike the earlier surplus fugacity, the history exponent here is the full
profile mass.  It is therefore present even on rows whose profile mass is
exactly their physical distance.

Constructive contract: decidable finite fibers and rational distributivity
only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateSplit

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateNormalizationFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateSplit

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mul_right_local {A : Type}
    (weight : A → Q') (factor : Q') (items : List A) :
    listQSum (fun item => weight item * factor) items ≈
      listQSum weight items * factor := by
  have hcommute :
      listQSum (fun item => weight item * factor) items ≈
        listQSum (fun item => factor * weight item) items :=
    listQSum_congr (fun item => Q'.mul_comm_eqv _ _) _
  exact Q'.eqv_trans _ _ _ hcommute
    (Q'.eqv_trans _ _ _
      (listQSum_mul_left factor weight items)
      (Q'.mul_comm_eqv factor (listQSum weight items)))

/-! ## 1. Full-profile history fugacity -/

def finePacketConnectedRateTerminalSkeletonHistoryPowerWeight
    (historyRate : Q')
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  historyRate ^
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row

def finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (historyRate : Q')
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) : Q' :=
  fiberWeight
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketConnectedRateTerminalSkeletonHistoryPowerWeight historyRate)
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    code

def finePacketConnectedRateTerminalSkeletonTwoRateWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q')
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  spatialRate ^
      (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row) *
    (historyRate ^
        finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row *
      finePacketConnectedRateProfiledTerminalSkeletonRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row)

theorem finePacketConnectedRateTerminalSkeletonTwoRateFiber_eqv_normalizedHistory
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q')
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    fiberWeight
        (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketConnectedRateTerminalSkeletonTwoRateWeight
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace spatialRate historyRate)
        (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        code ≈
      spatialRate ^ code.distance *
        (finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace historyRate code *
          code.residual) := by
  let rows := finePacketConnectedRateProfiledTerminalSkeletonRowCodes
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let compiler := finePacketConnectedRateTerminalSkeletonNormalizationCompiler
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let history :=
    finePacketConnectedRateTerminalSkeletonHistoryPowerWeight historyRate
  let selected := rows.filter (fun row => decide (code = compiler row))
  have hagree :
      listQSum
          (finePacketConnectedRateTerminalSkeletonTwoRateWeight
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace spatialRate historyRate)
          selected ≈
        listQSum
          (fun row => spatialRate ^ code.distance *
            (history row * code.residual))
          selected := by
    apply listQSum_congr_on
    intro row hrow
    have hparts := List.mem_filter.mp hrow
    have hcode : code = compiler row := of_decide_eq_true hparts.2
    have hdistance := congrArg
      FinePacketConnectedRateTerminalSkeletonNormalizationCode.distance hcode
    have hresidual := congrArg
      FinePacketConnectedRateTerminalSkeletonNormalizationCode.residual hcode
    rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_distance]
      at hdistance
    rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_residual]
      at hresidual
    unfold finePacketConnectedRateTerminalSkeletonTwoRateWeight history
      finePacketConnectedRateTerminalSkeletonHistoryPowerWeight
    rw [← hdistance, ← hresidual]
    exact Q'.eqv_refl _
  have hleft := listQSum_mul_left
    (spatialRate ^ code.distance)
    (fun row => history row * code.residual) selected
  have hright := listQSum_mul_right_local history code.residual selected
  unfold fiberWeight
  change listQSum _ selected ≈ _
  refine Q'.eqv_trans _ _ _ hagree ?_
  refine Q'.eqv_trans _ _ _ hleft ?_
  exact Q'.mul_eqv_congr_left _ _ _ (by
    unfold finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
      fiberWeight
    simpa only [rows, compiler, history, selected] using hright)

/-! ## 2. Exact two-rate normalization Fubini -/

def finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q') : Q' :=
  listQSum
    (fun code =>
      spatialRate ^ code.distance *
        (finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace historyRate code *
          code.residual))
    (finePacketConnectedRateTerminalSkeletonNormalizationCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

theorem finePacketConnectedRateTerminalSkeletonTwoRateMass_eqv_normalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q') :
    finePacketConnectedRateTerminalSkeletonTwoRateMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate ≈
      finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate := by
  let rows := finePacketConnectedRateProfiledTerminalSkeletonRowCodes
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let weight := finePacketConnectedRateTerminalSkeletonTwoRateWeight
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace spatialRate historyRate
  let compiler := finePacketConnectedRateTerminalSkeletonNormalizationCompiler
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let codes := finePacketConnectedRateTerminalSkeletonNormalizationCodes
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  have hfubini := fiberWeight_total rows weight compiler codes
    (finePacketConnectedRateTerminalSkeletonNormalizationCodes_nodup
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (fun row hrow =>
      finePacketConnectedRateTerminalSkeletonNormalizationCompiler_mem
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row hrow)
  have hfibers :
      listQSum (fiberWeight rows weight compiler) codes ≈
        finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace spatialRate historyRate := by
    unfold finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass
    apply listQSum_congr_on
    intro code _hcode
    exact
      finePacketConnectedRateTerminalSkeletonTwoRateFiber_eqv_normalizedHistory
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate code
  refine Q'.eqv_trans _ (listQSum weight rows) _ ?_ ?_
  · unfold finePacketConnectedRateTerminalSkeletonTwoRateMass weight
      finePacketConnectedRateTerminalSkeletonTwoRateWeight
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hfubini) hfibers

/-! ## 3. Complete explicit-corridor bound in normalized form -/

theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsNormalizedHistoryMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrateAnchor : rate ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace (Q'.mkPos 4 5 (by decide))
            (Q'.mkPos 2 5 (by decide)) := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  have hmass :=
    finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsHistoryMass
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate
        hrateAnchor orientation observableFaceId hobservableFace
  have hnormalize :=
    finePacketConnectedRateTerminalSkeletonTwoRateMass_eqv_normalizationMass
      S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
        hobservableFace (Q'.mkPos 4 5 (by decide))
          (Q'.mkPos 2 5 (by decide))
  exact Q'.le_trans' _ _ _ hmass (Q'.le_of_eqv hnormalize)

#print axioms finePacketConnectedRateTerminalSkeletonHistoryPowerWeight
#print axioms finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateWeight
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateFiber_eqv_normalizedHistory
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateMass_eqv_normalizationMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsNormalizedHistoryMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateNormalizationFiber
