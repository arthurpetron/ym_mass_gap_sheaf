/-
Track 11.7-fusion / R3k -- normalized deficit tail interface.

# Result

The remaining coefficient sandwich is exactly a comparison of the normalized
Dirichlet deficits

    rho(w,N) = (coordNormSq(w,N) - adjCorr(w,N)) / coordNormSq(w,N).

This module proves the division-cancellation compiler once.  The physical
tail can therefore be attacked by scalar variation and dyadic subdivision
estimates without carrying four growing cross products through every lemma.
The exact checked prefix through `k=6` is retained, so the open normalized
tail starts at `k=7`.

# Constructivity

Positive rational division, exact cross multiplication, and the already
proved coefficient compiler only.  No `Classical`, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate

namespace YMGap.Continuum.P2BlockCompatibleThetaNormalizedDeficit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "ratio_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Normalized coefficient Dirichlet deficit.  The denominator is strictly
positive for every nonnegative heat weight. -/
def coefficientDeficitRatio (w : Q') (N : Nat) (hw : (0 : Q') <= w) : Q' :=
  Q'.divPos (coefficientDeficit w N) (coordNormSq w N)
    (coordNormSq_pos hw N)

/-- Generic scalar ratio form of one coefficient sandwich cell. -/
structure CoefficientRatioSandwichCell
    (coarseWeight fineWeight fourthWeight debt : Q')
    (coarseCut fineCut fourthCut : Nat) : Type where
  coarseWeightNonneg : (0 : Q') <= coarseWeight
  fineWeightNonneg : (0 : Q') <= fineWeight
  fourthWeightNonneg : (0 : Q') <= fourthWeight
  coarse :
    coefficientDeficitRatio fourthWeight fourthCut fourthWeightNonneg <=
      coefficientDeficitRatio coarseWeight coarseCut coarseWeightNonneg + debt
  fine :
    Q'.ofNat 2 *
          coefficientDeficitRatio fineWeight fineCut fineWeightNonneg + debt <=
      coefficientDeficitRatio fourthWeight fourthCut fourthWeightNonneg

/-- Positive division cancellation converts the two normalized scalar bounds
back to the exact cross-multiplied coefficient cell. -/
def CoefficientRatioSandwichCell.toCoefficientSandwichCell
    {coarseWeight fineWeight fourthWeight debt : Q'}
    {coarseCut fineCut fourthCut : Nat}
    (C : CoefficientRatioSandwichCell
      coarseWeight fineWeight fourthWeight debt
      coarseCut fineCut fourthCut) :
    CoefficientSandwichCell
      coarseWeight fineWeight fourthWeight debt
      coarseCut fineCut fourthCut := by
  let D0 := coordNormSq coarseWeight coarseCut
  let T0 := coefficientDeficit coarseWeight coarseCut
  let D1 := coordNormSq fineWeight fineCut
  let T1 := coefficientDeficit fineWeight fineCut
  let D4 := coordNormSq fourthWeight fourthCut
  let T4 := coefficientDeficit fourthWeight fourthCut
  let R0 := coefficientDeficitRatio coarseWeight coarseCut
    C.coarseWeightNonneg
  let R1 := coefficientDeficitRatio fineWeight fineCut C.fineWeightNonneg
  let R4 := coefficientDeficitRatio fourthWeight fourthCut
    C.fourthWeightNonneg
  have hD0 : (0 : Q') < D0 := by
    simpa only [D0] using coordNormSq_pos C.coarseWeightNonneg coarseCut
  have hD1 : (0 : Q') < D1 := by
    simpa only [D1] using coordNormSq_pos C.fineWeightNonneg fineCut
  have hD4 : (0 : Q') < D4 := by
    simpa only [D4] using coordNormSq_pos C.fourthWeightNonneg fourthCut
  have hR0 : R0 * D0 ≈ T0 := by
    simpa only [R0, D0, T0, coefficientDeficitRatio] using
      Q'.divPos_mul_eqv (coefficientDeficit coarseWeight coarseCut)
        (coordNormSq coarseWeight coarseCut)
        (coordNormSq_pos C.coarseWeightNonneg coarseCut)
  have hR1 : R1 * D1 ≈ T1 := by
    simpa only [R1, D1, T1, coefficientDeficitRatio] using
      Q'.divPos_mul_eqv (coefficientDeficit fineWeight fineCut)
        (coordNormSq fineWeight fineCut)
        (coordNormSq_pos C.fineWeightNonneg fineCut)
  have hR4 : R4 * D4 ≈ T4 := by
    simpa only [R4, D4, T4, coefficientDeficitRatio] using
      Q'.divPos_mul_eqv (coefficientDeficit fourthWeight fourthCut)
        (coordNormSq fourthWeight fourthCut)
        (coordNormSq_pos C.fourthWeightNonneg fourthCut)
  have hscale0 : (0 : Q') <= D0 * D4 :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hD0) (Q'.le_of_lt hD4)
  have hscale1 : (0 : Q') <= D1 * D4 :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hD1) (Q'.le_of_lt hD4)
  refine ⟨?_, ?_⟩
  · have hnormalized : R4 <= R0 + debt := by
      simpa only [R0, R4] using C.coarse
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (D0 * D4)
      hnormalized hscale0
    have hleft : (D0 * D4) * R4 ≈ D0 * T4 := by
      refine Q'.eqv_trans _ (D0 * (R4 * D4)) _ ?_ ?_
      · ratio_ring
      · exact Q'.mul_eqv_congr_left D0 _ _ hR4
    have hright : (D0 * D4) * (R0 + debt) ≈
        T0 * D4 + debt * (D0 * D4) := by
      refine Q'.eqv_trans _
        ((R0 * D0) * D4 + debt * (D0 * D4)) _ ?_ ?_
      · ratio_ring
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ D4 hR0) (Q'.eqv_refl _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  · have hnormalized : Q'.ofNat 2 * R1 + debt <= R4 := by
      simpa only [R1, R4] using C.fine
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (D1 * D4)
      hnormalized hscale1
    have hleft : (D1 * D4) * (Q'.ofNat 2 * R1 + debt) ≈
        Q'.ofNat 2 * (D4 * T1) + debt * (D1 * D4) := by
      refine Q'.eqv_trans _
        (Q'.ofNat 2 * (D4 * (R1 * D1)) + debt * (D1 * D4)) _ ?_ ?_
      · ratio_ring
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
            (Q'.mul_eqv_congr_left D4 _ _ hR1))
          (Q'.eqv_refl _)
    have hright : (D1 * D4) * R4 ≈ D1 * T4 := by
      refine Q'.eqv_trans _ (D1 * (R4 * D4)) _ ?_ ?_
      · ratio_ring
      · exact Q'.mul_eqv_congr_left D1 _ _ hR4
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- Honest normalized analytic tail after the three checked cells. -/
structure BlockCompatibleP2NormalizedDeficitTailFromSeven : Type where
  coarse : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    coefficientDeficitRatio w4 (blockNcut k)
        (qpow_nonneg _ (blockWeight_nonneg (k + 1)) 4) <=
      coefficientDeficitRatio (blockWeight k) (blockNcut k)
          (blockWeight_nonneg k) + blockParityDebt k
  fine : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    Q'.ofNat 2 *
          coefficientDeficitRatio (blockWeight (k + 1)) (blockNcut (k + 1))
            (blockWeight_nonneg (k + 1)) + blockParityDebt k <=
      coefficientDeficitRatio w4 (blockNcut k)
        (qpow_nonneg _ (blockWeight_nonneg (k + 1)) 4)

/-- The normalized tail is sufficient for the existing checked-prefix
coefficient compiler. -/
def BlockCompatibleP2NormalizedDeficitTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2NormalizedDeficitTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven where
  cell := fun k hk =>
    ({
      coarseWeightNonneg := blockWeight_nonneg k
      fineWeightNonneg := blockWeight_nonneg (k + 1)
      fourthWeightNonneg := qpow_nonneg _ (blockWeight_nonneg (k + 1)) 4
      coarse := T.coarse k hk
      fine := T.fine k hk
    } : CoefficientRatioSandwichCell
      (blockWeight k) (blockWeight (k + 1))
      (qpow (blockWeight (k + 1)) 4) (blockParityDebt k)
      (blockNcut k) (blockNcut (k + 1)) (blockNcut k))
      |>.toCoefficientSandwichCell

#print axioms CoefficientRatioSandwichCell.toCoefficientSandwichCell
#print axioms BlockCompatibleP2NormalizedDeficitTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaNormalizedDeficit
