/-
Finite-prefix cubic-debt payment by the eighth Gaussian moment.

The factorial cubic coefficient is converted exactly into an eighth moment,
then the four-step summation-by-parts estimate and the large-scale quarter
window close the finite prefix.  The final statement is kept division-free.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentWindow

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentPayment

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentSummation
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem payment_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "payment_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               payment_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem lowerSixSquareCast_eqv_qpow_two (n : Nat) :
    Q'.ofNat (n * n) ≈ RingNormaliser.qpow (Q'.ofNat n) 2 := by
  refine Q'.eqv_trans _ (Q'.ofNat n * Q'.ofNat n) _
    (HeatKernelRGStep.ofNat_mul_eqv n n) ?_
  unfold RingNormaliser.qpow
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.one_mul_eqv (Q'.ofNat n)))

private theorem lowerSixSquareFourth_eqv_qpow_eight (n : Nat) :
    (((Q'.ofNat (n * n) * Q'.ofNat (n * n)) * Q'.ofNat (n * n)) *
        Q'.ofNat (n * n)) ≈ lowerSixQPower n 8 := by
  let M := Q'.ofNat (n * n)
  let N := Q'.ofNat n
  have hbase : M ≈ RingNormaliser.qpow N 2 := by
    dsimp only [M, N]
    exact lowerSixSquareCast_eqv_qpow_two n
  have hpow := RingNormaliser.qpow_eqv_congr hbase 4
  have hleft : ((M * M) * M) * M ≈ RingNormaliser.qpow M 4 := by
    unfold RingNormaliser.qpow
    exact Q'.mul_eqv_congr_right _ _ M
      (Q'.mul_eqv_congr_right _ _ M
        (Q'.mul_eqv_congr_right _ _ M
          (Q'.eqv_symm (Q'.one_mul_eqv M))))
  have hcompose :
      RingNormaliser.qpow (RingNormaliser.qpow N 2) 4 ≈
        RingNormaliser.qpow N 8 := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    payment_ring
  unfold lowerSixQPower
  dsimp only [M, N] at hleft hpow hcompose ⊢
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hpow hcompose)

private theorem six_cubicMomentCell_le_eighthMomentCell (k j : Nat) :
    Q'.ofNat 6 * lowerSixPrefixCubicMomentCell k j ≤
      lowerSixQPower (j + 1) 8 *
        lowerSixModeWeight (k + 1) (j + 1) := by
  let n := j + 1
  let m := n * n
  let C := Q'.ofNat (cubicCoeff m)
  let M := Q'.ofNat m
  let W := lowerSixModeWeight (k + 1) n
  have hnat := six_cubicCoeff_le_cube m
  have hcast : Q'.ofNat (6 * cubicCoeff m) ≤
      Q'.ofNat (m * m * m) := CReal.ofNat_le_ofNat hnat
  have hleftCast : Q'.ofNat (6 * cubicCoeff m) ≈ Q'.ofNat 6 * C := by
    dsimp only [C]
    exact HeatKernelRGStep.ofNat_mul_eqv 6 (cubicCoeff m)
  have hrightCast : Q'.ofNat (m * m * m) ≈ (M * M) * M := by
    dsimp only [M]
    refine Q'.eqv_trans _ (Q'.ofNat (m * m) * Q'.ofNat m) _
      (HeatKernelRGStep.ofNat_mul_eqv (m * m) m) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (HeatKernelRGStep.ofNat_mul_eqv m m)
  have hcoeff : Q'.ofNat 6 * C ≤ (M * M) * M :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleftCast)
      (Q'.le_trans' _ _ _ hcast (Q'.le_of_eqv hrightCast))
  have hM0 : (0 : Q') ≤ M := by
    dsimp only [M, m]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hW0 : (0 : Q') ≤ W := by
    dsimp only [W, n]
    exact lowerSixModeWeight_nonnegative _ _
  have hmulM := Q'.mul_le_mul_of_nonneg_right _ _ M hcoeff hM0
  have hmulW := Q'.mul_le_mul_of_nonneg_right _ _ W hmulM hW0
  have hcell :
      Q'.ofNat 6 * lowerSixPrefixCubicMomentCell k j ≈
        ((Q'.ofNat 6 * C) * M) * W := by
    unfold lowerSixPrefixCubicMomentCell
    dsimp only [n, m, C, M, W]
    payment_ring
  have hpow : ((M * M) * M) * M ≈ lowerSixQPower n 8 := by
    dsimp only [M, m, n]
    exact lowerSixSquareFourth_eqv_qpow_eight (j + 1)
  have hright : (((M * M) * M) * M) * W ≈
      lowerSixQPower n 8 * W :=
    Q'.mul_eqv_congr_right _ _ _ hpow
  dsimp only [n, W] at hright ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcell)
    (Q'.le_trans' _ _ _ hmulW (Q'.le_of_eqv hright))

/-- The complete factorial cubic prefix is at most one sixth of the eighth
Gaussian moment, in division-free form. -/
theorem six_prefixCubicMomentSum_le_eighthMoment (k : Nat) :
    Q'.ofNat 6 * lowerSixPrefixCubicMomentSum k ≤
      lowerSixNextGaussianMoment k 8 (thetaWindowRight k) := by
  let f : Nat → Q' := fun j =>
    Q'.ofNat 6 * lowerSixPrefixCubicMomentCell k j
  let g : Nat → Q' := fun j =>
    lowerSixQPower (j + 1) 8 *
      lowerSixModeWeight (k + 1) (j + 1)
  have hsum : finSum f (thetaWindowRight k) ≤
      finSum g (thetaWindowRight k) := by
    apply finSum_le_lt
    intro j hj
    dsimp only [f, g]
    exact six_cubicMomentCell_le_eighthMomentCell k j
  have hleft : Q'.ofNat 6 * lowerSixPrefixCubicMomentSum k ≈
      finSum f (thetaWindowRight k) := by
    unfold lowerSixPrefixCubicMomentSum
    dsimp only [f]
    exact const_mul_finSum _ _ _
  have hright : lowerSixNextGaussianMoment k 8 (thetaWindowRight k) =
      finSum g (thetaWindowRight k) := rfl
  rw [hright]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hsum

/-- Exact large-scale payment of the factorial cubic prefix by the zeroth
Gaussian moment.  `486 = 81·6` is the combined denominator-clearing factor. -/
theorem prefixCubicMoment_divisionFree_large
    {k : Nat} (hk : 8189 ≤ k) :
    Q'.ofNat 486 * lowerSixPrefixCubicMomentSum k ≤
      Q'.ofNat 105 *
        (lowerSixQPower (k + 3) 4 *
          lowerSixNextGaussianMoment k 0 (thetaWindowRight k)) := by
  have hcubic := six_prefixCubicMomentSum_le_eighthMoment k
  have h81 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 81) hcubic
    (HeatKernelRGStep.zero_le_ofNat 81)
  have hleft : Q'.ofNat 486 * lowerSixPrefixCubicMomentSum k ≈
      Q'.ofNat 81 *
        (Q'.ofNat 6 * lowerSixPrefixCubicMomentSum k) := by
    payment_ring
  have hm8 := lowerSixGaussianMoment_eight_divisionFree
    (show 5 ≤ k by omega) (lowerSixNextGaussianQuarterWindow_large hk)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h81 hm8)

private theorem lowerSixPrefixCubicDebtScalar_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixPrefixCubicDebtScalar k := by
  unfold lowerSixPrefixCubicDebtScalar
  have hD0 : (0 : Q') ≤ Q'.ofNat (k + 3) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hP0 : (0 : Q') ≤ lowerSixDirichletProfile (k + 1) :=
    lowerSixDirichletProfile_nonnegative_local _
  have he0 : (0 : Q') ≤ lowerSixDriftExcess k :=
    lowerSixDriftExcess_nonnegative k
  exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hD0 hP0)
    (Q'.mul_nonneg _ _ he0 (Q'.mul_nonneg _ _ he0 he0))

/-- The actual finite cubic debt, after its exact scalar factorization, is
paid by the zeroth next-scale Gaussian moment.  This is the production bridge
from the Taylor-prefix debt to the moment route. -/
theorem prefixCubicDebt_momentPaid_large
    {k : Nat} (hk : 8189 ≤ k) :
    Q'.ofNat 486 * prefixCubicDebtSum k ≤
      Q'.ofNat 105 *
        (lowerSixPrefixCubicDebtScalar k *
          (lowerSixQPower (k + 3) 4 *
            lowerSixNextGaussianMoment k 0 (thetaWindowRight k))) := by
  let S := lowerSixPrefixCubicDebtScalar k
  let C := lowerSixPrefixCubicMomentSum k
  let B := prefixCubicDebtSum k
  let R := lowerSixQPower (k + 3) 4 *
    lowerSixNextGaussianMoment k 0 (thetaWindowRight k)
  have hmoment := prefixCubicMoment_divisionFree_large hk
  change Q'.ofNat 486 * C ≤ Q'.ofNat 105 * R at hmoment
  have hS0 : (0 : Q') ≤ S := by
    dsimp only [S]
    exact lowerSixPrefixCubicDebtScalar_nonnegative k
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ S hmoment hS0
  have hfactor : B ≈ S * C := by
    dsimp only [B, S, C]
    exact prefixCubicDebtSum_eqv_scalar_moment k
  have hleft : Q'.ofNat 486 * B ≈ S * (Q'.ofNat 486 * C) := by
    refine Q'.eqv_trans _ (Q'.ofNat 486 * (S * C)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hfactor
    · payment_ring
  have hright : S * (Q'.ofNat 105 * R) ≈
      Q'.ofNat 105 * (S * R) := by payment_ring
  dsimp only [B, S, C, R] at hleft hright ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

#print axioms six_prefixCubicMomentSum_le_eighthMoment
#print axioms prefixCubicMoment_divisionFree_large
#print axioms prefixCubicDebt_momentPaid_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentPayment
