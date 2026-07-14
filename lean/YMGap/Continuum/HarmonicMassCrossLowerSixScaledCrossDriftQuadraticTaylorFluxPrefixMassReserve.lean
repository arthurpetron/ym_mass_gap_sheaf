/-
Mass-reserve regrouping for the two summed Taylor-flux residuals.

Paying four copies of the signed Hermite remainder consumes at most one copy
of the positive mass.  After scaling the complete cleared expression by four,
three mass copies remain.  This file makes that reserve exact and spends it
on the upper flux together with the explicit cubic Taylor debt.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserve

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope

local infix:50 " ≈ " => Q'.eqv

private theorem reserve_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "reserve_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               reserve_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The reserve left after the tapered head pays four copies of the signed
Hermite remainder: three full copies of the positive mass remain available
for the upper flux and cubic Taylor debt. -/
def lowerSixUpperMassReserveBlock (k : Nat) : Q' :=
  Q'.ofNat 4 * lowerSixUpperFluxPrefixBlock k +
    Q'.ofNat 3 * lowerSixHermiteMassSum k

/-- Fully explicit sufficient residual after replacing the signed prefix
correction by its nonnegative cubic debt. -/
def lowerSixCubicDebtMassReserveResidual (k : Nat) : Q' :=
  (Q'.ofNat 4 *
        lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1) +
      Q'.ofNat 3 * lowerSixHermiteMassSum k) +
    -(Q'.ofNat 4 * lowerSixQuadraticTaylorClearingScale k *
      prefixCubicDebtSum k)

private abbrev PE := RingNormaliser.PolyExpr

private def pFourBlocksL : PE :=
  .mul (.const 4)
    (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))

private def pFourBlocksR : PE :=
  .add
    (.add (.mul (.const 4) (.var 0))
      (.add (.mul (.const 4) (.var 1)) (.mul (.const 3) (.var 2))))
    (.add (.var 2) (.mul (.const 4) (.var 3)))

private theorem pFourBlocks_normal :
    RingNormaliser.normalize pFourBlocksL =
      RingNormaliser.normalize pFourBlocksR := by decide

private theorem four_blocks_algebra (E U M R : Q') :
    Q'.ofNat 4 * (E + U + (M + R)) ≈
      (Q'.ofNat 4 * E +
        (Q'.ofNat 4 * U + Q'.ofNat 3 * M)) +
      (M + Q'.ofNat 4 * R) := by
  simpa [pFourBlocksL, pFourBlocksR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFourBlocksL pFourBlocksR pFourBlocks_normal
      (fun | 0 => E | 1 => U | 2 => M | _ => R))

private theorem upper_reserve_algebra (F C M B : Q') :
    (Q'.ofNat 4 * F + Q'.ofNat 3 * M) +
        -(Q'.ofNat 4 * C * B) ≈
      Q'.ofNat 4 * (F + C * (-B)) + Q'.ofNat 3 * M := by
  reserve_ring

theorem lowerSixUpperMassReserveBlock_nonnegative_of_cubicDebt
    (k : Nat)
    (hresidual : (0 : Q') ≤ lowerSixCubicDebtMassReserveResidual k) :
    (0 : Q') ≤ lowerSixUpperMassReserveBlock k := by
  let F := lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)
  let C := lowerSixQuadraticTaylorClearingScale k
  let P := lowerSixQuadraticTaylorPrefixRemainder k
  let B := prefixCubicDebtSum k
  let M := lowerSixHermiteMassSum k
  have hP : -B ≤ P := negative_prefixCubicDebtSum_le_remainder k
  have hC0 : (0 : Q') ≤ C :=
    Q'.le_of_lt (lowerSixQuadraticTaylorClearingScale_pos k)
  have hCP := Q'.mul_le_mul_of_nonneg_left _ _ C hP hC0
  have hFC := Q'.add_le_add_left F _ _ hCP
  have h4 : (0 : Q') ≤ Q'.ofNat 4 := by decide
  have h4mul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hFC h4
  have hplusM := Q'.add_le_add_right _ _ (Q'.ofNat 3 * M) h4mul
  have hleft : lowerSixCubicDebtMassReserveResidual k ≈
      Q'.ofNat 4 * (F + C * (-B)) + Q'.ofNat 3 * M := by
    unfold lowerSixCubicDebtMassReserveResidual
    dsimp only [F, C, B, M]
    exact upper_reserve_algebra _ _ _ _
  have hright :
      Q'.ofNat 4 * (F + C * P) + Q'.ofNat 3 * M ≈
        lowerSixUpperMassReserveBlock k := by
    unfold lowerSixUpperMassReserveBlock lowerSixUpperFluxPrefixBlock
    dsimp only [F, C, P, M]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ hresidual (Q'.le_of_eqv hleft))
    (Q'.le_trans' _ _ _ hplusM (Q'.le_of_eqv hright))

theorem lowerSixClearedFluxExpression_nonnegative_of_mass_reserve
    {k : Nat} (hk : 247 ≤ k)
    (hremainder :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k)
    (hupper : (0 : Q') ≤ lowerSixUpperMassReserveBlock k) :
    (0 : Q') ≤ lowerSixQuadraticTaylorClearedFluxExpression k := by
  let E := lowerSixQuadraticTaylorClearingScale k *
      lowerSixQuadraticTaylorEndpointAugmentation k +
    -lowerSixDiscreteHermiteFluxNumerator k 1
  let U := lowerSixUpperFluxPrefixBlock k
  let M := lowerSixHermiteMassSum k
  let R := lowerSixHermiteRemainderSum k
  let H := lowerSixHermiteLinearHeadMassFloor k
  have hend : (0 : Q') ≤ E := by
    dsimp only [E]
    exact lowerSixEndpoint_add_lowerFlux_nonnegative hk
  have hHM : H ≤ M :=
    lowerSixHermiteLinearHeadMassFloor_le_mass (by omega)
  have hH4R : (0 : Q') ≤ H + Q'.ofNat 4 * R := by
    have hsub : (0 : Q') ≤ H + -(-(Q'.ofNat 4 * R)) :=
      Q'.sub_nonneg_of_le hremainder
    exact Q'.le_trans' _ _ _ hsub
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_left H _ _ (Q'.neg_neg_eqv _)))
  have hM4R : (0 : Q') ≤ M + Q'.ofNat 4 * R :=
    Q'.le_trans' _ _ _ hH4R
      (Q'.add_le_add_right H M (Q'.ofNat 4 * R) hHM)
  have h4E : (0 : Q') ≤ Q'.ofNat 4 * E :=
    Q'.mul_nonneg _ _ (by decide) hend
  have hsum : (0 : Q') ≤
      (Q'.ofNat 4 * E +
        (Q'.ofNat 4 * U + Q'.ofNat 3 * M)) +
      (M + Q'.ofNat 4 * R) :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ h4E hupper) hM4R
  have hfour : Q'.ofNat 4 *
      lowerSixQuadraticTaylorClearedFluxExpression k ≈
      (Q'.ofNat 4 * E +
        (Q'.ofNat 4 * U + Q'.ofNat 3 * M)) +
      (M + Q'.ofNat 4 * R) := by
    refine Q'.eqv_trans _
      (Q'.ofNat 4 * (E + U + (M + R))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (lowerSixClearedFluxExpression_eqv_three_blocks k)
    · exact four_blocks_algebra E U M R
  have hscaled : (0 : Q') ≤ Q'.ofNat 4 *
      lowerSixQuadraticTaylorClearedFluxExpression k :=
    Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hfour))
  have hzero : Q'.ofNat 4 * (0 : Q') ≤ Q'.ofNat 4 *
      lowerSixQuadraticTaylorClearedFluxExpression k :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 4))) hscaled
  exact Q'.le_of_mul_le_mul_left hzero (by decide)

theorem lowerSixQuadraticPayment_of_cubicDebt_mass_reserve
    {k : Nat} (hk : 247 ≤ k)
    (hremainder :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k)
    (hresidual : (0 : Q') ≤ lowerSixCubicDebtMassReserveResidual k) :
    -YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep.lowerSixScaledLinearCrossPaymentResidual k ≤
      YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment.lowerSixScaledQuadraticCrossWindowSuffix k := by
  exact lowerSixQuadraticPayment_of_clearedFluxExpression_nonnegative
    (show 48 ≤ k by omega)
    (lowerSixClearedFluxExpression_nonnegative_of_mass_reserve hk hremainder
      (lowerSixUpperMassReserveBlock_nonnegative_of_cubicDebt k hresidual))

#print axioms lowerSixUpperMassReserveBlock_nonnegative_of_cubicDebt
#print axioms lowerSixClearedFluxExpression_nonnegative_of_mass_reserve
#print axioms lowerSixQuadraticPayment_of_cubicDebt_mass_reserve

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserve
