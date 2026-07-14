/-
Explicit cubic debt for the signed Taylor prefix correction.

The exact-minus-quadratic factor is nonnegative, but it multiplies a signed
next-scale Abel carrier.  A universal lower bound on that carrier and the
cubic factor envelope convert every adverse cell into one nonnegative
Gaussian factorial-moment debt.  Summing gives a constructive lower bound
for the complete prefix correction with no sign assumption on its cells.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem debt_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "debt_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               debt_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

def cubicUpper (k n : Nat) : Q' :=
  Q'.ofNat (cubicCoeff (n * n)) *
      (lowerSixDriftExcess k *
        (lowerSixDriftExcess k * lowerSixDriftExcess k)) *
    lowerSixWeightDriftFactor k n

def carrierDebt (k j : Nat) : Q' :=
  lowerSixDirichletProfile (k + 1) *
    Q'.ofNat ((j + 1) * (j + 1))

def prefixCubicDebtCell (k j : Nat) : Q' :=
  lowerSixAbelWeight k j *
    ((Q'.ofNat (k + 3) * cubicUpper k (j + 1)) * carrierDebt k j)

def prefixCubicDebtSum (k : Nat) : Q' :=
  finSum (prefixCubicDebtCell k) (thetaWindowRight k)

theorem lowerSixDirichletProfile_nonnegative_local (k : Nat) :
    (0 : Q') ≤ lowerSixDirichletProfile k := by
  unfold lowerSixDirichletProfile
  exact Q'.mul_nonneg _ _ (harmU_nonneg k)
    (Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg _ _ (harmU_nonneg k) (harmU_nonneg k)))

theorem lowerSixModeCarrier_ge_negative_profile (k n : Nat) :
    -(lowerSixDirichletProfile k * Q'.ofNat (n * n)) ≤
      lowerSixModeCarrier k n := by
  let S := thetaRootSlope k n
  let B := lowerSixDirichletProfile k * Q'.ofNat (n * n)
  have hsquare : (0 : Q') ≤ S * S :=
    SumOfSquares.q_mul_self_nonneg S
  have hfour : (0 : Q') ≤ Q'.ofNat 4 * (S * S) :=
    Q'.mul_nonneg _ _ (by decide) hsquare
  have h := Q'.add_le_add_right 0 (Q'.ofNat 4 * (S * S)) (-B) hfour
  unfold lowerSixModeCarrier
  dsimp only [S, B] at h ⊢
  simpa only [Q'.zero_add'] using h

theorem lowerSixAbelCarrier_ge_negative_debt (k j : Nat) :
    -carrierDebt k j ≤ lowerSixAbelCarrier (k + 1) j := by
  cases j with
  | zero =>
      have hm := lowerSixModeCarrier_ge_negative_profile (k + 1) 1
      have hfour : lowerSixModeCarrier (k + 1) 1 ≤
          lowerSixModeCarrier (k + 1) 1 + Q'.ofNat 4 :=
        Q'.add_le_self_of_nonneg _ _ (by decide)
      unfold carrierDebt lowerSixAbelCarrier
      simpa only [Nat.zero_add, Nat.one_mul] using Q'.le_trans' _ _ _ hm hfour
  | succ j =>
      have hm := lowerSixModeCarrier_ge_negative_profile (k + 1) (j + 2)
      unfold carrierDebt lowerSixAbelCarrier
      have hbase : j + 1 + 1 = j + 2 := by omega
      have hidx : (j + 1 + 1) * (j + 1 + 1) = (j + 2) * (j + 2) := by
        rw [hbase]
      rw [hidx]
      exact hm

theorem cubicUpper_nonnegative (k n : Nat) :
    (0 : Q') ≤ cubicUpper k n := by
  unfold cubicUpper
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (Q'.mul_nonneg _ _ (lowerSixDriftExcess_nonnegative k)
        (Q'.mul_nonneg _ _ (lowerSixDriftExcess_nonnegative k)
          (lowerSixDriftExcess_nonnegative k))))
    (qpow_nonneg _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt (HarmonicWeightDriftFence.driftRatio_pos k))
        (Q'.le_of_lt (HarmonicWeightDriftFence.driftRatio_pos k))) _)

theorem carrierDebt_nonnegative (k j : Nat) :
    (0 : Q') ≤ carrierDebt k j := by
  unfold carrierDebt
  exact Q'.mul_nonneg _ _
    (lowerSixDirichletProfile_nonnegative_local (k + 1))
    (HeatKernelRGStep.zero_le_ofNat _)

theorem prefixCubicDebtCell_nonnegative (k j : Nat) :
    (0 : Q') ≤ prefixCubicDebtCell k j := by
  unfold prefixCubicDebtCell
  exact Q'.mul_nonneg _ _ (lowerSixModeWeight_nonnegative k (j + 1))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (cubicUpper_nonnegative k (j + 1)))
      (carrierDebt_nonnegative k j))

theorem prefixCubicDebtCell_pays_negative_remainder (k j : Nat) :
    -prefixCubicDebtCell k j ≤
      lowerSixAbelWeight k j * lowerSixQuadraticTaylorAbelRemainder k j := by
  let W := lowerSixAbelWeight k j
  let D := Q'.ofNat (k + 3)
  let r := lowerSixWeightDriftFactor k (j + 1) +
    -lowerSixQuadraticTaylorFactor k (j + 1)
  let U := cubicUpper k (j + 1)
  let B := carrierDebt k j
  let C := lowerSixAbelCarrier (k + 1) j
  let A := D * r
  have hW0 : (0 : Q') ≤ W := lowerSixModeWeight_nonnegative k (j + 1)
  have hD0 : (0 : Q') ≤ D := HeatKernelRGStep.zero_le_ofNat _
  have hr0 : (0 : Q') ≤ r :=
    lowerSixQuadraticTaylorFactorRemainder_nonnegative k (j + 1)
  have hrU : r ≤ U := by
    dsimp only [r, U]
    exact lowerSixQuadraticTaylorFactorRemainder_le_cubic_power k (j + 1)
  have hB0 : (0 : Q') ≤ B := carrierDebt_nonnegative k j
  have hC : -B ≤ C := lowerSixAbelCarrier_ge_negative_debt k j
  have hA0 : (0 : Q') ≤ A := Q'.mul_nonneg _ _ hD0 hr0
  have hAU : A ≤ D * U :=
    Q'.mul_le_mul_of_nonneg_left _ _ D hrU hD0
  have hAB : A * B ≤ (D * U) * B :=
    Q'.mul_le_mul_of_nonneg_right _ _ B hAU hB0
  have hnegAB : -((D * U) * B) ≤ -(A * B) := Q'.neg_le_neg hAB
  have hcarrier := Q'.mul_le_mul_of_nonneg_left _ _ A hC hA0
  have hAneg : A * (-B) ≈ -(A * B) := Q'.mul_neg_eqv A B
  have hinner : -((D * U) * B) ≤ A * C :=
    Q'.le_trans' _ _ _ hnegAB
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hAneg)) hcarrier)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ W hinner hW0
  have hleft : -prefixCubicDebtCell k j ≈ W * (-((D * U) * B)) := by
    unfold prefixCubicDebtCell
    dsimp only [W, D, U, B]
    exact Q'.eqv_symm (Q'.mul_neg_eqv _ _)
  have hright : W * (A * C) ≈
      lowerSixAbelWeight k j * lowerSixQuadraticTaylorAbelRemainder k j := by
    unfold lowerSixQuadraticTaylorAbelRemainder
    dsimp only [W, A, D, r, C]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))

theorem negative_prefixCubicDebtSum_le_remainder (k : Nat) :
    -prefixCubicDebtSum k ≤ lowerSixQuadraticTaylorPrefixRemainder k := by
  let f := prefixCubicDebtCell k
  let g := fun j => lowerSixAbelWeight k j *
    lowerSixQuadraticTaylorAbelRemainder k j
  have hsum := YMGap.Constructive.finSum_le_lt
    (fun j => -(f j)) g (thetaWindowRight k)
    (fun j _ => prefixCubicDebtCell_pays_negative_remainder k j)
  have hneg : -(finSum f (thetaWindowRight k)) ≈
      finSum (fun j => -(f j)) (thetaWindowRight k) :=
    YMGap.Constructive.neg_finSum f (thetaWindowRight k)
  unfold prefixCubicDebtSum lowerSixQuadraticTaylorPrefixRemainder
  dsimp only [f, g] at hsum hneg ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) hsum

#print axioms lowerSixModeCarrier_ge_negative_profile
#print axioms lowerSixAbelCarrier_ge_negative_debt
#print axioms prefixCubicDebtCell_nonnegative
#print axioms prefixCubicDebtCell_pays_negative_remainder
#print axioms negative_prefixCubicDebtSum_le_remainder

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt
