import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux

namespace YMGap.Continuum.ScratchTaylorModeOne

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ringq" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

theorem factor_mode_one (k : Nat) :
    lowerSixQuadraticTaylorFactor k 1 ≈
      lowerSixWeightDriftFactor k 1 := by
  have hr := driftRatio_eqv_one_add_unitDen k
  unfold lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff
    lowerSixWeightDriftFactor lowerSixDriftExcess qpow
  simp only [Nat.mul_one]
  refine Q'.eqv_trans _
    (((1 : Q') + unit (driftDen k) (driftDen_pos k)) *
      ((1 : Q') + unit (driftDen k) (driftDen_pos k))) _ ?_ ?_
  · ringq
  · exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hr)
      (Q'.mul_eqv_congr_left _ _ _ hr))

theorem remainder_mode_zero (k : Nat) :
    lowerSixQuadraticTaylorAbelRemainder k 0 ≈ (0 : Q') := by
  unfold lowerSixQuadraticTaylorAbelRemainder
  have hz : lowerSixWeightDriftFactor k (0 + 1) +
      -lowerSixQuadraticTaylorFactor k (0 + 1) ≈ (0 : Q') := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (factor_mode_one k)))
      (Q'.add_neg_self_eqv _)
  refine Q'.eqv_trans _
    (Q'.ofNat (k + 3) * (0 : Q') * lowerSixAbelCarrier (k + 1) 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hz)
  · exact Q'.eqv_trans _ ((0 : Q') * lowerSixAbelCarrier (k + 1) 0) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
      (Q'.zero_mul_eqv _)

#print axioms factor_mode_one
#print axioms remainder_mode_zero

end YMGap.Continuum.ScratchTaylorModeOne
