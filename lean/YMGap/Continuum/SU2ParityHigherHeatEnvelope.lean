/-
# Two explicit activities for the sharp SU(2) heat weight

For 0<=w<=1, (j+1)^2*w^c4(j) is bounded by
(4*w^3)^(j%2) * (9*w^8)^(j/2). Both parameters are explicit.
The higher-label tail at fixed parity has its actual geometric factor
1/(1-9*w^8), rather than a cutoff-dependent or opaque constant.
No spatial-state enumeration or signed-remainder smallness is asserted.
-/

import YMGap.Continuum.SU2ParityHigherArithmetic
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.SU2ParityHigherHeatEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2ParityHigherArithmetic

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

def oddRate (w : Q') : Q' := 4*qpow w 3
def higherRate (w : Q') : Q' := 9*qpow w 8
def heatWeight (w : Q') (spin : Nat) : Q' := (dimQ spin*dimQ spin)*qpow w (c4 spin)

theorem oddRate_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) : (0 : Q') ≤ oddRate w :=
  Q'.mul_nonneg _ _ (by decide) (qpow_nonneg w hw 3)

theorem higherRate_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) : (0 : Q') ≤ higherRate w :=
  Q'.mul_nonneg _ _ (by decide) (qpow_nonneg w hw 8)

theorem heatWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (spin : Nat) :
    (0 : Q') ≤ heatWeight w spin :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (dimQ_nonneg spin) (dimQ_nonneg spin)) (qpow_nonneg w hw _)

/-- Combine the natural dimension growth and the heat-power growth without division. -/
theorem scaled_power (w : Q') (base exponent : Nat) : ∀ n : Nat,
    Q'.ofNat (base^n) * qpow w (exponent*n) ≈ qpow (Q'.ofNat base*qpow w exponent) n
  | 0 => Q'.mul_one_eqv 1
  | n+1 => by
    rw [Nat.pow_succ, Nat.mul_succ]
    refine Q'.eqv_trans _ _ _ (qmul (ofNat_mul_eqv (base^n) base) (qpow_add w (exponent*n) exponent)) ?_
    refine Q'.eqv_trans _ _ _ (mul_shuffle _ _ _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (scaled_power w base exponent n)

theorem dimension_square_rational (spin : Nat) :
    dimQ spin*dimQ spin ≤ Q'.ofNat (4^(spin%2)*9^(spin/2)) :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ofNat_mul_eqv (spin+1) (spin+1)))
    (CReal.ofNat_le_ofNat (dimension_square_bound spin))

theorem envelope_factorization (w : Q') (bit higher : Nat) :
    Q'.ofNat (4^bit*9^higher) * qpow w (3*bit+8*higher) ≈
      qpow (oddRate w) bit * qpow (higherRate w) higher :=
  Q'.eqv_trans _ _ _ (qmul (ofNat_mul_eqv (4^bit) (9^higher)) (qpow_add w (3*bit) (8*higher)))
    (Q'.eqv_trans _ _ _ (mul_shuffle _ _ _ _)
      (qmul (scaled_power w 4 3 bit) (scaled_power w 9 8 higher)))

/-- The original sharp per-label weight, valid even at w=0 and w=1. -/
theorem heatWeight_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (spin : Nat) :
    heatWeight w spin ≤ qpow (oddRate w) (spin%2) * qpow (higherRate w) (spin/2) := by
  have hd := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w (c4 spin))
    (dimension_square_rational spin) (qpow_nonneg w hw0 (c4 spin))
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ _
    (qpow_antitone hw0 hw1 _ _ (casimir_parity_floor spin)) (zero_le_ofNat (4^(spin%2)*9^(spin/2)))
  exact Q'.le_trans' _ _ _ hd (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (envelope_factorization w _ _)))

theorem encoded_heatWeight_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (bit : Nat) (hb : bit ≤ 1) (higher : Nat) :
    heatWeight w (2*higher+bit) ≤ qpow (oddRate w) bit * qpow (higherRate w) higher := by
  have h := heatWeight_bound hw0 hw1 (2*higher+bit)
  have hm : (2*higher+bit)%2 = bit := by omega
  have hd : (2*higher+bit)/2 = higher := by omega
  rw [hm,hd] at h
  exact h

private theorem qpow_eqv_pow (w : Q') : ∀ n : Nat, qpow w n ≈ w^n
  | 0 => Q'.eqv_refl 1
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w (qpow_eqv_pow w n))
      (Q'.mul_comm_eqv _ w)

/-- Explicit higher-label tail: oddCost * higherRate^start / (1-higherRate). -/
def higherTailBound (w : Q') (bit start : Nat) : Q' :=
  geoTailBase (qpow (oddRate w) bit) (higherRate w) start

theorem higherTail_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hr0 : (0 : Q') < higherRate w) (hr1 : higherRate w < (1 : Q'))
    (bit : Nat) (hb : bit ≤ 1) (start count : Nat) :
    finSum (fun i => heatWeight w (2*(start+i)+bit)) count ≤ higherTailBound w bit start := by
  have ht : ∀ i, heatWeight w (2*(start+i)+bit) ≤ geoIncrBase (qpow (oddRate w) bit) (higherRate w) (start+i) := by
    intro i
    exact Q'.le_trans' _ _ _ (encoded_heatWeight_bound hw0 hw1 bit hb (start+i))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (qpow_eqv_pow (higherRate w) (start+i))))
  exact Q'.le_trans' _ _ _ (ExpNeg.finSum_le_finSum_of_termwise _ _ ht count)
    (geoTailBase_series_le (qpow_nonneg _ (oddRate_nonnegative hw0) bit) hr0 hr1 start count)

end YMGap.Continuum.SU2ParityHigherHeatEnvelope

#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.oddRate
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.higherRate
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.heatWeight
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.oddRate_nonnegative
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.higherRate_nonnegative
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.heatWeight_nonnegative
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.scaled_power
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.dimension_square_rational
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.envelope_factorization
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.heatWeight_bound
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.encoded_heatWeight_bound
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.higherTailBound
#print axioms YMGap.Continuum.SU2ParityHigherHeatEnvelope.higherTail_bound
