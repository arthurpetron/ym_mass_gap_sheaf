/-
# The existing family response band cannot be a small scaling coefficient

The actual padded signed-family energy band uses c = 1-rho. Its explicit
rho is at most (1/32)^(56*size), at EVERY nome 0<w<1. For a nonempty family,
c is therefore at least 1-2^(-280). Transport to the original completed
carrier multiplies c by (1+comparisonEta)^2 >= 1, so cannot improve it.

This bounds the ALREADY COMPUTED upper-bound coefficient, not the true
energy/OWN-variance ratio. It rules out using that particular band constant
to supply a spacing-small upper-energy bound. It neither refutes a stronger
original signed estimate nor says anything negative about Yang--Mills.
No action, observable, terminal message, variance, or frontier is changed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
import YMGap.Continuum.BF4WilsonAllNomeTerminalReferenceEnergyRatio

namespace YMGap.Continuum.BF4WilsonAllNomeFamilyBandCalibrationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.BF4ExactSlabStarRateObstruction (prefixCap_ge_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
  (localLower localUpper localLower_positive localUpper_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (familyResponseFraction)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound (pow_add_eqv)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
  (comparisonEta comparisonEta_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeTerminalReferenceEnergyRatio (referenceCoefficient)

local infix:50 " ≈ " => Q'.eqv

/-- Explicit conservative ceiling. At size one it is exactly 2^(-280). -/
def fractionCeiling (size : Nat) : Q' :=
  (Q'.mkPos 1 32 (by decide))^(56*size)

/-- The fixed positive coefficient barrier for every nonempty listed family. -/
def coefficientFloor : Q' := (1 : Q')-fractionCeiling 1

private theorem one_le_pow {a : Q'} (ha : (1 : Q') ≤ a) :
    ∀ n : Nat, (1 : Q') ≤ a^n
  | 0 => Q'.le_refl' _
  | n+1 => by
    have ha0 := Q'.le_trans' _ _ _ Q'.zero_le_one ha
    have h := Q'.mul_le_mul_of_nonneg_left _ _ a (one_le_pow ha n) ha0
    exact Q'.le_trans' _ _ _ ha
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv a)) h)

private theorem reciprocal_le_one {a : Q'} (ha : (0 : Q') < a)
    (h1 : (1 : Q') ≤ a) : Q'.recipPos a ha ≤ (1 : Q') := by
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos a ha) h1
    (Q'.le_of_lt (Q'.recipPos_pos a ha))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_recipPos_eqv a ha)))

/-- Retain the complete list-size dependence; no schedule limit is inferred. -/
theorem familyResponseFraction_le_ceiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    familyResponseFraction hw0 hw1 size ≤ fractionCeiling size := by
  let l := localLower w (4*size)
  let u := localUpper w (4*size)
  let hU := Q'.mul_pos (localUpper_positive hw0 hw1 (4*size))
    (localUpper_positive hw0 hw1 (4*size))
  let r := Q'.recipPos (u*u) hU
  let tau := Q'.mkPos 1 32 (by decide)
  have hl0 := Q'.le_of_lt (localLower_positive hw0 hw1 (4*size))
  have hl : l ≤ tau^(28*size) := by
    have hp := HKConv.pow_le_pow_base (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (headFloor_le_oneThirtySecond hw0 hw1) (7*(4*size))
    have hn : 7*(4*size) = 28*size := by omega
    simpa only [l, localLower, tau, hn] using hp
  have hu : (1 : Q') ≤ u := one_le_pow (prefixCap_ge_one hw0 hw1) _
  have hu0 : (0 : Q') ≤ u := Q'.le_trans' _ _ _ Q'.zero_le_one hu
  have huu : (1 : Q') ≤ u*u := Q'.le_trans' _ _ _ hu
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv u))
      (Q'.mul_le_mul_of_nonneg_left _ _ u hu hu0))
  have hr : r ≤ (1 : Q') := reciprocal_le_one hU huu
  have hll : (0 : Q') ≤ l*l := Q'.mul_nonneg _ _ hl0 hl0
  have hheat := HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 12
  have hheat0 := qpow_nonneg w (Q'.le_of_lt hw0) 12
  have hdrop : (qpow w 12*(l*l))*r ≤ l*l :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hr
        (Q'.mul_nonneg _ _ hheat0 hll))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ (l*l) hheat hll)
          (Q'.le_of_eqv (Q'.one_mul_eqv _))))
  have hsq : l*l ≤ tau^(28*size)*tau^(28*size) :=
    HKConv.mul_le_mul' hl0 (Q'.pow_nonneg tau (by decide) _) hl hl
  have hn : 28*size+28*size = 56*size := by omega
  exact Q'.le_trans' _ _ _ hdrop (Q'.le_trans' _ _ _ hsq
    (Q'.ge_of_eqv (by simpa only [hn] using pow_add_eqv tau (28*size) (28*size))))

theorem fractionCeiling_nonempty (size : Nat) (hs : 0 < size) :
    fractionCeiling size ≤ fractionCeiling 1 := by
  unfold fractionCeiling
  exact HKConvGen.pow_base_antitone (by decide) (by decide)
    (Nat.mul_le_mul_left 56 hs)

theorem coefficientFloor_ge_half : HalfPow.half ≤ coefficientFloor := by
  let tau := Q'.mkPos 1 32 (by decide)
  have hpow : fractionCeiling 1 ≤ tau^1 :=
    HKConvGen.pow_base_antitone (by decide) (by decide) (by decide : 1 ≤ 56)
  have hceil : fractionCeiling 1 ≤ tau := Q'.le_trans' _ _ _ hpow
    (Q'.le_of_eqv (Q'.mul_one_eqv tau))
  exact Q'.le_trans' _ _ _ (by decide : HalfPow.half ≤ (1 : Q')-tau)
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hceil))

/-- This is a bound on the explicit BAND COEFFICIENT, not the actual ratio. -/
theorem family_band_coefficient_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) (hs : 0 < size) :
    coefficientFloor ≤ (1 : Q')-familyResponseFraction hw0 hw1 size :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_trans' _ _ _
    (familyResponseFraction_le_ceiling hw0 hw1 size) (fractionCeiling_nonempty size hs)))

/-- The existing depth/completion loss never decreases a nonnegative input. -/
theorem referenceCoefficient_ge_input {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width s : Nat)
    (c : Q') (hc : (0 : Q') ≤ c) :
    c ≤ referenceCoefficient hw0 hw1 width s c := by
  let a := (1 : Q')+comparisonEta hw0 hw1 width s
  have ha : (1 : Q') ≤ a := Q'.add_le_self_of_nonneg _ _
    (comparisonEta_nonnegative hw0 hw1 width s)
  have ha0 := Q'.le_trans' _ _ _ Q'.zero_le_one ha
  have haa : (1 : Q') ≤ a*a := Q'.le_trans' _ _ _ ha
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv a))
      (Q'.mul_le_mul_of_nonneg_left _ _ a ha ha0))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv c))
    (Q'.mul_le_mul_of_nonneg_left _ _ c haa hc)

/-- No nome, width or reference depth improves THIS transported coefficient. -/
theorem transported_family_band_coefficient_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) (hs : 0 < size) (width s : Nat) :
    coefficientFloor ≤ referenceCoefficient hw0 hw1 width s
      ((1 : Q')-familyResponseFraction hw0 hw1 size) := by
  have h := family_band_coefficient_floor hw0 hw1 size hs
  have hc := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ HalfPow.half)
    (Q'.le_trans' _ _ _ coefficientFloor_ge_half h)
  exact Q'.le_trans' _ _ _ h (referenceCoefficient_ge_input hw0 hw1 width s _ hc)

/-- A target C*a below one half cannot be paid by the transported BAND
constant. No identification of a with physical spacing is assumed. -/
theorem transported_family_band_linear_budget_false {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) (hs : 0 < size) (width s : Nat) (C a : Q')
    (hbudget : C*a < HalfPow.half) :
    ¬ (referenceCoefficient hw0 hw1 width s
      ((1 : Q')-familyResponseFraction hw0 hw1 size) ≤ C*a) := by
  intro h
  have hfloor := Q'.le_trans' _ _ _ coefficientFloor_ge_half
    (Q'.le_trans' _ _ _
      (transported_family_band_coefficient_floor hw0 hw1 size hs width s) h)
  exact Int.not_lt.mpr hfloor hbudget

#print axioms familyResponseFraction_le_ceiling
#print axioms fractionCeiling_nonempty
#print axioms coefficientFloor_ge_half
#print axioms family_band_coefficient_floor
#print axioms referenceCoefficient_ge_input
#print axioms transported_family_band_coefficient_floor
#print axioms transported_family_band_linear_budget_false

end YMGap.Continuum.BF4WilsonAllNomeFamilyBandCalibrationObstruction
