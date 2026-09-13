/-
# Coefficient-L1 majorant for the original heat-character polynomials

The actual Chebyshev recurrence in `RatPoly` gives

    L1(characterPolynomial p s) <= (2 * L1(p) + 1)^s.

Multiplying by the ORIGINAL heat coefficient retains the Casimir damping:

    (s+1) * w^(s*(s+2)) * (2 * L1(p) + 1)^s.

This is a syntactic coefficient bound, so it controls exact quaternion Haar
integration without assuming a pointwise-to-integrated limit bridge. The
radius is computed from the supplied polynomial. No numerical pilot constant
or spectral rate is introduced. Summability, a moving-anchor GNS Cauchy
modulus, physical vacuum stationarity and spacing-uniform control are not
asserted here.
-/

import YMGap.Continuum.BF4GeometricHaarMehlerProjection
import YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

namespace YMGap.Continuum.SU2HeatCharacterPolynomialMajorant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep

local infix:50 " ≈ " => Q'.eqv

theorem coefficientL1_add (p q : RatPoly) :
    polynomialCoefficientL1 (polyAdd p q) ≈
      polynomialCoefficientL1 p + polynomialCoefficientL1 q := by
  induction p with
  | nil => exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | cons t p ih =>
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Q'.abs t.2) _ _ ih)
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

def characterRadius (p : RatPoly) : Q' := 2 * polynomialCoefficientL1 p + 1

theorem characterRadius_nonnegative (p : RatPoly) : (0 : Q') ≤ characterRadius p :=
  Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide) (polynomialCoefficientL1_nonnegative p))
    Q'.zero_le_one

theorem one_le_characterRadius (p : RatPoly) : (1 : Q') ≤ characterRadius p :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg 1 _
      (Q'.mul_nonneg _ _ (by decide) (polynomialCoefficientL1_nonnegative p)))
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _))

theorem characterRadius_pow_step (p : RatPoly) (s : Nat) :
    characterRadius p ^ s ≤ characterRadius p ^ (s + 1) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (one_le_characterRadius p)
      (Q'.pow_nonneg _ (characterRadius_nonnegative p) s))

private theorem twice_coefficientL1 (p : RatPoly) :
    polynomialCoefficientL1 (polySmul 2 p) ≤ 2 * polynomialCoefficientL1 p :=
  Q'.le_trans' _ _ _ (polynomialCoefficientL1_smul_le 2 p)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (by decide)))

private theorem neg_coefficientL1 (p : RatPoly) :
    polynomialCoefficientL1 (polySmul (-1) p) ≤ polynomialCoefficientL1 p :=
  Q'.le_trans' _ _ _ (polynomialCoefficientL1_smul_le (-1) p)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 1 _ (by decide)) (Q'.one_mul_eqv _)))

/-- Bound the original polynomial recurrence, not a scalar surrogate. -/
theorem characterPolynomial_coefficientL1 (p : RatPoly) : ∀ s : Nat,
    polynomialCoefficientL1 (characterPolynomial p s) ≤ characterRadius p ^ s
  | 0 => by
    change polynomialCoefficientL1 polyOne ≤ (1 : Q')
    decide
  | 1 =>
    Q'.le_trans' _ _ _ (twice_coefficientL1 p)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))))
  | s + 2 => by
    have hmul := Q'.le_trans' _ _ _
      (polynomialCoefficientL1_mul_le (polySmul 2 p) (characterPolynomial p (s + 1)))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (twice_coefficientL1 p)
          (polynomialCoefficientL1_nonnegative _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (characterPolynomial_coefficientL1 p (s + 1))
          (Q'.mul_nonneg _ _ (by decide) (polynomialCoefficientL1_nonnegative p))))
    have hneg := Q'.le_trans' _ _ _ (neg_coefficientL1 (characterPolynomial p s))
      (Q'.le_trans' _ _ _ (characterPolynomial_coefficientL1 p s) (characterRadius_pow_step p s))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_add _ _))
      (Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hmul hneg)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)))
          (Q'.eqv_symm (ExpNeg.add_mul_eqv _ _ _)))))

/-- Exact heat coefficient times the computed polynomial growth radius. -/
def heatCharacterMajorant (w : Q') (p : RatPoly) (s : Nat) : Q' :=
  coeffW w s * characterRadius p ^ s

theorem heatCharacterMajorant_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (p : RatPoly) (s : Nat) :
    (0 : Q') ≤ heatCharacterMajorant w p s :=
  Q'.mul_nonneg _ _ (coeffW_nonneg hw s) (Q'.pow_nonneg _ (characterRadius_nonnegative p) s)

theorem heatCharacter_coefficientL1 {w : Q'} (hw : (0 : Q') ≤ w) (p : RatPoly) (s : Nat) :
    polynomialCoefficientL1 (polySmul (coeffW w s) (characterPolynomial p s)) ≤
      heatCharacterMajorant w p s :=
  Q'.le_trans' _ _ _ (polynomialCoefficientL1_smul_le _ _)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg (coeffW_nonneg hw s)))))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (characterPolynomial_coefficientL1 p s) (coeffW_nonneg hw s)))

theorem packetCharacter_coefficientL1 {w : Q'} (hw : (0 : Q') ≤ w) (p : RatPoly)
    (K s : Nat) (hs : s < K + 1) :
    polynomialCoefficientL1 (polySmul (coeffAt (heatKernelPacket K w) s) (characterPolynomial p s)) ≤
      heatCharacterMajorant w p s := by
  rw [coeffAt_heatKernelPacket hs]
  exact heatCharacter_coefficientL1 hw p s

theorem heatCharacter_haar_abs {w : Q'} (hw : (0 : Q') ≤ w) (blocks : Nat) (p : RatPoly) (s : Nat) :
    Q'.abs (quaternionHaar blocks (polySmul (coeffW w s) (characterPolynomial p s))) ≤
      heatCharacterMajorant w p s :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _) (heatCharacter_coefficientL1 hw p s)

end YMGap.Continuum.SU2HeatCharacterPolynomialMajorant

#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.coefficientL1_add
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.characterRadius
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.characterRadius_nonnegative
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.one_le_characterRadius
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.characterRadius_pow_step
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.characterPolynomial_coefficientL1
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.heatCharacterMajorant
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.heatCharacterMajorant_nonnegative
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.heatCharacter_coefficientL1
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.packetCharacter_coefficientL1
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialMajorant.heatCharacter_haar_abs
