/-
# Actual angular action on an arbitrary carrier coordinate

Formal differentiation retains zero padding in monomial exponent lists.
The derivative of a coordinate by itself therefore equals the constant one
at COMMON-PADDED coefficient strength. Off-diagonal derivatives vanish at
raw coefficient strength. Combining these facts gives the actual angular
coordinate action, without a sphere equation or unit-quaternion premise.

The next consumer is the original all-link vertex-Gauss L/R coordinate pin
for literal closed Wilson sources. No such Gauss telescope, continuum
generator/domain, signed-response estimate or mass gap is supplied here.
-/

import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.SU2QuaternionAngularCoordinatePadded

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier

private theorem lowered_coordinate (c : Nat) :
    lowerExponentAt c (varMono c) = List.replicate (c+1) 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change 0 :: lowerExponentAt c (varMono c) = 0 :: List.replicate (c+1) 0
      exact congrArg (List.cons 0) ih

private theorem zero_exponents (n coordinate : Nat) :
    exponentAt (List.replicate n 0) coordinate = 0 := by
  induction n generalizing coordinate with
  | zero => rfl
  | succ n ih =>
      cases coordinate with
      | zero => rfl
      | succ coordinate => exact ih coordinate

/-- The literal derivative retains its all-zero exponent list; common
padding identifies it with one without any Haar or sphere assumption. -/
theorem ratDerivative_polyVar_self_padded (B c : Nat) :
    PaddedPolynomialCoeffEqv B (ratDerivative c (polyVar c)) polyOne := by
  apply PaddedPolynomialCoeffEqv.of_prefix
  change QuaternionPrefixPolynomialEqv B
    [(lowerExponentAt c (varMono c), Q'.ofNat (exponentAt (varMono c) c) * 1)] [([], 1)]
  rw [lowered_coordinate, exponentAt_varMono, if_pos rfl]
  exact .cons ⟨by
    change Q'.eqv (Q'.ofNat 1 * 1) 1
    decide, fun coordinate _ => zero_exponents (c+1) coordinate⟩ .nil

private theorem coordinate_factor (B a b c : Nat) :
    PaddedPolynomialCoeffEqv B (polyMul (polyVar a) (ratDerivative b (polyVar c)))
      (if c = b then polyVar a else polyZero) := by
  by_cases h : c = b
  · subst c
    rw [if_pos rfl]
    exact ((PaddedPolynomialCoeffEqv.refl B (polyVar a)).mul
      (ratDerivative_polyVar_self_padded B b)).trans
        (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_one _))
  · rw [if_neg h]
    exact PaddedPolynomialCoeffEqv.of_coeff
      (((ratDerivative_polyVar_ne b c (Ne.symm h)).mul_left (polyVar a)).trans
        (RatPolyCoeffEqv.mul_zero_right _))

/-- The actual infinitesimal coordinate-plane rotation on any declared
carrier coordinate. All three coordinate guards stay explicit. -/
theorem angularDerivative_polyVar_padded {B a b c : Nat}
    (_ha : a < 4*B) (_hb : b < 4*B) (_hc : c < 4*B) :
    PaddedPolynomialCoeffEqv B (angularDerivative a b (polyVar c))
      (polyAdd (if c=b then polyVar a else polyZero)
        (polyNeg (if c=a then polyVar b else polyZero))) := by
  unfold angularDerivative
  exact ((coordinate_factor B a b c).add ((coordinate_factor B b a c).smul (-1))).trans
    (PaddedPolynomialCoeffEqv.of_coeff
      ((RatPolyCoeffEqv.refl _).add (neg_smul _).symm))

end YMGap.Continuum.SU2QuaternionAngularCoordinatePadded

#print axioms YMGap.Continuum.SU2QuaternionAngularCoordinatePadded.ratDerivative_polyVar_self_padded
#print axioms YMGap.Continuum.SU2QuaternionAngularCoordinatePadded.angularDerivative_polyVar_padded
