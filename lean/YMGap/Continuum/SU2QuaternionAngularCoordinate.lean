/-
# Angular derivatives of arbitrary supported coordinates

The self derivative of a variable is the constant one under the original
Haar carrier, not necessarily as a raw exponent-list coefficient identity.
This elementary calculation supplies the simultaneous-rotation identity of
the original relative scalar at arbitrary block indices.
-/

import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

namespace YMGap.Continuum.SU2QuaternionAngularCoordinate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem lower_self (k : Nat) :
    lowerExponentAt k (varMono k) = List.replicate (k+1) 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change 0 :: lowerExponentAt k (varMono k) = 0 :: List.replicate (k+1) 0
      rw [ih]

private theorem zeros_exponent : ∀ n i, exponentAt (List.replicate n 0) i = 0
  | 0, _ => rfl
  | _+1, 0 => rfl
  | n+1, i+1 => zeros_exponent n i

/-- Constant one with trailing-zero padding removed only through supported
Haar-carrier equality. -/
theorem derivative_self_carrier {blocks coordinate : Nat}
    (hc : coordinate < 4 * blocks) :
    HaarCarrierEqv blocks (ratDerivative coordinate (polyVar coordinate)) polyOne := by
  apply carrierOfPrefix
    (ratDerivative_supported (coordinateInterval hc).support) (supported_one blocks)
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · change Q'.eqv (Q'.ofNat (exponentAt (varMono coordinate) coordinate) * 1) 1
      rw [exponentAt_varMono, if_pos rfl]
      decide
    · intro k _
      change exponentAt (lowerExponentAt coordinate (varMono coordinate)) k = 0
      rw [lower_self, zeros_exponent]
  · exact .nil

private theorem derivative_var_carrier {blocks i k : Nat}
    (hk : k < 4 * blocks) :
    HaarCarrierEqv blocks (ratDerivative i (polyVar k))
      (if i = k then polyOne else polyZero) := by
  by_cases h : i = k
  · subst i
    rw [if_pos rfl]
    exact derivative_self_carrier hk
  · rw [if_neg h]
    exact RatPolyCoeffEqv.haarCarrier (ratDerivative_polyVar_ne i k h)

/-- The exact Kronecker-delta formula at any supported coordinate. -/
theorem angular_coordinate_carrier {blocks i j k : Nat}
    (hk : k < 4 * blocks) :
    HaarCarrierEqv blocks (angularDerivative i j (polyVar k))
      (polyAdd (if j = k then polyVar i else polyZero)
        (polySmul (-1) (if i = k then polyVar j else polyZero))) := by
  have left : HaarCarrierEqv blocks
      (polyMul (polyVar i) (ratDerivative j (polyVar k)))
      (if j = k then polyVar i else polyZero) := by
    refine ((derivative_var_carrier (i := j) hk).mul_left (polyVar i)).trans ?_
    by_cases h : j = k
    · simp only [if_pos h]
      exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_one _)
    · simp only [if_neg h]
      exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _)
  have right : HaarCarrierEqv blocks
      (polyMul (polyVar j) (ratDerivative i (polyVar k)))
      (if i = k then polyVar j else polyZero) := by
    refine ((derivative_var_carrier (i := i) hk).mul_left (polyVar j)).trans ?_
    by_cases h : i = k
    · simp only [if_pos h]
      exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_one _)
    · simp only [if_neg h]
      exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _)
  exact HaarCarrierEqv.add left (HaarCarrierEqv.smul (-1) right)

end YMGap.Continuum.SU2QuaternionAngularCoordinate

#print axioms YMGap.Continuum.SU2QuaternionAngularCoordinate.derivative_self_carrier
#print axioms YMGap.Continuum.SU2QuaternionAngularCoordinate.angular_coordinate_carrier
