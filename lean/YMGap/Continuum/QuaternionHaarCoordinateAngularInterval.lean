/-
# Coordinate intervals for one quaternion angular derivative

Each supported quaternion coordinate has its sharp unit interval.  For a
head-plane rotation of any supported coordinate, the two formal derivative
factors each have unit interval, hence their signed sum has cap two.  Matching
derivatives are identified only through prefix/Haar-carrier equality, so the
proof does not confuse trailing-zero-padded constants with raw coefficient
equality.
-/

import YMGap.Continuum.QuaternionHaarAngularCarrier
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck

namespace YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

/-- Every coordinate in the declared quaternion carrier has its sharp unit
interval. -/
def coordinateInterval {blocks coordinate : Nat}
    (hc : coordinate < 4 * blocks) :
    Interval blocks (polyVar coordinate) 1 :=
  unitSquareInterval (coordinateSquareBound blocks coordinate hc)

private theorem ratDerivative_polyVar_ne (i j : Nat) (hij : i ≠ j) :
    RatPolyCoeffEqv (ratDerivative i (polyVar j)) polyZero := by
  intro weight
  change
    (Q'.ofNat (exponentAt (varMono j) i) * 1) *
        weight (lowerExponentAt i (varMono j)) + 0 ≈ 0
  rw [exponentAt_varMono, if_neg hij]
  have hcoefficient : Q'.ofNat 0 * 1 ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ 1 Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv 1)
  have hterm :
      (Q'.ofNat 0 * 1) * weight (lowerExponentAt i (varMono j)) ≈
        (0 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hcoefficient)
      (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hterm (Q'.eqv_refl 0))
    (QPoly.q_add_zero_eqv 0)

private theorem derivativeFactor_self_carrier
    (blocks factor derivative : Nat) (hb : 0 < blocks)
    (hf : factor < 4) (hd : derivative < 4) :
    HaarCarrierEqv blocks
      (polyMul (polyVar factor) (ratDerivative derivative (polyVar derivative)))
      (polyVar factor) := by
  have hfactor : factor < 4 * blocks := by omega
  have hderivative : derivative < 4 * blocks := by omega
  apply carrierOfPrefix
    (supported_polyMul
      (coordinateSquareBound blocks factor hfactor).support
      (ratDerivative_supported
        (coordinateSquareBound blocks derivative hderivative).support))
    (coordinateSquareBound blocks factor hfactor).support
  have hfCases : factor = 0 ∨ factor = 1 ∨ factor = 2 ∨ factor = 3 := by
    omega
  have hdCases : derivative = 0 ∨ derivative = 1 ∨
      derivative = 2 ∨ derivative = 3 := by
    omega
  rcases hfCases with rfl | rfl | rfl | rfl <;>
    rcases hdCases with rfl | rfl | rfl | rfl <;>
      exact quaternionPrefixPolynomialCheck_sound blocks (by rfl)

private def derivativeFactorInterval
    (blocks factor derivative coordinate : Nat) (hb : 0 < blocks)
    (hf : factor < 4) (hd : derivative < 4)
    (hc : coordinate < 4 * blocks) :
    Interval blocks
      (polyMul (polyVar factor) (ratDerivative derivative (polyVar coordinate))) 1 := by
  have hfactor : factor < 4 * blocks := by omega
  have hsupport : SupportedQuaternionBlocks blocks
      (polyMul (polyVar factor) (ratDerivative derivative (polyVar coordinate))) :=
    supported_polyMul
      (coordinateSquareBound blocks factor hfactor).support
      (ratDerivative_supported (coordinateSquareBound blocks coordinate hc).support)
  by_cases heq : derivative = coordinate
  · subst coordinate
    exact intervalOfCarrier hsupport
      (derivativeFactor_self_carrier blocks factor derivative hb hf hd)
      (coordinateInterval hfactor)
  · have hz : RatPolyCoeffEqv
        (polyMul (polyVar factor) (ratDerivative derivative (polyVar coordinate)))
        polyZero :=
      ((ratDerivative_polyVar_ne derivative coordinate heq).mul_left
        (polyVar factor)).trans (RatPolyCoeffEqv.mul_zero_right _)
    exact Interval.ofCoeff hsupport hz
      (Interval.weaken (Interval.zero blocks) (by decide))

/-- A head angular derivative of one supported carrier coordinate lies in
the conservative interval `[-2,2]`.  No pointwise derivative identity or
analytic estimate is used. -/
def coordinateAngularInterval {blocks i j coordinate : Nat}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hc : coordinate < 4 * blocks) :
    Interval blocks (angularDerivative i j (polyVar coordinate)) 2 := by
  let left := polyMul (polyVar i) (ratDerivative j (polyVar coordinate))
  let right := polyMul (polyVar j) (ratDerivative i (polyVar coordinate))
  have hleft : Interval blocks left 1 :=
    derivativeFactorInterval blocks i j coordinate hb hi hj hc
  have hright : Interval blocks right 1 :=
    derivativeFactorInterval blocks j i coordinate hb hj hi hc
  have hnegative : Interval blocks (polySmul (-1) right) 1 :=
    Interval.ofCoeff (polySmul_supported hright.support (-1))
      (neg_smul right).symm (intervalNeg hright)
  unfold angularDerivative
  exact Interval.changeCap (by decide) (hleft.add hnegative)

end YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

#print axioms YMGap.Continuum.QuaternionHaarCoordinateAngularInterval.coordinateInterval
#print axioms YMGap.Continuum.QuaternionHaarCoordinateAngularInterval.coordinateAngularInterval
