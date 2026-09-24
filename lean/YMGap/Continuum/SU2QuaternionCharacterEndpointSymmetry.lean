/- Right-endpoint Casimir action from symmetry of the relative character. -/

import YMGap.Continuum.SU2QuaternionSelectedCharacterEigenaction

namespace YMGap.Continuum.SU2QuaternionCharacterEndpointSymmetry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
open YMGap.Continuum.SU2QuaternionSelectedCharacterEigenaction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare

private theorem scalarAt_symm (left right : Nat) :
    RatPolyCoeffEqv (scalarAt left right) (scalarAt right left) := by
  let environment : Nat → RatPoly := fun
    | 0 => (PolyQuaternion.coordinateVariable left).scalar
    | 1 => (PolyQuaternion.coordinateVariable left).iPart
    | 2 => (PolyQuaternion.coordinateVariable left).jPart
    | 3 => (PolyQuaternion.coordinateVariable left).kPart
    | 4 => (PolyQuaternion.coordinateVariable right).scalar
    | 5 => (PolyQuaternion.coordinateVariable right).iPart
    | 6 => (PolyQuaternion.coordinateVariable right).jPart
    | _ => (PolyQuaternion.coordinateVariable right).kPart
  simpa only [scalarAt, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
    PolyQuaternionExpr.coordinate, coeffEvalExpr, environment,
    PolyQuaternion.mul, PolyQuaternion.conj] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))).scalar
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
      (by decide) environment)

/-- Normalized relative characters are coefficientwise symmetric in their
two endpoints. -/
theorem normalizedCharacterAt_symm (left right degree : Nat) :
    RatPolyCoeffEqv (normalizedCharacterAt left right degree)
      (normalizedCharacterAt right left degree) := by
  unfold normalizedCharacterAt
  exact (characterPolynomial_coeffEqv (scalarAt_symm left right) degree).smul _

/-- Exact Casimir eigenaction at the right endpoint. -/
theorem normalizedCharacterAt_blockAngularLaplacian_right
    {blocks : Nat} (hb : 1 < blocks) (a b : Fin blocks)
    (hab : a.val ≠ b.val) (degree : Nat) :
    HaarCarrierEqv blocks
      (blockAngularLaplacian b.val
        (normalizedCharacterAt a.val b.val degree))
      (polySmul (-(Q'.ofNat degree * (Q'.ofNat degree + 2)))
        (normalizedCharacterAt a.val b.val degree)) := by
  let eigenvalue := -(Q'.ofNat degree * (Q'.ofNat degree + 2))
  have hs := normalizedCharacterAt_symm a.val b.val degree
  have hc : HaarCarrierEqv blocks
      (normalizedCharacterAt a.val b.val degree)
      (normalizedCharacterAt b.val a.val degree) :=
    RatPolyCoeffEqv.haarCarrier hs
  exact (blockAngularLaplacian_carrier b.isLt hc).trans
    ((normalizedCharacterAt_blockAngularLaplacian hb b a
      (Ne.symm hab) degree).trans
      (HaarCarrierEqv.smul eigenvalue hc.symm))

end YMGap.Continuum.SU2QuaternionCharacterEndpointSymmetry

#print axioms YMGap.Continuum.SU2QuaternionCharacterEndpointSymmetry.normalizedCharacterAt_symm
#print axioms YMGap.Continuum.SU2QuaternionCharacterEndpointSymmetry.normalizedCharacterAt_blockAngularLaplacian_right
