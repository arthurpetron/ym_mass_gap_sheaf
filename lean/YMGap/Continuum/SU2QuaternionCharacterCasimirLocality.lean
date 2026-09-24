/-
# Character locality for literal block Casimirs

The block angular Laplacian obeys the expected product rule when one factor
is independent of the differentiated block.  Normalized relative characters
are independent of every block except their two endpoints.
-/

import YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
import YMGap.Continuum.SU2QuaternionCharacterProductPositive

namespace YMGap.Continuum.SU2QuaternionCharacterCasimirLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

private theorem derivative_mul_independent (block i j : Nat)
    (hi : i < 4) (hj : j < 4) (p q : RatPoly)
    (hq : QuaternionBlockIndependent block q) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j (polyMul p q))
      (polyMul (blockAngularDerivative block i j p) q) := by
  have hz := angularDerivative_blockIndependent_zero hi hj hq
  unfold blockAngularDerivative
  exact (angularDerivative_mul (4*block+i) (4*block+j) p q).trans
    (((RatPolyCoeffEqv.refl _).add
      ((hz.mul_left p).trans (RatPolyCoeffEqv.mul_zero_right p))).trans
        (RatPolyCoeffEqv.add_zero _))

private theorem secondDerivative_mul_independent (block i j : Nat)
    (hi : i < 4) (hj : j < 4) (p q : RatPoly)
    (hq : QuaternionBlockIndependent block q) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j (polyMul p q)))
      (polyMul
        (blockAngularDerivative block i j
          (blockAngularDerivative block i j p)) q) := by
  exact (angularDerivative_congr (4*block+i) (4*block+j)
    (derivative_mul_independent block i j hi hj p q hq)).trans
      (derivative_mul_independent block i j hi hj
        (blockAngularDerivative block i j p) q hq)

private theorem six_mul_right (f : Nat → Nat → RatPoly) (q : RatPoly) :
    RatPolyCoeffEqv (six fun i j => polyMul (f i j) q)
      (polyMul (six f) q) := by
  unfold six
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 6))
      (.add (.mul (.var 1) (.var 6))
        (.add (.mul (.var 2) (.var 6))
          (.add (.mul (.var 3) (.var 6))
            (.add (.mul (.var 4) (.var 6)) (.mul (.var 5) (.var 6)))))))
    (.mul (.add (.var 0) (.add (.var 1) (.add (.var 2)
      (.add (.var 3) (.add (.var 4) (.var 5)))))) (.var 6))
    (by decide) (fun
      | 0 => f 0 1 | 1 => f 0 2 | 2 => f 0 3
      | 3 => f 1 2 | 4 => f 1 3 | 5 => f 2 3 | _ => q)

/-- A block Laplacian differentiates only the factor depending on that block. -/
theorem blockAngularLaplacian_mul_independent (block : Nat) (p q : RatPoly)
    (hq : QuaternionBlockIndependent block q) :
    RatPolyCoeffEqv (blockAngularLaplacian block (polyMul p q))
      (polyMul (blockAngularLaplacian block p) q) := by
  refine (blockAngularLaplacian_eq_six block (polyMul p q)).trans ?_
  refine (RatPolyCoeffEqv.add
    (secondDerivative_mul_independent block 0 1 (by decide) (by decide) p q hq)
    ((secondDerivative_mul_independent block 0 2 (by decide) (by decide) p q hq).add
      ((secondDerivative_mul_independent block 0 3 (by decide) (by decide) p q hq).add
        ((secondDerivative_mul_independent block 1 2 (by decide) (by decide) p q hq).add
          ((secondDerivative_mul_independent block 1 3 (by decide) (by decide) p q hq).add
            (secondDerivative_mul_independent block 2 3 (by decide) (by decide) p q hq)))))).trans ?_
  exact (six_mul_right (fun i j => blockAngularDerivative block i j
    (blockAngularDerivative block i j p)) q).trans
      ((blockAngularLaplacian_eq_six block p).symm.mul_right q)

/-- A normalized relative character is independent of every quaternion block
apart from its two displayed endpoints. -/
theorem normalizedCharacterAt_independent {left right block : Nat}
    (hleft : block ≠ left) (hright : block ≠ right) (degree : Nat) :
    QuaternionBlockIndependent block
      (normalizedCharacterAt left right degree) := by
  unfold normalizedCharacterAt
  exact quaternionBlockIndependent_polySmul _
    (degree_zero_independent
      (character_independent (scalar_independent block left right hleft hright) degree))

end YMGap.Continuum.SU2QuaternionCharacterCasimirLocality

#print axioms YMGap.Continuum.SU2QuaternionCharacterCasimirLocality.blockAngularLaplacian_mul_independent
#print axioms YMGap.Continuum.SU2QuaternionCharacterCasimirLocality.normalizedCharacterAt_independent
