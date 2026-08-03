/- Shared definitions for the split exact orientation certificates. -/

import YMGap.Continuum.SU2QuaternionRatPolyDifferential
import YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- The three squared radii not belonging to the selected head quaternion. -/
def retainedThreeRadiusProduct : RatPoly :=
  polyMul (quaternionRadiusPolynomial 1)
    (polyMul (quaternionRadiusPolynomial 2)
      (quaternionRadiusPolynomial 3))

theorem fourRadius_eq_head_mul_retained :
    fourQuaternionRadiusProduct =
      polyMul (quaternionRadiusPolynomial 0)
        retainedThreeRadiusProduct := rfl

/-- One fixed orientation's two genuinely finite quaternion identities.  The
scalar/radius identity is derived uniformly from Euler homogeneity. -/
structure ExposedDifferentialCertificate
    (reverse0 reverse1 reverse2 reverse3 : Bool) : Prop where
  laplacianScalar :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)
      polyZero
  gradientSelf :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)
      retainedThreeRadiusProduct

/-- The retained radii have selected-head degree zero. -/
theorem retainedThreeRadiusProduct_headDegree_zero :
    HasQuaternionBlockDegree 0 0 retainedThreeRadiusProduct := by
  unfold retainedThreeRadiusProduct
  exact HasQuaternionBlockDegree.relabel (by decide)
    ((hasQuaternionBlockDegree_radius 1 0).mul
      ((hasQuaternionBlockDegree_radius 2 0).mul
        (hasQuaternionBlockDegree_radius 3 0)))

/-- Radial directional derivative for every polynomial homogeneous in the
selected quaternion.  This is the Euler theorem with all three tail radii
retained as polynomial coefficients. -/
theorem headGradientDot_fourRadius_of_blockDegree
    (degree : Nat) (polynomial : RatPoly)
    (hdegree : HasQuaternionBlockDegree 0 degree polynomial) :
    RatPolyCoeffEqv
      (headGradientDot polynomial fourQuaternionRadiusProduct)
      (polySmul (2 * Q'.ofNat degree)
        (polyMul retainedThreeRadiusProduct polynomial)) := by
  rw [fourRadius_eq_head_mul_retained]
  have hhead : RatPolyCoeffEqv
      (headGradientDot polynomial (quaternionRadiusPolynomial 0))
      (polySmul (2 * Q'.ofNat degree) polynomial) :=
    RatPolyCoeffEqv.trans
      (headGradientDot_headRadius_right polynomial)
      (RatPolyCoeffEqv.trans
        ((headEuler_of_blockDegree degree polynomial hdegree).smul 2)
        (RatPolyCoeffEqv.smul_assoc 2 (Q'.ofNat degree) polynomial))
  have hfirst : RatPolyCoeffEqv
      (polyMul
        (headGradientDot polynomial (quaternionRadiusPolynomial 0))
        retainedThreeRadiusProduct)
      (polySmul (2 * Q'.ofNat degree)
        (polyMul retainedThreeRadiusProduct polynomial)) :=
    RatPolyCoeffEqv.trans
      (hhead.mul_right retainedThreeRadiusProduct)
      (RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.polyMul_smul_left
          (2 * Q'.ofNat degree) polynomial retainedThreeRadiusProduct)
        ((RatPolyCoeffEqv.mul_comm
          polynomial retainedThreeRadiusProduct).smul
            (2 * Q'.ofNat degree)))
  have hsecond : RatPolyCoeffEqv
      (polyMul (quaternionRadiusPolynomial 0)
        (headGradientDot polynomial retainedThreeRadiusProduct))
      polyZero :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_left (quaternionRadiusPolynomial 0)
        (headGradientDot_headIndependent_right polynomial
          retainedThreeRadiusProduct
          retainedThreeRadiusProduct_headDegree_zero))
      (RatPolyCoeffEqv.mul_zero_right
        (quaternionRadiusPolynomial 0))
  exact RatPolyCoeffEqv.trans
    (headGradientDot_mul_right polynomial
      (quaternionRadiusPolynomial 0) retainedThreeRadiusProduct)
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add hfirst hsecond)
      (RatPolyCoeffEqv.add_zero _))

/-- The exposed scalar is selected-head linear, so its radial derivative is
exactly twice the scalar times the retained-radius coefficient. -/
theorem gradient_exposedScalar_fourRadius
    (reverse0 reverse1 reverse2 reverse3 : Bool) :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
        fourQuaternionRadiusProduct)
      (polySmul 2
        (polyMul retainedThreeRadiusProduct
          (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar)) := by
  refine RatPolyCoeffEqv.trans
    (headGradientDot_fourRadius_of_blockDegree 1 _
      (exposedFourWord_scalar_blockDegree
        reverse0 reverse1 reverse2 reverse3 0 (by omega))) ?_
  exact RatPolyCoeffEqv.smul_coefficient
    (Q'.mul_one_eqv 2) _

/-- The orientation-independent radial Laplacian certificate. -/
theorem laplacian_fourRadius :
    RatPolyCoeffEqv
      (headLaplacian fourQuaternionRadiusProduct)
      (polySmul 8 retainedThreeRadiusProduct) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase.laplacian_fourRadius
