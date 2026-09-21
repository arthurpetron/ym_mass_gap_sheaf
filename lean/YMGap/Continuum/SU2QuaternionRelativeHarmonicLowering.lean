/-
# Terminating harmonic lowering for the original relative scalar

The explicit operator D_y = sum y_i partial_(x_i) preserves head harmonicity
and lowers positive head degree by one.  Iterating the exact Gaussian
recurrence therefore computes the pairing with (x . y)^n as a head-degree-zero
polynomial, with every retained coefficient unchanged.  The original Haar
pairing has its explicit radial denominator.  Identifying the output with
n! times head-to-retained-link substitution remains a separate obligation;
this module does not assume the diagonal character normalization.
-/

import YMGap.Continuum.SU2QuaternionDerivativeCommutation
import YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion
import YMGap.Continuum.SU2QuaternionRelativeCharacterSelection

namespace YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionDerivativeCommutation
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation (ratPolyPow)

/-- Differentiate the ACTUAL relative quaternion scalar, not an assumed
replacement kernel.  Only four finite polynomial identities are checked. -/
theorem relativeScalar_derivative (i : Fin 4) :
    RatPolyCoeffEqv (ratDerivative i.val relativeScalar) (polyVar (4+i.val)) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  revert i
  decide +kernel

theorem retained_coordinate_independent (i : Fin 4) :
    HasQuaternionBlockDegree 0 0 (polyVar (4+i.val)) :=
  hasQuaternionBlockDegree_coordinate 1 i.val 0 i.isLt

theorem relativeScalar_headDegree : HasQuaternionBlockDegree 0 1 relativeScalar := by
  have hc : relativeScalar.all
      (fun t => decide (quaternionBlockDegree t.1 0 = 1)) = true := by decide +kernel
  intro t ht
  exact of_decide_eq_true ((List.all_eq_true.mp hc) t ht)

/-- A syntactically homogeneous representative; terms whose differentiated
exponent is zero are deleted before differentiation. -/
def lower (p : RatPoly) : RatPoly :=
  polyFour (polyMul (polyVar 4) (activeDerivative 0 p))
    (polyMul (polyVar 5) (activeDerivative 1 p))
    (polyMul (polyVar 6) (activeDerivative 2 p))
    (polyMul (polyVar 7) (activeDerivative 3 p))

theorem lower_coeff (p : RatPoly) :
    RatPolyCoeffEqv (lower p) (headGradientDot p relativeScalar) := by
  have hi (i : Fin 4) : RatPolyCoeffEqv
      (polyMul (polyVar (4+i.val)) (activeDerivative i.val p))
      (polyMul (ratDerivative i.val p) (ratDerivative i.val relativeScalar)) :=
    ((activeDerivative_coeff i.val p).mul_left _).trans
      ((RatPolyCoeffEqv.mul_comm _ _).trans
        ((relativeScalar_derivative i).symm.mul_left _))
  exact (hi 0).add ((hi 1).add ((hi 2).add (hi 3)))

theorem lower_degree {n : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 (n+1) p) :
    HasQuaternionBlockDegree 0 n (lower p) := by
  have hi (i : Fin 4) : HasQuaternionBlockDegree 0 n
      (polyMul (polyVar (4+i.val)) (activeDerivative i.val p)) :=
    ((retained_coordinate_independent i).mul
      (activeDerivative_degree i.isLt hp)).relabel (by omega)
  exact (hi 0).add ((hi 1).add ((hi 2).add (hi 3)))

private theorem harmonic_add {p q : RatPoly}
    (hp : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hq : RatPolyCoeffEqv (headLaplacian q) polyZero) :
    RatPolyCoeffEqv (headLaplacian (polyAdd p q)) polyZero :=
  (headLaplacian_add p q).trans
    ((hp.add hq).trans (RatPolyCoeffEqv.zero_add polyZero))

theorem lower_harmonic {p : RatPoly}
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv (headLaplacian (lower p)) polyZero := by
  have hi (i : Fin 4) : RatPolyCoeffEqv
      (headLaplacian (polyMul (polyVar (4+i.val)) (activeDerivative i.val p)))
      polyZero :=
    (RatPolyCoeffEqv.mul_comm _ _).headLaplacian.trans
      (harmonic_mul_independent (activeDerivative_harmonic i.val hh)
        (retained_coordinate_independent i))
  exact harmonic_add (hi 0) (harmonic_add (hi 1) (harmonic_add (hi 2) (hi 3)))

theorem gaussian_lowering_step {n : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 (n+1) p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv
      (partialGaussianHead (polyMul p (ratPolyPow relativeScalar (n+1))))
      (partialGaussianHead (polyMul (lower p) (ratPolyPow relativeScalar n))) :=
  (harmonic_power_step hp hh relativeScalar).trans
    (partialGaussianHead_congr ((lower_coeff p).symm.mul_right _))

/-- Explicit finite iteration, not a witness extracted from existence. -/
def lowerIter : Nat → RatPoly → RatPoly
  | 0, p => p
  | n+1, p => lowerIter n (lower p)

theorem lowerIter_degree_zero : ∀ (n : Nat) (p : RatPoly),
    HasQuaternionBlockDegree 0 n p →
    HasQuaternionBlockDegree 0 0 (lowerIter n p)
  | 0, _, hp => hp
  | n+1, p, hp => lowerIter_degree_zero n (lower p) (lower_degree hp)

/-- The Gaussian calculation terminates on an explicit head-independent
polynomial for EVERY degree, retaining all tail coefficients. -/
theorem gaussian_pairing_lowerIter : ∀ (n : Nat) (p : RatPoly),
    HasQuaternionBlockDegree 0 n p →
    RatPolyCoeffEqv (headLaplacian p) polyZero →
    RatPolyCoeffEqv
      (partialGaussianHead (polyMul p (ratPolyPow relativeScalar n)))
      (partialGaussianHead (lowerIter n p))
  | 0, _, _, _ => partialGaussianHead_congr (RatPolyCoeffEqv.mul_one _)
  | n+1, p, hp, hh => (gaussian_lowering_step hp hh).trans
      (gaussian_pairing_lowerIter n (lower p) (lower_degree hp) (lower_harmonic hh))

private theorem gaussian_independent {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 0 p) :
    RatPolyCoeffEqv (partialGaussianHead p) (dropHeadPolynomial p) :=
  (partialGaussianHead_congr (RatPolyCoeffEqv.one_mul p)).symm.trans
    ((partialGaussianHead_mul_independent polyOne p hp).trans
      (((partialGaussianHead_one).mul_right _).trans (RatPolyCoeffEqv.one_mul _)))

/-- Exact all-degree evaluation of the original sphere pairing with (x.y)^n,
up to its explicit radial factor.  No normalization is hidden in the output. -/
theorem haar_pairing_lowerIter (n : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv
      (polySmul (Q'.ofNat (sphereFourDenominator n))
        (partialHaarHead (polyMul p (ratPolyPow relativeScalar n))))
      (dropHeadPolynomial (lowerIter n p)) := by
  have hprod : HasQuaternionBlockDegree 0 (2*n)
      (polyMul p (ratPolyPow relativeScalar n)) :=
    (hp.mul (power_headDegree relativeScalar_headDegree n)).relabel (by omega)
  exact (partialHaarHead_mul_radial n _ hprod).trans
    ((gaussian_pairing_lowerIter n p hp hh).trans
      (gaussian_independent (lowerIter_degree_zero n p hp)))

end YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering

#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.relativeScalar_derivative
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.relativeScalar_headDegree
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.lower_coeff
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.lower_degree
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.lower_harmonic
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.gaussian_lowering_step
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.lowerIter_degree_zero
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.gaussian_pairing_lowerIter
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering.haar_pairing_lowerIter
