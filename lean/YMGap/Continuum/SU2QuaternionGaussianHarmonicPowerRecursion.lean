/-
# Exact degree-lowering recurrence for harmonic Gaussian pairings

For a head-homogeneous harmonic p of degree n+1, Gaussian Euler/IBP
and the polynomial power rule cancel the positive integer n+1 exactly:

  E[p*l^(n+1)] = E[(grad p . grad l)*l^n].

Every coefficient in the retained variables survives. When l is head-linear,
the existing explicit radial factor converts the left side to the original
partial sphere/Haar integral. These are exact polynomial identities, not an
assumed diagonal reproducing normalization or a spectral estimate.
-/

import YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
import YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

namespace YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation (ratPolyPow)

private theorem gradient_right_congr (p : RatPoly) {l r : RatPoly}
    (h : RatPolyCoeffEqv l r) :
    RatPolyCoeffEqv (headGradientDot p l) (headGradientDot p r) := by
  have hi (i : Nat) := (h.derivative i).mul_left (ratDerivative i p)
  exact (hi 0).add ((hi 1).add ((hi 2).add (hi 3)))

/-- The coefficient-sensitive power rule for the selected gradient. -/
theorem headGradientDot_power (p l : RatPoly) : ∀ n,
    RatPolyCoeffEqv (headGradientDot p (ratPolyPow l (n+1)))
      (polySmul (Q'.ofNat (n+1))
        (polyMul (ratPolyPow l n) (headGradientDot p l)))
  | 0 =>
      (gradient_right_congr p (RatPolyCoeffEqv.one_mul l)).trans
        (((RatPolyCoeffEqv.one_mul _).smul 1).trans
          (RatPolyCoeffEqv.one_smul _)).symm
  | n+1 => by
      let G := headGradientDot p l
      let Z := polyMul (ratPolyPow l (n+1)) G
      have hfirst : RatPolyCoeffEqv
          (polyMul (headGradientDot p (ratPolyPow l (n+1))) l)
          (polySmul (Q'.ofNat (n+1)) Z) :=
        ((headGradientDot_power p l n).mul_right l).trans
          ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
            (((RatPolyCoeffEqv.mul_assoc _ _ _).trans
              (((RatPolyCoeffEqv.mul_comm G l).mul_left (ratPolyPow l n)).trans
                (RatPolyCoeffEqv.mul_assoc _ _ _).symm)).smul _))
      have hscale : (Q'.ofNat (n+1) + 1).eqv (Q'.ofNat (n+1+1)) :=
        Q'.eqv_symm (Q'.ofNat_add_eqv (n+1) 1)
      exact (headGradientDot_mul_right p (ratPolyPow l (n+1)) l).trans
        ((hfirst.add (RatPolyCoeffEqv.one_smul Z).symm).trans
          ((RatPolyCoeffEqv.add_smul_same _ _ Z).trans
            (RatPolyCoeffEqv.smul_coefficient hscale Z)))

/-- One exact downward step, without division on the polynomial carrier.
No linearity assumption on l is needed for this Gaussian identity. -/
theorem harmonic_power_step {n : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 (n+1) p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (l : RatPoly) :
    RatPolyCoeffEqv
      (partialGaussianHead (polyMul p (ratPolyPow l (n+1))))
      (partialGaussianHead (polyMul (headGradientDot p l) (ratPolyPow l n))) := by
  have hz := partialGaussianHead_congr
    ((hh.mul_right (ratPolyPow l (n+1))).trans (RatPolyCoeffEqv.mul_zero_left _))
  have he := (homogeneous_euler_pairing (ratPolyPow l (n+1)) hp hz).trans
    ((partialGaussianHead_congr (headGradientDot_power p l n)).trans
      (partialGaussianHead_smul _ _))
  exact (coeffEqv_of_positive_smul (Q'.ofNat_succ_pos n) he).trans
    (partialGaussianHead_congr (RatPolyCoeffEqv.mul_comm _ _))

theorem power_headDegree {l : RatPoly} (hl : HasQuaternionBlockDegree 0 1 l) :
    ∀ n, HasQuaternionBlockDegree 0 n (ratPolyPow l n)
  | 0 => hasQuaternionBlockDegree_one 0
  | n+1 => (power_headDegree hl n).mul hl

/-- The same downward step starting from the ORIGINAL partial sphere/Haar
pairing, with its explicit positive natural radial denominator retained. -/
theorem harmonic_haar_power_step {n : Nat} {p l : RatPoly}
    (hp : HasQuaternionBlockDegree 0 (n+1) p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hl : HasQuaternionBlockDegree 0 1 l) :
    RatPolyCoeffEqv
      (polySmul (Q'.ofNat (sphereFourDenominator (n+1)))
        (partialHaarHead (polyMul p (ratPolyPow l (n+1)))))
      (partialGaussianHead (polyMul (headGradientDot p l) (ratPolyPow l n))) := by
  have hprod : HasQuaternionBlockDegree 0 (2*(n+1))
      (polyMul p (ratPolyPow l (n+1))) :=
    (hp.mul (power_headDegree hl (n+1))).relabel (by omega)
  exact (partialHaarHead_mul_radial (n+1) _ hprod).trans
    (harmonic_power_step hp hh l)

end YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion

#print axioms YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion.headGradientDot_power
#print axioms YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion.harmonic_power_step
#print axioms YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion.power_headDegree
#print axioms YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion.harmonic_haar_power_step
