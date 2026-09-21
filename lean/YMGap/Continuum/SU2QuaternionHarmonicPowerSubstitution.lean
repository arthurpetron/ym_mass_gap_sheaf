/-
# Exact harmonic power pairing by retained-link substitution

After dropping the integrated head, substitution sends both x_i and y_i
to the same retained variable. Euler's identity therefore identifies one
lowering step with multiplication by the degree. Iteration supplies the
factorial without a multinomial expansion. The explicit radial denominator
then cancels to the exact factor 2^n*(n+1) in the original Haar pairing.
-/

import YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
import YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering
import YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality

namespace YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality (hermiteFactorial)
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation (ratPolyPow)

theorem substitute_lower_euler (p : RatPoly) :
    RatPolyCoeffEqv (substituteRetained (lower p))
      (substituteRetained (headEuler p)) := by
  have hi (i : Fin 4) : RatPolyCoeffEqv
      (substituteRetained (polyMul (polyVar (4+i.val)) (activeDerivative i.val p)))
      (substituteRetained (polyMul (polyVar i.val) (ratDerivative i.val p))) :=
    (substituteRetained_mul _ _).trans
      (((substituteRetained_tail_coordinate i).trans
        (substituteRetained_head_coordinate i).symm).mul
          (substituteRetained_congr (activeDerivative_coeff i.val p)) |>.trans
            (substituteRetained_mul _ _).symm)
  have hfour (a b c d : RatPoly) : RatPolyCoeffEqv
      (substituteRetained (polyFour a b c d))
      (polyFour (substituteRetained a) (substituteRetained b)
        (substituteRetained c) (substituteRetained d)) :=
    (substituteRetained_add _ _).trans
      ((RatPolyCoeffEqv.refl _).add ((substituteRetained_add _ _).trans
        ((RatPolyCoeffEqv.refl _).add (substituteRetained_add _ _))))
  exact (hfour _ _ _ _).trans
    (((hi 0).add ((hi 1).add ((hi 2).add (hi 3)))).trans (hfour _ _ _ _).symm)

/-- Substitution extracts the exact Euler degree, with every tail retained. -/
theorem substitute_lower_degree {n : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p) :
    RatPolyCoeffEqv (substituteRetained (lower p))
      (polySmul (Q'.ofNat n) (substituteRetained p)) :=
  (substitute_lower_euler p).trans
    ((substituteRetained_congr (headEuler_of_blockDegree n p hp)).trans
      (substituteRetained_smul _ _))

theorem factorial_positive : ∀ n, 0 < hermiteFactorial n
  | 0 => by decide
  | n+1 => Nat.mul_pos (by omega) (factorial_positive n)

/-- Reuse the existing constructive factorial and the actual lowering
iteration; no repeated-derivative formula is assumed. -/
theorem substitute_lowerIter : ∀ (n : Nat) (p : RatPoly),
    HasQuaternionBlockDegree 0 n p →
    RatPolyCoeffEqv (substituteRetained (lowerIter n p))
      (polySmul (Q'.ofNat (hermiteFactorial n)) (substituteRetained p))
  | 0, _, _ => (RatPolyCoeffEqv.one_smul _).symm
  | n+1, p, hp =>
      (substitute_lowerIter n (lower p) (lower_degree hp)).trans
        (((substitute_lower_degree hp).smul _).trans
          ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
            (RatPolyCoeffEqv.smul_coefficient
              (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
                (SU3CharFactor.ofNat_mul_eqv (n+1) (hermiteFactorial n))) _)))

/-- At the terminal degree zero, dropping the padded head makes the
substitution identity coefficient-exact. -/
theorem drop_lowerIter (n : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p) :
    RatPolyCoeffEqv (dropHeadPolynomial (lowerIter n p))
      (polySmul (Q'.ofNat (hermiteFactorial n)) (substituteRetained p)) :=
  (substituteRetained_degree_zero (lowerIter_degree_zero n p hp)).symm.trans
    (substitute_lowerIter n p hp)

theorem radial_factorial : ∀ n,
    sphereFourDenominator n = (2^n * (n+1)) * hermiteFactorial n
  | 0 => rfl
  | n+1 => by
      rw [sphereFourDenominator, radial_factorial n, hermiteFactorial, Nat.pow_succ]
      have h : 4+2*n = 2*(n+2) := by omega
      rw [h]
      simp [Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Exact normalized power pairing on the original partial Haar carrier.
The remaining character leading coefficient is not assumed here. -/
theorem harmonic_power_substitution (n : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv
      (polySmul (Q'.ofNat (2^n*(n+1)))
        (partialHaarHead (polyMul p (ratPolyPow relativeScalar n))))
      (substituteRetained p) := by
  let a := Q'.ofNat (hermiteFactorial n)
  have ha : (0 : Q') < a := by
    change (0 : Q') < Q'.ofNat (hermiteFactorial n)
    cases hf : hermiteFactorial n with
    | zero => have := factorial_positive n; omega
    | succ k => exact Q'.ofNat_succ_pos k
  apply coeffEqv_of_positive_smul ha
  have hscale : (a * Q'.ofNat (2^n*(n+1))).eqv
      (Q'.ofNat (sphereFourDenominator n)) := by
    rw [radial_factorial n]
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (SU3CharFactor.ofNat_mul_eqv _ _)
  exact (RatPolyCoeffEqv.smul_assoc _ _ _).trans
    ((RatPolyCoeffEqv.smul_coefficient hscale _).trans
      ((haar_pairing_lowerIter n p hp hh).trans (drop_lowerIter n p hp)))

end YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution

#print axioms YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution.substitute_lower_euler
#print axioms YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution.substitute_lower_degree
#print axioms YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution.substitute_lowerIter
#print axioms YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution.drop_lowerIter
#print axioms YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution.radial_factorial
#print axioms YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution.harmonic_power_substitution
