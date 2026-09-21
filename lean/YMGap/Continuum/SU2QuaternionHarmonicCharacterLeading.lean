/-
# Exact leading character coefficient in a harmonic Haar pairing

The ordinary character recurrence and harmonic lower-degree annihilation
leave only 2^n times the leading power at the matching degree. The proof
retains arbitrary polynomial coefficients in the unintegrated variables;
neither physical link is fixed and no sphere relation for the tail is needed.
-/

import YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.SU2QuaternionHarmonicCharacterLeading

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
open YMGap.Continuum.SU2QuaternionGaussianHarmonicPowerRecursion
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation (ratPolyPow)

private def pair (p q : RatPoly) : RatPoly := partialHaarHead (polyMul p q)

private theorem pair_congr (p : RatPoly) {q r : RatPoly} (h : RatPolyCoeffEqv q r) :
    RatPolyCoeffEqv (pair p q) (pair p r) := partialHaarHead_congr (h.mul_left p)

private theorem pair_add (p q r : RatPoly) :
    RatPolyCoeffEqv (pair p (polyAdd q r)) (polyAdd (pair p q) (pair p r)) := by
  have h := partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right p q r)
  rw [partialHaarHead_add] at h
  exact h

private theorem pair_smul (p q : RatPoly) (a : Q') :
    RatPolyCoeffEqv (pair p (polySmul a q)) (polySmul a (pair p q)) :=
  (partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_right a p q)).trans
    (partialHaarHead_smul a _)

private theorem shifted_character_step (l : RatPoly) (n k : Nat) :
    RatPolyCoeffEqv (polyMul (ratPolyPow l k) (characterPolynomial l (n+2)))
      (polyAdd
        (polySmul 2 (polyMul (ratPolyPow l (k+1)) (characterPolynomial l (n+1))))
        (polySmul (-1) (polyMul (ratPolyPow l k) (characterPolynomial l n)))) := by
  change RatPolyCoeffEqv
    (polyMul (ratPolyPow l k) (polyAdd
      (polyMul (polySmul 2 l) (characterPolynomial l (n+1)))
      (polySmul (-1) (characterPolynomial l n)))) _
  apply (RatPolyCoeffEqv.mul_add_right _ _ _).trans
  apply RatPolyCoeffEqv.add
  · exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      (((RatPolyCoeffEqv.polyMul_smul_right 2 (ratPolyPow l k) l).mul_right _).trans
        (RatPolyCoeffEqv.polyMul_smul_left 2 _ _))
  · exact RatPolyCoeffEqv.polyMul_smul_right (-1) _ _

private theorem twice_power (n : Nat) :
    ((2 : Q') * Q'.ofNat (2^n)).eqv (Q'.ofNat (2^(n+1))) := by
  rw [Nat.pow_succ, Nat.mul_comm (2^n) 2]
  exact SU3CharFactor.ofNat_mul_eqv 2 (2^n)

/-- A power-shifted character of total degree at most the harmonic degree
has only its leading-power contribution. The strict lower-degree case is
included to close the actual three-term character recurrence. -/
theorem harmonic_character_power {d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 d p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    ∀ (n k : Nat), n+k ≤ d →
      RatPolyCoeffEqv
        (pair p (polyMul (ratPolyPow relativeScalar k) (relativeCharacter n)))
        (polySmul (Q'.ofNat (2^n)) (pair p (ratPolyPow relativeScalar (k+n))))
  | 0, k, _ => (pair_congr p (RatPolyCoeffEqv.mul_one _)).trans
      (RatPolyCoeffEqv.one_smul _).symm
  | 1, k, _ =>
      (pair_congr p (RatPolyCoeffEqv.polyMul_smul_right 2 _ relativeScalar)).trans
        (pair_smul p _ 2)
  | n+2, k, hkd => by
      have hfirst := harmonic_character_power hp hh (n+1) (k+1) (by omega)
      have hlower := harmonic_character_power hp hh n k (by omega)
      have hz := partialHaarHead_harmonic_lower_degree hp hh
        (power_headDegree relativeScalar_headDegree (k+n)) (by omega : k+n < d)
      have hsecond : RatPolyCoeffEqv
          (pair p (polyMul (ratPolyPow relativeScalar k) (relativeCharacter n))) polyZero :=
        hlower.trans ((hz.smul _).trans (RatPolyCoeffEqv.smul_zero _))
      have heq : k+1+(n+1) = k+(n+2) := by omega
      rw [heq] at hfirst
      have hsplit := (pair_congr p (shifted_character_step relativeScalar n k)).trans
        ((pair_add p _ _).trans ((pair_smul p _ 2).add (pair_smul p _ (-1))))
      have hleft := (hfirst.smul 2).trans
        ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
          (RatPolyCoeffEqv.smul_coefficient (twice_power (n+1)) _))
      exact hsplit.trans
        ((hleft.add ((hsecond.smul (-1)).trans (RatPolyCoeffEqv.smul_zero (-1)))).trans
          (RatPolyCoeffEqv.add_zero _))

/-- The actual ordinary character at matching degree, not its solid
surrogate, with exact leading coefficient and no retained-link constraint. -/
theorem harmonic_character_leading (n : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv (partialHaarHead (polyMul p (relativeCharacter n)))
      (polySmul (Q'.ofNat (2^n))
        (partialHaarHead (polyMul p (ratPolyPow relativeScalar n)))) := by
  have h := harmonic_character_power hp hh n 0 (by omega)
  simp only [Nat.zero_add] at h
  exact (pair_congr p (RatPolyCoeffEqv.one_mul _)).symm.trans h

end YMGap.Continuum.SU2QuaternionHarmonicCharacterLeading

#print axioms YMGap.Continuum.SU2QuaternionHarmonicCharacterLeading.harmonic_character_power
#print axioms YMGap.Continuum.SU2QuaternionHarmonicCharacterLeading.harmonic_character_leading
