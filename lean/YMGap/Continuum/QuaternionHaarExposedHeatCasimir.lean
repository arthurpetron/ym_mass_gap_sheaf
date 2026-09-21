/-
# Angular Casimir for every exposed SU(2) heat character

The homogeneous harmonic solid representative has the exact Casimir
eigenvalue `-n(n+2)`.  Tangential differentiation preserves arbitrary-
insertion Haar equality, so the result transports to the ordinary character
used by the finite heat expansion, for every orientation and label.

This is a local generator identity on the finite quaternion Haar carrier.  It
is not an interacting temporal-energy upper bound, a semigroup comparison, or
a continuum spectral-gap statement.
-/

import YMGap.Continuum.QuaternionHaarAngularCasimir
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
import YMGap.Continuum.QuaternionHaarHeatAngularDerivative

namespace YMGap.Continuum.QuaternionHaarExposedHeatCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic

/-- Arbitrary-insertion Haar equality is preserved by the full six-direction
angular Laplacian. -/
theorem angularLaplacian_carrier {blocks : Nat} (hb : 0 < blocks)
    {p q : RatPoly} (h : QuaternionHaarCarrierEqv blocks p q) :
    QuaternionHaarCarrierEqv blocks (angularLaplacian p) (angularLaplacian q) := by
  have hd (i j : Nat) (hi : i < 4) (hj : j < 4) :
      QuaternionHaarCarrierEqv blocks
        (angularDerivative i j (angularDerivative i j p))
        (angularDerivative i j (angularDerivative i j q)) := by
    exact angularDerivative_carrier hb hi hj
      (angularDerivative_carrier hb hi hj h)
  exact QuaternionHaarCarrierEqv.add (hd 0 1 (by decide) (by decide))
    (QuaternionHaarCarrierEqv.add (hd 0 2 (by decide) (by decide))
      (QuaternionHaarCarrierEqv.add (hd 0 3 (by decide) (by decide))
        (QuaternionHaarCarrierEqv.add (hd 1 2 (by decide) (by decide))
          (QuaternionHaarCarrierEqv.add (hd 1 3 (by decide) (by decide))
            (hd 2 3 (by decide) (by decide))))))

/-- Same-carrier Casimir identity on the coefficient-sensitive harmonic solid
mode. -/
theorem exposedSolid_angularCasimir
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    QuaternionHaarCarrierEqv 116
      (angularLaplacian
        (exposedSolidZonalCharacter reverse0 reverse1 reverse2 reverse3 spin))
      (polySmul (-(Q'.ofNat spin * (Q'.ofNat spin + 2)))
        (exposedSolidZonalCharacter reverse0 reverse1 reverse2 reverse3 spin)) := by
  exact harmonic_angularLaplacian (by decide)
    (exposedSolidZonalCharacter reverse0 reverse1 reverse2 reverse3 spin)
    (exposedSolidZonalCharacter_blockDegree
      reverse0 reverse1 reverse2 reverse3 0 (by decide) spin)
    (laplacian_exposedSolidZonalCharacter_zero
      reverse0 reverse1 reverse2 reverse3 spin)

/-- Every ordinary exposed character in the actual finite heat expansion has
the exact label Casimir `-spin(spin+2)` under arbitrary Haar insertion. -/
theorem exposedCharacter_angularCasimir
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    QuaternionHaarCarrierEqv 116
      (angularLaplacian
        (characterPolynomial
          (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar spin))
      (polySmul (-(Q'.ofNat spin * (Q'.ofNat spin + 2)))
        (characterPolynomial
          (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar spin)) := by
  let solid := exposedSolidZonalCharacter reverse0 reverse1 reverse2 reverse3 spin
  let ordinary := characterPolynomial
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar spin
  let eigenvalue := -(Q'.ofNat spin * (Q'.ofNat spin + 2))
  have hc : QuaternionHaarCarrierEqv 116 solid ordinary :=
    exposedSolidZonalCharacter_eq_character_116
      reverse0 reverse1 reverse2 reverse3 spin
  have hlap : QuaternionHaarCarrierEqv 116
      (angularLaplacian solid) (angularLaplacian ordinary) :=
    angularLaplacian_carrier (by decide) hc
  have heigen : QuaternionHaarCarrierEqv 116
      (angularLaplacian solid) (polySmul eigenvalue solid) :=
    exposedSolid_angularCasimir reverse0 reverse1 reverse2 reverse3 spin
  exact QuaternionHaarCarrierEqv.trans (QuaternionHaarCarrierEqv.symm hlap)
    (QuaternionHaarCarrierEqv.trans heigen
      (QuaternionHaarCarrierEqv.smul eigenvalue hc))

private theorem secondAngular_add (i j : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polyAdd p q)))
      (polyAdd (angularDerivative i j (angularDerivative i j p))
        (angularDerivative i j (angularDerivative i j q))) :=
  (angularDerivative_congr i j (angularDerivative_add i j p q)).trans
    (angularDerivative_add i j (angularDerivative i j p) (angularDerivative i j q))

private theorem six_add (f g : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polyAdd (f i j) (g i j)))
      (polyAdd (six f) (six g)) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (by decide) (fun
      | 0 => f 0 1 | 1 => f 0 2 | 2 => f 0 3
      | 3 => f 1 2 | 4 => f 1 3 | 5 => f 2 3
      | 6 => g 0 1 | 7 => g 0 2 | 8 => g 0 3
      | 9 => g 1 2 | 10 => g 1 3 | _ => g 2 3)

private theorem angularLaplacian_add (p q : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polyAdd p q))
      (polyAdd (angularLaplacian p) (angularLaplacian q)) := by
  unfold angularLaplacian
  exact ((secondAngular_add 0 1 p q).add
    ((secondAngular_add 0 2 p q).add
      ((secondAngular_add 0 3 p q).add
        ((secondAngular_add 1 2 p q).add
          ((secondAngular_add 1 3 p q).add (secondAngular_add 2 3 p q)))))).trans
    (six_add
      (fun i j => angularDerivative i j (angularDerivative i j p))
      (fun i j => angularDerivative i j (angularDerivative i j q)))

private theorem secondAngular_smul (i j : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polySmul c p)))
      (polySmul c (angularDerivative i j (angularDerivative i j p))) :=
  (angularDerivative_congr i j (angularDerivative_smul i j c p)).trans
    (angularDerivative_smul i j c (angularDerivative i j p))

private theorem six_smul (c : Q') (f : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polySmul c (f i j))) (polySmul c (six f)) := by
  unfold six
  have h4 : RatPolyCoeffEqv
      (polyAdd (polySmul c (f 1 3)) (polySmul c (f 2 3)))
      (polySmul c (polyAdd (f 1 3) (f 2 3))) :=
    (RatPolyCoeffEqv.smul_add c (f 1 3) (f 2 3)).symm
  have h3 : RatPolyCoeffEqv
      (polyAdd (polySmul c (f 1 2))
        (polyAdd (polySmul c (f 1 3)) (polySmul c (f 2 3))))
      (polySmul c (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3)))) :=
    ((RatPolyCoeffEqv.refl _).add h4).trans
      (RatPolyCoeffEqv.smul_add c (f 1 2) (polyAdd (f 1 3) (f 2 3))).symm
  have h2 : RatPolyCoeffEqv
      (polyAdd (polySmul c (f 0 3))
        (polyAdd (polySmul c (f 1 2))
          (polyAdd (polySmul c (f 1 3)) (polySmul c (f 2 3)))))
      (polySmul c (polyAdd (f 0 3)
        (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3))))) :=
    ((RatPolyCoeffEqv.refl _).add h3).trans
      (RatPolyCoeffEqv.smul_add c (f 0 3)
        (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3)))).symm
  have h1 : RatPolyCoeffEqv
      (polyAdd (polySmul c (f 0 2))
        (polyAdd (polySmul c (f 0 3))
          (polyAdd (polySmul c (f 1 2))
            (polyAdd (polySmul c (f 1 3)) (polySmul c (f 2 3))))))
      (polySmul c (polyAdd (f 0 2) (polyAdd (f 0 3)
        (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3)))))) :=
    ((RatPolyCoeffEqv.refl _).add h2).trans
      (RatPolyCoeffEqv.smul_add c (f 0 2)
        (polyAdd (f 0 3) (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3))))).symm
  exact ((RatPolyCoeffEqv.refl _).add h1).trans
    (RatPolyCoeffEqv.smul_add c (f 0 1)
      (polyAdd (f 0 2) (polyAdd (f 0 3)
        (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3)))))).symm

private theorem angularLaplacian_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polySmul c p))
      (polySmul c (angularLaplacian p)) := by
  unfold angularLaplacian
  exact ((secondAngular_smul 0 1 c p).add
    ((secondAngular_smul 0 2 c p).add
      ((secondAngular_smul 0 3 c p).add
        ((secondAngular_smul 1 2 c p).add
          ((secondAngular_smul 1 3 c p).add (secondAngular_smul 2 3 c p)))))).trans
    (six_smul c (fun i j => angularDerivative i j (angularDerivative i j p)))

private theorem angularLaplacian_finitePolySum {A : Type} (f : A → RatPoly) :
    ∀ xs : List A,
    RatPolyCoeffEqv (angularLaplacian (finitePolySum f xs))
      (finitePolySum (fun a => angularLaplacian (f a)) xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => (angularLaplacian_add (f a) (finitePolySum f xs)).trans
      ((RatPolyCoeffEqv.refl _).add (angularLaplacian_finitePolySum f xs))

private theorem carrier_finitePolySum {A : Type} (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → QuaternionHaarCarrierEqv 116 (f a) (g a)) →
      QuaternionHaarCarrierEqv 116 (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => QuaternionHaarCarrierEqv.refl _ _
  | a :: xs, h => QuaternionHaarCarrierEqv.add (h a List.mem_cons_self)
      (carrier_finitePolySum f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- The finite original heat prefix is sent labelwise to its exact Casimir-
weighted character sum.  The normalization is the repository convention
`spin*(spin+2)`; no positivity, nome, or cutoff guard is used. -/
theorem exposedHeatPrefix_angularCasimir
    (reverse0 reverse1 reverse2 reverse3 : Bool) (w : Q') (K : Nat) :
    let scalar := (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
    QuaternionHaarCarrierEqv 116
      (angularLaplacian (heatPrefix w K scalar))
      (finitePolySum (fun spin =>
        polySmul (coeffW w spin * (-(Q'.ofNat spin * (Q'.ofNat spin + 2))))
          (characterPolynomial scalar spin)) (List.range (K+1))) := by
  let scalar := (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar
  let term : Nat → RatPoly := fun spin =>
    polySmul (coeffW w spin) (characterPolynomial scalar spin)
  let target : Nat → RatPoly := fun spin =>
    polySmul (coeffW w spin * (-(Q'.ofNat spin * (Q'.ofNat spin + 2))))
      (characterPolynomial scalar spin)
  change QuaternionHaarCarrierEqv 116
    (angularLaplacian (finitePolySum term (List.range (K+1))))
    (finitePolySum target (List.range (K+1)))
  have hcommute : QuaternionHaarCarrierEqv 116
      (angularLaplacian (finitePolySum term (List.range (K+1))))
      (finitePolySum (fun spin => angularLaplacian (term spin)) (List.range (K+1))) :=
    RatPolyCoeffEqv.haarCarrier (angularLaplacian_finitePolySum term (List.range (K+1)))
  have hlabel (spin : Nat) : QuaternionHaarCarrierEqv 116
      (angularLaplacian (term spin)) (target spin) := by
    let eigenvalue := -(Q'.ofNat spin * (Q'.ofNat spin + 2))
    exact QuaternionHaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier
        (angularLaplacian_smul (coeffW w spin) (characterPolynomial scalar spin)))
      (QuaternionHaarCarrierEqv.trans
        (QuaternionHaarCarrierEqv.smul (coeffW w spin)
          (exposedCharacter_angularCasimir reverse0 reverse1 reverse2 reverse3 spin))
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.smul_assoc (coeffW w spin) eigenvalue
            (characterPolynomial scalar spin))))
  exact QuaternionHaarCarrierEqv.trans hcommute
    (carrier_finitePolySum (fun spin => angularLaplacian (term spin)) target
      (List.range (K+1)) (fun spin _ => hlabel spin))

end YMGap.Continuum.QuaternionHaarExposedHeatCasimir

#print axioms YMGap.Continuum.QuaternionHaarExposedHeatCasimir.angularLaplacian_carrier
#print axioms YMGap.Continuum.QuaternionHaarExposedHeatCasimir.exposedSolid_angularCasimir
#print axioms YMGap.Continuum.QuaternionHaarExposedHeatCasimir.exposedCharacter_angularCasimir
#print axioms YMGap.Continuum.QuaternionHaarExposedHeatCasimir.exposedHeatPrefix_angularCasimir
