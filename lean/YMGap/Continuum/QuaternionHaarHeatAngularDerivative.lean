/-
# Cutoff-independent angular derivative certificates for heat prefixes

The character derivative is bounded in original Haar polynomial order by
a cubic label budget. Multiplication by the actual heat coefficient leaves
the existing quartic Gaussian series, whose finite head and geometric tail
give an explicit cap at each strict nome.

The input bound for the derivative of the original scalar remains explicit.
In particular, this file does not construct the selected-link plaquette
derivative certificate, a Ward response floor, or a nome-uniform score bound.
-/

import YMGap.Continuum.QuaternionHaarCharacterDerivative
import YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
import YMGap.Continuum.SU2HeatQuarticPrefixBound

namespace YMGap.Continuum.QuaternionHaarHeatAngularDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.SU2CharacterDerivativeCubicBudget
open YMGap.Continuum.QuaternionHaarCharacterDerivative
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate (heatTerm prefixInterval)
open YMGap.Continuum.SU2HeatQuarticPrefixBound

local infix:50 " ≈ " => Q'.eqv

/-- Angular differentiation commutes with every finite polynomial sum. -/
theorem angularDerivative_finitePolySum {A : Type} (i j : Nat) (f : A → RatPoly) :
    ∀ ids : List A,
    RatPolyCoeffEqv (angularDerivative i j (finitePolySum f ids))
      (finitePolySum (fun a => angularDerivative i j (f a)) ids)
  | [] => RatPolyCoeffEqv.refl _
  | a :: ids => (angularDerivative_add i j (f a) (finitePolySum f ids)).trans
      ((RatPolyCoeffEqv.refl _).add (angularDerivative_finitePolySum i j f ids))

private theorem fourth_nat (a : Nat) :
    Q'.ofNat (a^4) ≈ ((Q'.ofNat a * Q'.ofNat a) * Q'.ofNat a) * Q'.ofNat a := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  exact Q'.eqv_trans _ _ _ (ofNat_mul_eqv (a*a*a) a)
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (ofNat_mul_eqv (a*a) a)
        (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv a a))))

private theorem quartic_rearrange (a q d : Q') :
    (a*q)*((2*(a*a*a))*d) ≈ (2*d)*((a*a*a*a)*q) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.mul (.const 2) (.mul (.mul (.var 0) (.var 0)) (.var 0))) (.var 2)))
    (.mul (.mul (.const 2) (.var 2))
      (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 0)) (.var 1)))
    (by decide) (fun | 0 => a | 1 => q | _ => d)

/-- Exact quartic-label pin, including the actual representation dimension
already present in the original heat coefficient. -/
theorem heat_derivative_budget_pin (w d : Q') (n : Nat) :
    coeffW w n * (cubicBudget n * d) ≈ (2*d) * tailTerm w 4 n :=
  Q'.eqv_trans _ _ _ (quartic_rearrange (dimQ n) (RGTransport.qpow w (c4 n)) d)
    (Q'.mul_eqv_congr_left (2*d) _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (fourth_nat (n+1)))))

/-- One differentiated heat term in the original Haar order. -/
def heatDerivativeTermInterval {blocks i j : Nat} {x : RatPoly} {d w : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (hw : (0 : Q') ≤ w)
    (X : SquareBound blocks x 1) (DX : Interval blocks (angularDerivative i j x) d)
    (n : Nat) :
    Interval blocks (angularDerivative i j (heatTerm w x n)) ((2*d)*tailTerm w 4 n) :=
  (Interval.ofCoeff
    (angularDerivative_supported hb hi hj
      (((sharpCharacterInterval X n).smul (coeffW w n) (coeffW_nonneg hw n)).support))
    (angularDerivative_smul i j (coeffW w n) (characterPolynomial x n))
    ((angularDerivativeCharacterInterval hb hi hj X DX n).smul (coeffW w n) (coeffW_nonneg hw n)))
      |>.changeCap (heat_derivative_budget_pin w d n)

/-- Explicit derivative cap: cutoff-independent at each strict nome, but
dependent on the nome and the supplied original scalar-derivative cap. -/
def heatDerivativeCap (w d : Q') : Q' := (2*d)*prefixBudget w

/-- The actual heat-prefix angular derivative, not a separately assigned
derivative polynomial, has this constructed two-sided Haar certificate. -/
def heatPrefixAngularInterval {blocks i j : Nat} {x : RatPoly} {d w : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (X : SquareBound blocks x 1) (DX : Interval blocks (angularDerivative i j x) d)
    (K : Nat) :
    Interval blocks (angularDerivative i j (heatPrefix w K x)) (heatDerivativeCap w d) := by
  refine Interval.ofCoeff
    (angularDerivative_supported hb hi hj (prefixInterval hw0 hw1 X K).support)
    (angularDerivative_finitePolySum i j (heatTerm w x) (List.range (K+1))) ?_
  refine (Interval.finiteRange (fun n => angularDerivative i j (heatTerm w x n))
    (fun n => (2*d)*tailTerm w 4 n)
    (heatDerivativeTermInterval hb hi hj (Q'.le_of_lt hw0) X DX) (K+1)).weaken ?_
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (const_mul_finSum (tailTerm w 4) (2*d) (K+1)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (prefix_bound hw0 hw1 (K+1))
      (Q'.mul_nonneg _ _ (by decide) DX.nonnegative))

/-- The cutoff-independent cap is valid against any original positive
background, including backgrounds sharing every variable of the prefix. -/
theorem heatPrefix_angular_weighted_bound {blocks i j : Nat} {x r : RatPoly} {d w : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (X : SquareBound blocks x 1) (DX : Interval blocks (angularDerivative i j x) d)
    (R : Certificate blocks r) (K : Nat) :
    Q'.abs (quaternionHaar blocks (polyMul r (angularDerivative i j (heatPrefix w K x)))) ≤
      heatDerivativeCap w d * quaternionHaar blocks r :=
  (heatPrefixAngularInterval hb hi hj hw0 hw1 X DX K).weighted_haar_bound R

end YMGap.Continuum.QuaternionHaarHeatAngularDerivative

#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDerivative.angularDerivative_finitePolySum
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDerivative.heat_derivative_budget_pin
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDerivative.heatDerivativeTermInterval
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDerivative.heatDerivativeCap
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDerivative.heatPrefixAngularInterval
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDerivative.heatPrefix_angular_weighted_bound
