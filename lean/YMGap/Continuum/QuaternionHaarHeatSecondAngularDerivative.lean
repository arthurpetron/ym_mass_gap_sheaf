/-
# Cutoff-independent mixed angular derivatives of the ORIGINAL heat prefix

The positive lower-character recurrence bounds a differentiated character
derivative by a quintic label budget. The actual representation dimension
therefore gives degree-six and degree-four Gaussian sums. Their explicit
budgets depend on the nome, not on cutoff or ambient carrier size.

This is a local derivative producer for a kinetic curvature estimate, not
a normalized joint score estimate or a physical mass-gap statement.
-/

import YMGap.Continuum.QuaternionHaarCharacterSecondDerivative
import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.SU2HeatPolynomialPrefixBound

namespace YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterDerivative
open YMGap.Continuum.QuaternionHaarCharacterSecondDerivative
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate (heatTerm prefixInterval)
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative
open YMGap.Continuum.SU2CharacterDerivativeCubicBudget

local infix:50 " ≈ " => Q'.eqv

private theorem dim_power (n m : Nat) :
    dimQ n * Q'.ofNat ((n+1)^m) ≈ Q'.ofNat ((n+1)^(m+1)) := by
  rw [Nat.pow_succ]
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.eqv_symm (ofNat_mul_eqv _ _))

private theorem term_pin (w d e f : Q') (n : Nat) :
    coeffW w n * (((4*Q'.ofNat ((n+1)^5))*d)*e + cubicBudget n*f) ≈
      (4*d*e)*tailTerm w 6 n + (2*f)*tailTerm w 4 n := by
  have left : coeffW w n * (((4*Q'.ofNat ((n+1)^5))*d)*e) ≈
      (4*d*e)*tailTerm w 6 n := by
    refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.mul (.mul (.const 4) (.var 2)) (.var 3)) (.var 4)))
      (.mul (.mul (.mul (.const 4) (.var 3)) (.var 4))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))) (by decide)
      (fun
        | 0 => dimQ n
        | 1 => qpow w (c4 n)
        | 2 => Q'.ofNat ((n+1)^5)
        | 3 => d
        | _ => e)) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (dim_power n 5))
  exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
    (Q'.add_eqv_congr' left (heat_derivative_budget_pin w f n))

/-- Explicit mixed derivative cap; no uniformity as `w` approaches one is asserted. -/
def heatSecondDerivativeCap (w d e f : Q') : Q' :=
  (4*d*e)*SU2HeatPolynomialPrefixBound.prefixBudget w 6 +
    (2*f)*SU2HeatPolynomialPrefixBound.prefixBudget w 4

/-- One original character term with explicit degree-six and degree-four
budgets, also usable for constructive mixed-derivative tail estimates. -/
def heatSecondTermInterval {blocks i j k l : Nat} {x : RatPoly}
    {d e f w : Q'} (hi : i < 4*blocks) (hj : j < 4*blocks)
    (hk : k < 4*blocks) (hl : l < 4*blocks) (hw : (0 : Q') ≤ w)
    (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d)
    (EX : Interval blocks (angularDerivative k l x) e)
    (FX : Interval blocks (angularDerivative i j (angularDerivative k l x)) f)
    (n : Nat) :
    Interval blocks (angularDerivative i j (angularDerivative k l (heatTerm w x n)))
      ((4*d*e)*tailTerm w 6 n + (2*f)*tailTerm w 4 n) := by
  let B := angularSecondDerivativeCharacterIntervalAt hi hj hk hl X DX EX FX n
  have hg := Q'.add_le_add_right _ _ (cubicBudget n*f)
    (Q'.mul_le_mul_of_nonneg_right _ _ e
      (derivativeAngularCap_le_quintic d DX.nonnegative n) EX.nonnegative)
  let C := (B.weaken hg).smul (coeffW w n) (coeffW_nonneg hw n)
  refine (Interval.ofCoeff
    (angularDerivative_supported_at hi hj (angularDerivative_supported_at hk hl
      (((QuaternionHaarSharpCharacterInterval.sharpCharacterInterval X n).smul
        (coeffW w n) (coeffW_nonneg hw n)).support)))
    ((angularDerivative_congr i j (angularDerivative_smul k l (coeffW w n) _)).trans
      (angularDerivative_smul i j (coeffW w n) _)) C).changeCap (term_pin w d e f n)

/-- The actual mixed second derivative has a constructed Haar interval at
every finite cutoff. Both scalar derivatives and their mixed derivative are
explicit inputs; the relative-quaternion consumer constructs them. -/
def heatPrefixSecondAngularIntervalAt {blocks i j k l : Nat} {x : RatPoly}
    {d e f w : Q'} (hi : i < 4*blocks) (hj : j < 4*blocks)
    (hk : k < 4*blocks) (hl : l < 4*blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d)
    (EX : Interval blocks (angularDerivative k l x) e)
    (FX : Interval blocks (angularDerivative i j (angularDerivative k l x)) f)
    (K : Nat) :
    Interval blocks (angularDerivative i j (angularDerivative k l (heatPrefix w K x)))
      (heatSecondDerivativeCap w d e f) := by
  refine Interval.ofCoeff
    (angularDerivative_supported_at hi hj
      (angularDerivative_supported_at hk hl (prefixInterval hw0 hw1 X K).support))
    ((angularDerivative_congr i j
      (angularDerivative_finitePolySum k l (heatTerm w x) (List.range (K+1)))).trans
        (angularDerivative_finitePolySum i j _ (List.range (K+1)))) ?_
  refine (Interval.finiteRange _ _
    (heatSecondTermInterval hi hj hk hl (Q'.le_of_lt hw0) X DX EX FX) (K+1)).weaken ?_
  have hsum : finSum (fun n => (4*d*e)*tailTerm w 6 n + (2*f)*tailTerm w 4 n) (K+1) ≈
      (4*d*e)*finSum (tailTerm w 6) (K+1) + (2*f)*finSum (tailTerm w 4) (K+1) :=
    Q'.eqv_trans _ _ _ (finSum_add _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_symm (const_mul_finSum _ _ _))
        (Q'.eqv_symm (const_mul_finSum _ _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (SU2HeatPolynomialPrefixBound.prefix_bound hw0 hw1 6 (K+1))
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) DX.nonnegative) EX.nonnegative))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (SU2HeatPolynomialPrefixBound.prefix_bound hw0 hw1 4 (K+1))
        (Q'.mul_nonneg _ _ (by decide) FX.nonnegative)))

end YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative

#print axioms YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative.heatSecondDerivativeCap
#print axioms YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative.heatSecondTermInterval
#print axioms YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative.heatPrefixSecondAngularIntervalAt
