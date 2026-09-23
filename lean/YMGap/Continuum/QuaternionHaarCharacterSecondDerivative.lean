/- # Mixed angular second derivatives of the actual SU(2) characters -/

import YMGap.Continuum.QuaternionHaarCharacterDerivative

namespace YMGap.Continuum.QuaternionHaarCharacterSecondDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarCharacterDerivative
open YMGap.Continuum.SU2CharacterDerivativeCubicBudget

local infix:50 " ≈ " => Q'.eqv

private theorem nat_fourth (b : Nat) :
    Q'.ofNat (b^4) ≈ ((Q'.ofNat b * Q'.ofNat b) * Q'.ofNat b) * Q'.ofNat b := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  exact Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv (b*b*b) b)
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv (b*b) b)
        (Q'.mul_eqv_congr_right _ _ _ (HeatKernelRGStep.ofNat_mul_eqv b b))))

/-- Exact positive cap recurrence for one angular derivative of `U'_n`. -/
def derivativeAngularCap (d : Q') : Nat → Q'
  | 0 => 0
  | 1 => 0
  | n+2 => derivativeAngularCap d n +
      2 * (Q'.ofNat (n+2) * (cubicBudget (n+1) * d))

private theorem degreeFive_step (n : Nat) :
    (n+1)^5 + (n+2)^4 ≤ (n+3)^5 := by
  have h13 : n+1 ≤ n+3 := by omega
  have h23 : n+2 ≤ n+3 := by omega
  have hpow4 : (n+1)^4 ≤ (n+3)^4 := Nat.pow_le_pow_left h13 4
  have hpow1 : (n+1)^5 ≤ (n+3)^4 * (n+2) := by
    simpa [Nat.pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul hpow4 (show n+1 ≤ n+2 by omega)
  have hpow2 : (n+2)^4 ≤ (n+3)^4 := Nat.pow_le_pow_left h23 4
  calc
    (n+1)^5 + (n+2)^4 ≤ (n+3)^4 * (n+2) + (n+3)^4 :=
      Nat.add_le_add hpow1 hpow2
    _ = (n+3)^4 * (n+3) := by
      simpa only [Nat.add_assoc] using (Nat.mul_succ ((n+3)^4) (n+2)).symm
    _ = (n+3)^5 := by simp [Nat.pow_succ, Nat.mul_comm]

/-- Closed degree-five domination of the recursive derivative-polynomial
cap.  This is the cutoff-independent form consumed by subsequent heat sums. -/
theorem derivativeAngularCap_le_quintic (d : Q') (hd : (0 : Q') ≤ d) :
    ∀ n : Nat, derivativeAngularCap d n ≤
      (4 * Q'.ofNat ((n+1)^5)) * d
  | 0 => by
      unfold derivativeAngularCap
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) (HeatKernelRGStep.zero_le_ofNat _)) hd
  | 1 => by
      unfold derivativeAngularCap
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) (HeatKernelRGStep.zero_le_ofNat _)) hd
  | n+2 => by
      have ih := derivativeAngularCap_le_quintic d hd n
      have hn := Q'.ofNat_le_ofNat (degreeFive_step n)
      have hscale := Q'.mul_le_mul_of_nonneg_right _ _ d
        (Q'.mul_le_mul_of_nonneg_left _ _ 4 hn (by decide)) hd
      have hpin : (4 * Q'.ofNat ((n+1)^5))*d +
          2*(Q'.ofNat (n+2)*(cubicBudget (n+1)*d)) ≈
          (4 * Q'.ofNat ((n+1)^5+(n+2)^4))*d := by
        refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
            (.add (.mul (.mul (.const 4) (.var 0)) (.var 2))
              (.mul (.const 2) (.mul (.var 1)
                (.mul (.mul (.const 2) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.var 2)))))
            (.mul (.mul (.const 4) (.add (.var 0)
              (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)))) (.var 2))
            (by decide)
            (fun | 0 => Q'.ofNat ((n+1)^5) | 1 => Q'.ofNat (n+2) | _ => d)) ?_
        exact Q'.mul_eqv_congr_right _ _ d (Q'.mul_eqv_congr_left 4 _ _
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (nat_fourth (n+2))))
            (Q'.eqv_symm (Q'.ofNat_add_eqv _ _))))
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ih)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) hscale)

private def constantDerivativeInterval {blocks i j : Nat}
    (hi : i < 4*blocks) (hj : j < 4*blocks) (c : Q') (hc : (0 : Q') ≤ c) :
    Interval blocks (angularDerivative i j (cap c)) 0 := by
  refine Interval.ofCoeff
    (angularDerivative_supported_at hi hj (Interval.constant blocks c hc).support)
    ?_ (Interval.zero blocks)
  exact (angularDerivative_smul i j c polyOne).trans
    (((angularDerivative_one i j).smul c).trans (RatPolyCoeffEqv.smul_zero c))

private def derivativeMulInterval {blocks i j : Nat} {p q : RatPoly}
    {a b da db : Q'} (hi : i < 4*blocks) (hj : j < 4*blocks)
    (P : Interval blocks p a) (Q : Interval blocks q b)
    (DP : Interval blocks (angularDerivative i j p) da)
    (DQ : Interval blocks (angularDerivative i j q) db) :
    Interval blocks (angularDerivative i j (polyMul p q)) (da*b+a*db) :=
  Interval.ofCoeff (angularDerivative_supported_at hi hj (P.mul Q).support)
    (angularDerivative_mul i j p q) ((DP.mul Q).add (P.mul DQ))

/-- The mixed-coordinate derivative of the actual positive derivative
polynomial.  The cap is cutoff-free and follows its parity recurrence. -/
def derivativePolynomialAngularIntervalAt {blocks i j : Nat} {x : RatPoly}
    {d : Q'} (hi : i < 4*blocks) (hj : j < 4*blocks)
    (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d) : ∀ n : Nat,
    Interval blocks (angularDerivative i j (derivativePolynomial x n))
      (derivativeAngularCap d n)
  | 0 => by
      simpa only [derivativePolynomial, derivativeAngularCap] using
        constantDerivativeInterval hi hj 0 (Q'.le_refl' _)
  | 1 => by
      simpa only [derivativePolynomial, derivativeAngularCap] using
        constantDerivativeInterval hi hj 2 (by decide)
  | n+2 => by
      let C2 := Interval.constant blocks 2 (by decide)
      let CN := Interval.constant blocks (Q'.ofNat (n+2))
        (HeatKernelRGStep.zero_le_ofNat _)
      let Ch := sharpCharacterInterval X (n+1)
      let D2 := constantDerivativeInterval hi hj 2 (by decide)
      let DN := constantDerivativeInterval hi hj (Q'.ofNat (n+2))
        (HeatKernelRGStep.zero_le_ofNat _)
      let Dh := angularDerivativeCharacterIntervalAt hi hj X DX (n+1)
      let inner := derivativeMulInterval hi hj CN Ch DN Dh
      let outer := derivativeMulInterval hi hj C2 (CN.mul Ch) D2 inner
      have outer' := outer.changeCap (poly_identity_of_normal_eq
        (.add (.mul (.const 0) (.mul (.var 0) (.var 1)))
          (.mul (.const 2) (.add (.mul (.const 0) (.var 1))
            (.mul (.var 0) (.var 2)))))
        (.mul (.const 2) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => Q'.ofNat (n+2) | 1 => RGTransport.dimQ (n+1) | _ => cubicBudget (n+1)*d))
      refine Interval.ofCoeff
        (angularDerivative_supported_at hi hj
          ((derivativePolynomialInterval X n).add (C2.mul (CN.mul Ch))).support)
        ((angularDerivative_add i j _ _).trans ?_)
        ((derivativePolynomialAngularIntervalAt hi hj X DX n).add outer')
      exact RatPolyCoeffEqv.refl _

/-- Mixed angular second derivative of the actual character polynomial.
Both derivatives of the supplied scalar are retained explicitly. -/
def angularSecondDerivativeCharacterIntervalAt
    {blocks i j k l : Nat} {x : RatPoly} {dij dkl mixed : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (hk : k < 4*blocks) (hl : l < 4*blocks)
    (X : SquareBound blocks x 1)
    (Dij : Interval blocks (angularDerivative i j x) dij)
    (Dkl : Interval blocks (angularDerivative k l x) dkl)
    (Dmixed : Interval blocks
      (angularDerivative i j (angularDerivative k l x)) mixed)
    (n : Nat) :
    Interval blocks
      (angularDerivative i j (angularDerivative k l (characterPolynomial x n)))
      (derivativeAngularCap dij n * dkl + cubicBudget n * mixed) := by
  let P := derivativePolynomialInterval X n
  let DP := derivativePolynomialAngularIntervalAt hi hj X Dij n
  let H := derivativeMulInterval hi hj P Dkl DP Dmixed
  exact Interval.ofCoeff
    (angularDerivative_supported_at hi hj
      (angularDerivative_supported_at hk hl (character_squareBound X n).support))
    (angularDerivative_congr i j
      (angularDerivative_character_at k l x n)) H

end YMGap.Continuum.QuaternionHaarCharacterSecondDerivative

#print axioms YMGap.Continuum.QuaternionHaarCharacterSecondDerivative.derivativeAngularCap_le_quintic
#print axioms YMGap.Continuum.QuaternionHaarCharacterSecondDerivative.derivativePolynomialAngularIntervalAt
#print axioms YMGap.Continuum.QuaternionHaarCharacterSecondDerivative.angularSecondDerivativeCharacterIntervalAt
