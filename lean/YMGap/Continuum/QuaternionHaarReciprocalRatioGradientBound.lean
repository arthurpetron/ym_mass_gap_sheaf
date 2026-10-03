/-
# Degree-uniform first derivative of the actual reciprocal ratio

The relative certificates C*A plus/minus b and the certified sensitivity
0 <= A^2*slope <= 1 control the differentiated finite ratio without
dividing by a lower terminal floor. All three square forms use the SAME
certified background W. The estimate is uniform only in reciprocal degree;
the actual A, b, W and their derivatives remain in its right hand side.
-/

import YMGap.Continuum.QuaternionHaarReciprocalSensitivity
import YMGap.Continuum.QuaternionHaarWeightedSquareTriangle

namespace YMGap.Continuum.QuaternionHaarReciprocalRatioGradientBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Relative signed source control applies to any certified multiplier.
No inverse, positivity floor, or pointwise division is part of this rule. -/
def relative_multiplier_square_certificate {blocks : Nat} {A b J : RatPoly} {C : Q'}
    (hJ : SupportedQuaternionBlocks blocks J) (hC : (0 : Q') ≤ C)
    (Splus : Certificate blocks (polyAdd (polyMul (cap C) A) b))
    (Sminus : Certificate blocks (polyAdd (polyMul (cap C) A) (polyNeg b)))
    (M : Certificate blocks (polyAdd polyOne
      (polyNeg (polyMul (polyMul A J) (polyMul A J))))) :
    Certificate blocks (gap (C*C) (polyMul J b)) := by
  have hcap : Certificate blocks (polyMul (cap C) (cap C)) :=
    Certificate.ofCoeff (cap_mul C C)
      (Certificate.constant blocks (C*C) (Q'.mul_nonneg _ _ hC hC))
  have hid : RatPolyCoeffEqv (gap (C*C) (polyMul J b))
      (polyAdd
        (polyMul (polyMul J J)
          (polyMul (polyAdd (polyMul (cap C) A) b)
            (polyAdd (polyMul (cap C) A) (polyNeg b))))
        (polyMul (polyMul (cap C) (cap C))
          (polyAdd polyOne (polyNeg (polyMul (polyMul A J) (polyMul A J)))))) := by
    refine ((cap_mul C C).symm.add (RatPolyCoeffEqv.refl _)).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 0))
        (.neg (.mul (.mul (.var 3) (.var 2)) (.mul (.var 3) (.var 2)))))
      (.add
        (.mul (.mul (.var 3) (.var 3))
          (.mul (.add (.mul (.var 0) (.var 1)) (.var 2))
            (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))))
        (.mul (.mul (.var 0) (.var 0))
          (.add (.const 1) (.neg
            (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3)))))))
      (by decide) (fun | 0 => cap C | 1 => A | 2 => b | _ => J)
  exact Certificate.ofCoeff hid
    (((Certificate.square J hJ).mul (Splus.mul Sminus)).add (hcap.mul M))

private theorem weighted_multiplier_square_le {blocks : Nat} {W p r : RatPoly} {c : Q'}
    (M : Certificate blocks W) (P : Certificate blocks (gap c p))
    (hr : SupportedQuaternionBlocks blocks r) :
    quaternionHaar blocks (polyMul W (polyMul (polyMul p r) (polyMul p r))) ≤
      c * quaternionHaar blocks (polyMul W (polyMul r r)) := by
  let B := polyMul W (polyMul r r)
  let E := polyMul B (gap c p)
  have hn : (0 : Q') ≤ quaternionHaar blocks E :=
    ((M.mul (Certificate.square r hr)).mul P).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W (polyMul (polyMul p r) (polyMul p r))) E)
      (polyMul (cap c) B) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2)))
          (.add (.var 3) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.var 3) (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => W | 1 => p | 2 => r | _ => cap c)
  have he :
      quaternionHaar blocks (polyMul W (polyMul (polyMul p r) (polyMul p r))) +
          quaternionHaar blocks E ≈ c * quaternionHaar blocks B :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left c B)))
        (quaternionHaar_polySmul blocks c B))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- Exact cleared Leibniz rule for the literal finite reciprocal. -/
theorem reciprocal_ratio_cleared_derivative (i j : Nat) (A b : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv
      (polyMul A (angularDerivative i j (polyMul (reciprocal A u hu k) b)))
      (polyAdd
        (polyMul (polyMul A (reciprocal A u hu k)) (angularDerivative i j b))
        (polyNeg (polyMul (polyMul (polyMul A (reciprocalSlope A u hu k)) b)
          (angularDerivative i j A)))) := by
  have hd := (angularDerivative_mul i j (reciprocal A u hu k) b).trans
    (((reciprocal_angularDerivative i j A u hu k).mul_right b).add
      (RatPolyCoeffEqv.refl _))
  refine (hd.mul_left A).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add
      (.mul (.neg (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.var 4) (.var 5))))
    (.add (.mul (.mul (.var 0) (.var 4)) (.var 5))
      (.neg (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2))))
    (by decide)
    (fun
      | 0 => A
      | 1 => reciprocalSlope A u hu k
      | 2 => angularDerivative i j A
      | 3 => b
      | 4 => reciprocal A u hu k
      | _ => angularDerivative i j b)

/-- Same-weight bound, uniform in k, with the actual source derivatives retained.
Only 0<=A<=u is needed: there is no lower-window hypothesis or cost factor. -/
theorem reciprocal_ratio_cleared_gradient_square_le
    {blocks i j : Nat} {W A b : RatPoly} {u C : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (M : Certificate blocks W)
    (hA : SupportedQuaternionBlocks blocks A)
    (hb : SupportedQuaternionBlocks blocks b)
    (hu : (0 : Q') < u)
    (hC : (0 : Q') ≤ C)
    (P : Certificate blocks A)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (Splus : Certificate blocks (polyAdd (polyMul (cap C) A) b))
    (Sminus : Certificate blocks (polyAdd (polyMul (cap C) A) (polyNeg b)))
    (k : Nat) :
    let d := polyMul A (angularDerivative i j (polyMul (reciprocal A u hu k) b))
    quaternionHaar blocks (polyMul W (polyMul d d)) ≤
      sumBound
        (quaternionHaar blocks (polyMul W
          (polyMul (angularDerivative i j b) (angularDerivative i j b))))
        ((C*C) * quaternionHaar blocks (polyMul W
          (polyMul (angularDerivative i j A) (angularDerivative i j A)))) := by
  dsimp only
  let G := reciprocal A u hu k
  let J := polyMul A (reciprocalSlope A u hu k)
  let r := polyMul J b
  let p := polyMul (polyMul A G) (angularDerivative i j b)
  let q := polyNeg (polyMul r (angularDerivative i j A))
  have hdA := angularDerivative_supported_at hi hj hA
  have hdb := angularDerivative_supported_at hi hj hb
  have hG := reciprocal_supported hA u hu k
  have hJ := supported_polyMul hA (reciprocalSlope_supported hA u hu k)
  have hp : SupportedQuaternionBlocks blocks p :=
    supported_polyMul (supported_polyMul hA hG) hdb
  have hq : SupportedQuaternionBlocks blocks q :=
    support_neg (supported_polyMul (supported_polyMul hJ hb) hdA)
  have hAJ : RatPolyCoeffEqv (polyMul A J)
      (polyMul (polyMul A A) (reciprocalSlope A u hu k)) :=
    RatPolyCoeffEqv.mul_assoc A A (reciprocalSlope A u hu k) |>.symm
  have JC : Certificate blocks
      (polyAdd polyOne (polyNeg (polyMul (polyMul A J) (polyMul A J)))) :=
    Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.neg (hAJ.mul hAJ)))
      (reciprocalSensitivitySquareCertificate hu P U k)
  have RC := relative_multiplier_square_certificate hJ hC Splus Sminus JC
  have PC : Certificate blocks (gap 1 (polyMul A G)) := Certificate.ofCoeff
    ((RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _))
    (reciprocalMultiplierSquareCertificate hu P U k)
  have hpb := Q'.le_trans' _ _ _ (weighted_multiplier_square_le M PC hdb)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hqpin : RatPolyCoeffEqv (polyMul q q)
      (polyMul (polyMul r (angularDerivative i j A))
        (polyMul r (angularDerivative i j A))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
      (by decide) (fun _ => polyMul r (angularDerivative i j A))
  have hqb := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff (hqpin.mul_left W)))
    (weighted_multiplier_square_le M RC hdA)
  have he := reciprocal_ratio_cleared_derivative i j A b u hu k
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((he.mul he).mul_left W)))
    (weighted_square_add_bound M hp hq hpb hqb)

#print axioms relative_multiplier_square_certificate
#print axioms reciprocal_ratio_cleared_derivative
#print axioms reciprocal_ratio_cleared_gradient_square_le

end YMGap.Continuum.QuaternionHaarReciprocalRatioGradientBound
