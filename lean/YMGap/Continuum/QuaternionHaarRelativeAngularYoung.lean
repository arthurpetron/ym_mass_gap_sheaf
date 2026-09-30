/-
# Denominator-cleared Young bound for a certified relative Haar derivative

For a positive original weight W with both polynomial cone certificates
CW ± DW, multiply those certificates by the squares (Ca ∓ b)^2. Their
sum is 2C times the signed Young budget. No minimum of W, division by W,
or independence of the supported test polynomials is used.
-/

import YMGap.Continuum.QuaternionHaarRelativeAngularBound
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.QuaternionHaarRelativeAngularYoung

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound

local infix:50 " ≈ " => Q'.eqv

private theorem supported_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term hterm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hterm
  exact hp s hs

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term hterm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hterm
  exact hp s hs

/-- The signed integrand before multiplication by the positive scalar 2C. -/
def youngBudget (i j : Nat) (W a b : RatPoly) (C : Q') : RatPoly :=
  polyAdd
    (polyAdd
      (polyMul (polyMul (cap C) (cap C)) (polyMul W (polyMul a a)))
      (polyMul W (polyMul b b)))
    (polyNeg (polyMul (cap 2) (polyMul (angularDerivative i j W) (polyMul a b))))

/-- An actual positive-cone certificate, including all signed mixed terms.
The factor 2C is left in place, so the witness never divides a polynomial. -/
def scaled_young_certificate {blocks i j : Nat} {W : RatPoly} {C : Q'}
    (R : RelativeBound blocks i j W C) {a b : RatPoly}
    (ha : SupportedQuaternionBlocks blocks a)
    (hb : SupportedQuaternionBlocks blocks b) :
    Certificate blocks (polyMul (cap 2) (polyMul (cap C) (youngBudget i j W a b C))) := by
  let d := angularDerivative i j W
  let minus := polyAdd (polyMul (cap C) a) (polyMul (cap (-1)) b)
  let plus := polyAdd (polyMul (cap C) a) b
  have hc : SupportedQuaternionBlocks blocks (cap C) := by
    unfold cap
    exact supported_smul (supported_one blocks) C
  have hn : SupportedQuaternionBlocks blocks (cap (-1)) := by
    unfold cap
    exact supported_smul (supported_one blocks) (-1)
  have hm : SupportedQuaternionBlocks blocks minus :=
    supported_add (supported_polyMul hc ha) (supported_polyMul hn hb)
  have hp : SupportedQuaternionBlocks blocks plus :=
    supported_add (supported_polyMul hc ha) hb
  have hcone : Certificate blocks
      (polyAdd
        (polyMul (polyAdd (polyMul (cap C) W) d) (polyMul minus minus))
        (polyMul (polyAdd (polyMul (cap C) W) (polyNeg d)) (polyMul plus plus))) :=
    (R.lower.mul (.square minus hm)).add (R.upper.mul (.square plus hp))
  apply Certificate.ofCoeff ?_ hcone
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.const 2) (.mul (.var 4)
      (.add
        (.add
          (.mul (.mul (.var 4) (.var 4))
            (.mul (.var 0) (.mul (.var 2) (.var 2))))
          (.mul (.var 0) (.mul (.var 3) (.var 3))))
        (.neg (.mul (.const 2) (.mul (.var 1) (.mul (.var 2) (.var 3))))))))
    (.add
      (.mul
        (.add (.mul (.var 4) (.var 0)) (.var 1))
        (.mul
          (.add (.mul (.var 4) (.var 2)) (.mul (.const (-1)) (.var 3)))
          (.add (.mul (.var 4) (.var 2)) (.mul (.const (-1)) (.var 3)))))
      (.mul
        (.add (.mul (.var 4) (.var 0)) (.neg (.var 1)))
        (.mul
          (.add (.mul (.var 4) (.var 2)) (.var 3))
          (.add (.mul (.var 4) (.var 2)) (.var 3)))))
    (by decide) (fun | 0 => W | 1 => d | 2 => a | 3 => b | _ => cap C)

private theorem haar_cap (blocks : Nat) (c : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul (cap c) p) ≈ c * quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c p))
    (quaternionHaar_polySmul blocks c p)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_double_cap (blocks : Nat) (C : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul (polyMul (cap C) (cap C)) p) ≈
      (C*C) * quaternionHaar blocks p := by
  have h : RatPolyCoeffEqv (polyMul (polyMul (cap C) (cap C)) p)
      (polyMul (cap C) (polyMul (cap C) p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.mul (.var 0) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => cap C | _ => p)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff h)
    (Q'.eqv_trans _ _ _
      (haar_cap blocks C _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left C _ _ (haar_cap blocks C p))
        (Q'.eqv_symm (Q'.mul_assoc_eqv C C (quaternionHaar blocks p)))))

private theorem haar_budget_pin (blocks i j : Nat) (W a b : RatPoly) (C : Q') :
    quaternionHaar blocks (youngBudget i j W a b C) ≈
      (C*C) * quaternionHaar blocks (polyMul W (polyMul a a)) +
      quaternionHaar blocks (polyMul W (polyMul b b)) +
      -(2 * quaternionHaar blocks (polyMul (angularDerivative i j W) (polyMul a b))) := by
  unfold youngBudget
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (haar_double_cap blocks C _) (Q'.eqv_refl _)))
      (Q'.eqv_trans _ _ _ (haar_neg blocks _)
        (Q'.neg_eqv_congr _ _ (haar_cap blocks 2 _))))

private theorem budget_nonnegative {blocks i j : Nat} {W : RatPoly} {C : Q'}
    (R : RelativeBound blocks i j W C) (hC : (0 : Q') < C)
    {a b : RatPoly} (ha : SupportedQuaternionBlocks blocks a)
    (hb : SupportedQuaternionBlocks blocks b) :
    (0 : Q') ≤ quaternionHaar blocks (youngBudget i j W a b C) := by
  let p := youngBudget i j W a b C
  have hs := (scaled_young_certificate R ha hb).haar_nonnegative
  have hp : quaternionHaar blocks (polyMul (cap 2) (polyMul (cap C) p)) ≈
      2 * (C * quaternionHaar blocks p) :=
    Q'.eqv_trans _ _ _ (haar_cap blocks 2 _)
      (Q'.mul_eqv_congr_left 2 _ _ (haar_cap blocks C p))
  have hprod : (0 : Q') ≤ 2 * (C * quaternionHaar blocks p) :=
    Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hp)
  exact Q'.nonneg_of_mul_pos hC (Q'.nonneg_of_mul_pos (by decide) hprod)

/-- The positive-sign mixed derivative is bounded by the two original
weighted squares. The supported tests may overlap the weight arbitrarily. -/
theorem relative_young_upper {blocks i j : Nat} {W : RatPoly} {C : Q'}
    (R : RelativeBound blocks i j W C) (hC : (0 : Q') < C)
    {a b : RatPoly} (ha : SupportedQuaternionBlocks blocks a)
    (hb : SupportedQuaternionBlocks blocks b) :
    2 * quaternionHaar blocks (polyMul (angularDerivative i j W) (polyMul a b)) ≤
      (C*C) * quaternionHaar blocks (polyMul W (polyMul a a)) +
      quaternionHaar blocks (polyMul W (polyMul b b)) := by
  have h0 := budget_nonnegative R hC ha hb
  have hp := haar_budget_pin blocks i j W a b C
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv hp))

/-- The opposite signed mixed derivative obeys the same Young budget. -/
theorem relative_young_lower {blocks i j : Nat} {W : RatPoly} {C : Q'}
    (R : RelativeBound blocks i j W C) (hC : (0 : Q') < C)
    {a b : RatPoly} (ha : SupportedQuaternionBlocks blocks a)
    (hb : SupportedQuaternionBlocks blocks b) :
    -(2 * quaternionHaar blocks (polyMul (angularDerivative i j W) (polyMul a b))) ≤
      (C*C) * quaternionHaar blocks (polyMul W (polyMul a a)) +
      quaternionHaar blocks (polyMul W (polyMul b b)) := by
  let d := angularDerivative i j W
  have hcrossPoly : RatPolyCoeffEqv
      (polyMul d (polyMul a (polyNeg b)))
      (polyNeg (polyMul d (polyMul a b))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.neg (.var 2))))
      (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => d | 1 => a | _ => b)
  have hcross : quaternionHaar blocks (polyMul d (polyMul a (polyNeg b))) ≈
      -(quaternionHaar blocks (polyMul d (polyMul a b))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hcrossPoly) (haar_neg blocks _)
  have hsquarePoly : RatPolyCoeffEqv
      (polyMul W (polyMul (polyNeg b) (polyNeg b)))
      (polyMul W (polyMul b b)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1))))
      (.mul (.var 0) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => W | _ => b)
  have hleft :
      2 * quaternionHaar blocks (polyMul d (polyMul a (polyNeg b))) ≈
      -(2 * quaternionHaar blocks (polyMul d (polyMul a b))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ hcross)
      (Q'.mul_neg_eqv 2 _)
  have hright :
      (C*C) * quaternionHaar blocks (polyMul W (polyMul a a)) +
        quaternionHaar blocks (polyMul W (polyMul (polyNeg b) (polyNeg b))) ≈
      (C*C) * quaternionHaar blocks (polyMul W (polyMul a a)) +
        quaternionHaar blocks (polyMul W (polyMul b b)) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_of_coeff hsquarePoly)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
      (relative_young_upper R hC ha (supported_neg hb)))
    (Q'.le_of_eqv hright)

#print axioms youngBudget
#print axioms scaled_young_certificate
#print axioms relative_young_upper
#print axioms relative_young_lower

end YMGap.Continuum.QuaternionHaarRelativeAngularYoung
