/-
# A square-triangle estimate in the same weighted Haar form

Positivity of m*(p-q)^2 and the exact parallelogram identity bound
H[m*(p+q)^2] by twice each separate weighted square. The weight is the
same constructed positive polynomial in every term; neither independence
nor unweighted norm comparison is used.

The consumer combines the two finite approximation errors in the original
temporal marginal. This is not a bound on their interacting signed cost.
-/

import YMGap.Continuum.QuaternionHaarFamilySquare
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Constructive.CRealAdd

namespace YMGap.Continuum.QuaternionHaarWeightedSquareTriangle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem parallelogram (p q : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (polyAdd p q) (polyAdd p q))
        (polyMul (polyAdd p (polyNeg q)) (polyAdd p (polyNeg q))))
      (polyAdd (polyAdd (polyMul p p) (polyMul p p))
        (polyAdd (polyMul q q) (polyMul q q))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1)))))
    (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
      (.add (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => p | _ => q)

/-- The two errors are measured against exactly the same positive weight. -/
theorem weighted_square_add_le {blocks : Nat} {m p q : RatPoly}
    (M : Certificate blocks m)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    quaternionHaar blocks (polyMul m (polyMul (polyAdd p q) (polyAdd p q))) ≤
      (quaternionHaar blocks (polyMul m (polyMul p p)) +
        quaternionHaar blocks (polyMul m (polyMul p p))) +
      (quaternionHaar blocks (polyMul m (polyMul q q)) +
        quaternionHaar blocks (polyMul m (polyMul q q))) := by
  let d := polyAdd p (polyNeg q)
  have hd : SupportedQuaternionBlocks blocks d := supported_add hp (support_neg hq)
  have hpositive := (M.mul (Certificate.square d hd)).haar_nonnegative
  have he :
      quaternionHaar blocks (polyMul m (polyMul (polyAdd p q) (polyAdd p q))) +
        quaternionHaar blocks (polyMul m (polyMul d d)) ≈
      (quaternionHaar blocks (polyMul m (polyMul p p)) +
        quaternionHaar blocks (polyMul m (polyMul p p))) +
      (quaternionHaar blocks (polyMul m (polyMul q q)) +
        quaternionHaar blocks (polyMul m (polyMul q q))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_weighted_add blocks m _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff ((parallelogram p q).mul_left m))
        (Q'.eqv_trans _ _ _ (haar_weighted_add blocks m _ _)
          (Q'.add_eqv_congr' (haar_weighted_add blocks m _ _) (haar_weighted_add blocks m _ _))))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hpositive) (Q'.le_of_eqv he)

/-- Existing rational square budgets combine without square roots or
additional positivity hypotheses on their upper bounds. -/
theorem weighted_square_add_bound {blocks : Nat} {m p q : RatPoly}
    (M : Certificate blocks m)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    {a b : Q'}
    (ha : quaternionHaar blocks (polyMul m (polyMul p p)) ≤ a)
    (hb : quaternionHaar blocks (polyMul m (polyMul q q)) ≤ b) :
    quaternionHaar blocks (polyMul m (polyMul (polyAdd p q) (polyAdd p q))) ≤ sumBound a b :=
  Q'.le_trans' _ _ _ (weighted_square_add_le M hp hq)
    (Q'.add_le_add (Q'.add_le_add ha ha) (Q'.add_le_add hb hb))

#print axioms weighted_square_add_le
#print axioms weighted_square_add_bound

end YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
