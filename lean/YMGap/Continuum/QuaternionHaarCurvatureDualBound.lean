/-
# A lossless dual score estimate from curvature and an integrated Hessian sign

Complete the square AFTER clearing the positive kernel factor, then remove
that factor by constructive integrated order reflection. The final estimate
retains the same kernel, background and normalization, with no inverse-floor
loss. This general theorem has explicit curvature and Hessian premises;
physical instances must actually supply them for their original kernel.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
import YMGap.Continuum.RationalQuadraticDiscriminant
import YMGap.Continuum.SU2QuaternionAngularSupport

namespace YMGap.Continuum.QuaternionHaarCurvatureDualBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
open YMGap.Continuum.RationalQuadraticDiscriminant

local infix:50 " ≈ " => Q'.eqv

private def scalePoly (c : Q') (p : RatPoly) := polyMul (cap c) p

private theorem scale_support {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (scalePoly c p) :=
  supported_polyMul (polySmul_supported (supported_one blocks) c) hp

private def tilt (W d dd f : RatPoly) (lambda s t : Q') : RatPoly :=
  polyAdd
    (polyAdd (scalePoly s (scalePoly s (polyMul W (polyMul f f))))
      (scalePoly (-2) (scalePoly s (scalePoly t (polyMul d f)))))
    (scalePoly t (scalePoly t (polyAdd dd (scalePoly lambda W))))

private theorem tilt_support {blocks : Nat} {W d dd f : RatPoly}
    (hW : SupportedQuaternionBlocks blocks W) (hd : SupportedQuaternionBlocks blocks d)
    (hdd : SupportedQuaternionBlocks blocks dd) (hf : SupportedQuaternionBlocks blocks f)
    (lambda s t : Q') : SupportedQuaternionBlocks blocks (tilt W d dd f lambda s t) :=
  supported_add
    (supported_add (scale_support (scale_support (supported_polyMul hW (supported_polyMul hf hf)) s) s)
      (scale_support (scale_support (scale_support (supported_polyMul hd hf) t) s) (-2)))
    (scale_support (scale_support (supported_add hdd (scale_support hW lambda)) t) t)

/-- Exact completion of the square, including the original mixed numerator. -/
private def clearedTiltCertificate {blocks : Nat} {W d dd f : RatPoly}
    (hW : SupportedQuaternionBlocks blocks W) (hd : SupportedQuaternionBlocks blocks d)
    (hf : SupportedQuaternionBlocks blocks f) (lambda s t : Q')
    (C : Certificate blocks (polyAdd (polyMul (cap lambda) (polyMul W W))
      (polyAdd (polyMul W dd) (polyNeg (polyMul d d))))) :
    Certificate blocks (polyMul W (tilt W d dd f lambda s t)) := by
  let v := polyAdd (scalePoly s (polyMul W f)) (scalePoly (-1) (scalePoly t d))
  have hv : SupportedQuaternionBlocks blocks v :=
    supported_add (scale_support (supported_polyMul hW hf) s)
      (scale_support (scale_support hd t) (-1))
  have t2 : Certificate blocks (polyMul (cap t) (cap t)) :=
    Certificate.square (cap t) (polySmul_supported (supported_one blocks) t)
  exact Certificate.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0)
      (.add
        (.add (.mul (.var 4) (.mul (.var 4) (.mul (.var 0) (.mul (.var 3) (.var 3)))))
          (.mul (.const (-2)) (.mul (.var 4) (.mul (.var 5) (.mul (.var 1) (.var 3))))))
        (.mul (.var 5) (.mul (.var 5) (.add (.var 2) (.mul (.var 6) (.var 0)))))))
    (.add
      (.mul
        (.add (.mul (.var 4) (.mul (.var 0) (.var 3)))
          (.mul (.const (-1)) (.mul (.var 5) (.var 1))))
        (.add (.mul (.var 4) (.mul (.var 0) (.var 3)))
          (.mul (.const (-1)) (.mul (.var 5) (.var 1)))))
      (.mul (.mul (.var 5) (.var 5))
        (.add (.mul (.var 6) (.mul (.var 0) (.var 0)))
          (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))))
    (by decide)
    (fun | 0 => W | 1 => d | 2 => dd | 3 => f | 4 => cap s | 5 => cap t | _ => cap lambda))
    ((Certificate.square v hv).add (t2.mul C))

private theorem haar_scale (blocks : Nat) (background p : RatPoly) (c : Q') :
    quaternionHaar blocks (polyMul background (scalePoly c p)) ≈
      c*quaternionHaar blocks (polyMul background p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => background | 1 => cap c | _ => p)).trans (cap_mul_left c _)))
    (quaternionHaar_polySmul blocks c _)

private theorem haar_add (blocks : Nat) (background p q : RatPoly) :
    quaternionHaar blocks (polyMul background (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul background p) + quaternionHaar blocks (polyMul background q) := by
  exact Q'.eqv_trans _ _ _ (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.var 2)))
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => background | 1 => p | _ => q)))
    (quaternionHaar_append blocks _ _)

private theorem haar_tilt (blocks : Nat) (background W d dd f : RatPoly) (lambda s t : Q') :
    quaternionHaar blocks (polyMul background (tilt W d dd f lambda s t)) ≈
      s*s*quaternionHaar blocks (polyMul background (polyMul W (polyMul f f))) +
      -(2*(s*t)*quaternionHaar blocks (polyMul background (polyMul d f))) +
      t*t*(quaternionHaar blocks (polyMul background dd) +
        lambda*quaternionHaar blocks (polyMul background W)) := by
  have first := Q'.eqv_trans _ _ _ (haar_scale blocks background
    (scalePoly s (polyMul W (polyMul f f))) s)
    (Q'.mul_eqv_congr_left s _ _ (haar_scale blocks background _ s))
  have second := Q'.eqv_trans _ _ _ (haar_scale blocks background
    (scalePoly s (scalePoly t (polyMul d f))) (-2))
    (Q'.mul_eqv_congr_left (-2) _ _ (Q'.eqv_trans _ _ _ (haar_scale blocks background _ s)
      (Q'.mul_eqv_congr_left s _ _ (haar_scale blocks background _ t))))
  have third := Q'.eqv_trans _ _ _ (haar_scale blocks background
    (scalePoly t (polyAdd dd (scalePoly lambda W))) t)
    (Q'.mul_eqv_congr_left t _ _ (Q'.eqv_trans _ _ _ (haar_scale blocks background _ t)
      (Q'.mul_eqv_congr_left t _ _ (Q'.eqv_trans _ _ _ (haar_add blocks background dd _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_scale blocks background W lambda))))))
  refine Q'.eqv_trans _ _ _ (haar_add blocks background _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (haar_add blocks background _ _) (Q'.add_eqv_congr' first second)) third) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
      (.mul (.const (-2)) (.mul (.var 0) (.mul (.var 1) (.var 3)))))
      (.mul (.var 1) (.mul (.var 1) (.var 4))))
    (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
      (.neg (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 3))))
      (.mul (.mul (.var 1) (.var 1)) (.var 4))) (by decide)
    (fun
      | 0 => s
      | 1 => t
      | 2 => quaternionHaar blocks (polyMul background (polyMul W (polyMul f f)))
      | 3 => quaternionHaar blocks (polyMul background (polyMul d f))
      | _ => quaternionHaar blocks (polyMul background dd) +
          lambda*quaternionHaar blocks (polyMul background W))

/-- Same-background dual score bound. Positivity of a density is never
substituted for a supplied bound on a different kernel or normalization. -/
theorem curvature_dual_bound
    {blocks : Nat} {background W d dd f : RatPoly} {ell u lambda : Q'}
    (hW : SupportedQuaternionBlocks blocks W) (hd : SupportedQuaternionBlocks blocks d)
    (hdd : SupportedQuaternionBlocks blocks dd) (hf : SupportedQuaternionBlocks blocks f)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd W (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg W)))
    (B : Certificate blocks background)
    (C : Certificate blocks (polyAdd (polyMul (cap lambda) (polyMul W W))
      (polyAdd (polyMul W dd) (polyNeg (polyMul d d)))))
    (H : quaternionHaar blocks (polyMul background dd) ≤ (0 : Q')) :
    quaternionHaar blocks (polyMul background (polyMul d f)) *
        quaternionHaar blocks (polyMul background (polyMul d f)) ≤
      quaternionHaar blocks (polyMul background (polyMul W (polyMul f f))) *
        (lambda*quaternionHaar blocks (polyMul background W)) := by
  apply nonnegative_quadratic_discriminant
  intro s t
  have h := haar_nonnegative_of_positive_multiplier hW
    (tilt_support hW hd hdd hf lambda s t) hell hu hle L U B
    (clearedTiltCertificate hW hd hf lambda s t C)
  have hD : quaternionHaar blocks (polyMul background dd) +
      lambda*quaternionHaar blocks (polyMul background W) ≤
      lambda*quaternionHaar blocks (polyMul background W) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ H)
      (Q'.le_of_eqv (QPoly.q_zero_add_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_tilt blocks background W d dd f lambda s t)))
    (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hD
      (SumOfSquares.q_mul_self_nonneg t)))

end YMGap.Continuum.QuaternionHaarCurvatureDualBound

#print axioms YMGap.Continuum.QuaternionHaarCurvatureDualBound.curvature_dual_bound
