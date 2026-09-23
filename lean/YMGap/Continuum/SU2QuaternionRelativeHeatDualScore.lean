/-
# Actual relative-heat dual score bound with the same positive source

The source may depend on every block of its slice, and the test may depend on
both complete slices. The local kernel is the actual selected relative heat.
Its curvature and integrated Hessian sign are constructed, not hypotheses.
This is a local estimate, not the whole interacting product-family estimate
or a spectral gap. Nome dependence and the cutoff onset remain explicit.
-/

import YMGap.Continuum.QuaternionHaarCurvatureDualBound
import YMGap.Continuum.SU2QuaternionHeatLogCurvature
import YMGap.Continuum.SU2QuaternionSingleHeatHessian
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension

namespace YMGap.Continuum.SU2QuaternionRelativeHeatDualScore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.SU2QuaternionSingleHeatHessian
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarCurvatureDualBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)

/-- Actual finite-heat score duality, with no ADDITIONAL inverse heat-floor
cost from cancellation. The explicit curvature constant still depends on the
heat floor. Both source copies and the same normalization are retained. -/
theorem relativeHeat_dual_score_bound
    {n : Nat} (block : Fin n) (first second : Fin 4)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (a f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (A : Certificate n a) (hf : SupportedQuaternionBlocks (n+n) f) :
    let W := heatAt block.val (n+block.val) w K
    let d := angularDerivative (4*(n+block.val)+first.val)
      (4*(n+block.val)+second.val) W
    let background := polyMul a (liftBoundary n a)
    quaternionHaar (n+n) (polyMul background (polyMul d f)) *
        quaternionHaar (n+n) (polyMul background (polyMul d f)) ≤
      quaternionHaar (n+n) (polyMul background (polyMul W (polyMul f f))) *
        (logCurvatureCap w hw0 hw1 * quaternionHaar (n+n) (polyMul background W)) := by
  dsimp only
  let W := heatAt block.val (n+block.val) w K
  let D := angularDerivative (4*(n+block.val)+first.val) (4*(n+block.val)+second.val)
  have hleft : block.val < n+n := by have := block.isLt; omega
  have hright : n+block.val < n+n := by have := block.isLt; omega
  have hfirst : 4*(n+block.val)+first.val < 4*(n+n) := by have := first.isLt; omega
  have hsecond : 4*(n+block.val)+second.val < 4*(n+n) := by have := second.isLt; omega
  have hW : SupportedQuaternionBlocks (n+n) W := heat_supported hleft hright w K
  have hd := angularDerivative_supported_at hfirst hsecond hW
  have hdd := angularDerivative_supported_at hfirst hsecond hd
  let I := heatInterval hleft hright hw0 hw1 K
  let ell := headFloor w
  let u := ell + prefixCap w
  have hell : (0 : Q') < ell := headFloor_positive hw0 hw1
  have hle : ell ≤ u := Q'.add_le_self_of_nonneg _ _ I.nonnegative
  have hu : (0 : Q') < u := Q'.pos_of_lt_of_le hell hle
  let U : Certificate (n+n) (polyAdd (cap u) (polyNeg W)) :=
    Certificate.ofCoeff
      (((cap_add ell _).symm.add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
          (.add (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
          (fun | 0 => cap ell | 1 => cap (prefixCap w) | _ => W)))
      ((Certificate.constant (n+n) ell (Q'.le_of_lt hell)).add I.upper)
  exact curvature_dual_bound hW hd hdd hf hell hu hle
    (heatAt_floorCertificate hleft hright hw0 hw1 K
      (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK)) U
    ((certificate_extend n ha A).mul (lift_certificate n A))
    (heatLogHessianBounds hleft hright hright hright
      first.isLt second.isLt first.isLt second.isLt hw0 hw1 K hK).1
    (heatAt_upperAngularHessian_nonpositive n block first second w (Q'.le_of_lt hw0) K a ha)

/-- The normalized version uses the reciprocal of the SAME original edge
mass. Its positivity is explicit; the zero-source case is covered by the
homogeneous theorem above, not assigned an artificial normalized law. -/
theorem relativeHeat_normalized_dual_score_bound
    {n : Nat} (block : Fin n) (first second : Fin 4)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (a f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (A : Certificate n a) (hf : SupportedQuaternionBlocks (n+n) f)
    (hZ : (0 : Q') < quaternionHaar (n+n)
      (polyMul (polyMul a (liftBoundary n a)) (heatAt block.val (n+block.val) w K))) :
    let W := heatAt block.val (n+block.val) w K
    let d := angularDerivative (4*(n+block.val)+first.val)
      (4*(n+block.val)+second.val) W
    let background := polyMul a (liftBoundary n a)
    let r := Q'.recipPos (quaternionHaar (n+n) (polyMul background W)) hZ
    (r*quaternionHaar (n+n) (polyMul background (polyMul d f))) *
        (r*quaternionHaar (n+n) (polyMul background (polyMul d f))) ≤
      logCurvatureCap w hw0 hw1 *
        (r*quaternionHaar (n+n) (polyMul background (polyMul W (polyMul f f)))) :=
  RationalQuadraticDiscriminant.normalize_squared_bound _ _ _ _ hZ
    (relativeHeat_dual_score_bound block first second hw0 hw1 K hK a f ha A hf)

end YMGap.Continuum.SU2QuaternionRelativeHeatDualScore

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatDualScore.relativeHeat_dual_score_bound
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatDualScore.relativeHeat_normalized_dual_score_bound
