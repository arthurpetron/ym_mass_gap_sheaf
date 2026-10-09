/-
# Lossless paired score duality on the ORIGINAL odd marginal

The weight is literally W=V*g_n*g_(n+1). Full integrated curvature order,
the actual finite positive window and paired Haar integration by parts give
H[(J_i W)h]^2 <= C(w)*H[W]*H[W*h^2] for every supported signed test h.
The finite reciprocal approximation disappears from the final cost. Its
window/cutoff can depend on width and depth; C depends on the strict nome.

This is a dual score estimate, not a variance floor, weighted Poincare,
useful macro retention, a spacing-uniform mass or a continuum theorem.
-/

import YMGap.Continuum.QPolyHaarPairedAtFrozenBasis
import YMGap.Continuum.QuaternionHaarCurvatureDualBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFisherDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature
  (marginalCurvatureCost marginalCurvatureCutoff
    marginalWeight_frozen_curvature_nonnegative_nearFlat)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature
  (plaquetteCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameAt
  (pairedDerivativeAt pairedDerivativeAt_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QPolyHaarPairedAtFrozenBasis
  (basisDirection frozenCurvatureAt_basis_pin paired_square_haar_zero)
open YMGap.Continuum.QuaternionHaarCurvatureDualBound (integrated_curvature_dual_bound)
open YMGap.Continuum.RationalQuadraticDiscriminant (normalize_squared_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks marginalWeight

private theorem headCutoff_le {w : Q'} {K : Nat}
    (hK : marginalCurvatureCutoff w ≤ K) : headCutoff w ≤ K := by
  unfold marginalCurvatureCutoff plaquetteCurvatureCutoff at hK
  omega

private theorem haar_one_mul (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks (polyMul polyOne p) ≈ quaternionHaar blocks p :=
  haar_of_coeff (RatPolyCoeffEqv.one_mul p)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- Actual selected-link score duality. No curvature or Hessian premise is
left to the caller: both are supplied on the literal original marginal. -/
theorem marginal_paired_score_dual_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (i : Fin 3) {h : RatPoly} (hh : SupportedQuaternionBlocks (N width) h) :
    quaternionHaar (N width) (polyMul
        (pairedDerivativeAt ((baseLinks width).idxOf selected) i
          (marginalWeight w K width n)) h) *
      quaternionHaar (N width) (polyMul
        (pairedDerivativeAt ((baseLinks width).idxOf selected) i
          (marginalWeight w K width n)) h) ≤
    quaternionHaar (N width) (polyMul (marginalWeight w K width n) (polyMul h h)) *
      (marginalCurvatureCost w * quaternionHaar (N width) (marginalWeight w K width n)) := by
  let s := (baseLinks width).idxOf selected
  let W := marginalWeight w K width n
  let d := pairedDerivativeAt s i W
  let dd := pairedDerivativeAt s i d
  have hb : s < N width := activeBlocks_lt width s hs
  have hW := marginalWeight_supported w K width n
  have hd := pairedDerivativeAt_supported hb i hW
  have hdd := pairedDerivativeAt_supported hb i hd
  have hdir : ∀ j, SupportedQuaternionBlocks (N width) (basisDirection i j) := by
    intro j
    unfold basisDirection
    split
    · exact supported_one _
    · intro term ht
      cases ht
  have P : ∀ {R : RatPoly}, Certificate (N width) R →
      (0 : Q') ≤ quaternionHaar (N width) (polyMul R
        (polyAdd (polyMul (cap (marginalCurvatureCost w)) (polyMul W W))
          (polyAdd (polyMul W dd) (polyNeg (polyMul d d))))) := by
    intro R PR
    have hcurv := marginalWeight_frozen_curvature_nonnegative_nearFlat
      hw0 hw1 K width n hK selected hl hs (basisDirection i) hdir PR
    exact Q'.le_trans' _ _ _ hcurv (Q'.le_of_eqv (haar_of_coeff
      ((frozenCurvatureAt_basis_pin s (marginalCurvatureCost w) W i).mul_left R)))
  have hD : quaternionHaar (N width) (polyMul polyOne dd) ≤ (0 : Q') :=
    Q'.le_of_eqv (Q'.eqv_trans _ _ _ (haar_one_mul (N width) dd)
      (paired_square_haar_zero hb i W))
  have hhead := headCutoff_le hK
  have hdual := integrated_curvature_dual_bound hW hd hdd hh
    (BF4ExactSlabFixedSpatialActualMarginalWindow.lower_positive hw0 hw1 K width hhead n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.upper_positive hw0 hw1 K width hhead n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.lower_le_upper w K width n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.lowerCertificate hw0 hw1 K width hhead n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.upperCertificate hw0 hw1 K width hhead n)
    (Certificate.one (N width)) P hD
  have hleft := mul_congr (haar_one_mul (N width) (polyMul d h))
    (haar_one_mul (N width) (polyMul d h))
  have hright := mul_congr
    (haar_one_mul (N width) (polyMul W (polyMul h h)))
    (mul_congr (Q'.eqv_refl (marginalCurvatureCost w)) (haar_one_mul (N width) W))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hdual (Q'.le_of_eqv hright))

/-- Normalize by the SAME positive odd partition, not either terminal mass. -/
theorem marginal_paired_score_normalized_dual_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (i : Fin 3) {h : RatPoly} (hh : SupportedQuaternionBlocks (N width) h) :
    let Z := quaternionHaar (N width) (marginalWeight w K width n)
    let r := Q'.recipPos Z (mass_positive hw0 hw1 K width (headCutoff_le hK) n)
    let B := quaternionHaar (N width) (polyMul
      (pairedDerivativeAt ((baseLinks width).idxOf selected) i
        (marginalWeight w K width n)) h)
    (r*B)*(r*B) ≤ marginalCurvatureCost w *
      (r*quaternionHaar (N width) (polyMul (marginalWeight w K width n) (polyMul h h))) := by
  exact normalize_squared_bound _ _ _ _
    (mass_positive hw0 hw1 K width (headCutoff_le hK) n)
    (marginal_paired_score_dual_bound hw0 hw1 K width n hK selected hl hs i hh)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFisherDual

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherDual.marginal_paired_score_dual_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherDual.marginal_paired_score_normalized_dual_bound
