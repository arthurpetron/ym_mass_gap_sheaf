/-
# Actual two-exterior conditional kernels with finite reciprocal error

The shared updated link, both original incident stars and both actual Haar
normalizers are retained. Positive finite reciprocal polynomials give
  ell^2 (1-rho^k) H[A' G_E r] <= U^2 H[A G_D r]
for every certified nonnegative joint insertion r. The same explicit cutoff
bounds both normalization defects by epsilon. Here ell=headFloor^d,
U=prefixCap^d and rho=1-ell/U; nome dependence is not suppressed.

No limiting conditional inverse, path-variance inequality, spatially uniform
coercivity or physical mass gap is asserted by this finite comparison.
-/

import YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
import YMGap.Continuum.QuaternionHaarReciprocalCrossComparison
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

namespace YMGap.Continuum.BF4ExactSlabConditionalStarComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalCrossComparison
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

private theorem support_extend {n : Nat} (extra : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+extra) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n extra))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (link : Z4Link)

def firstKernel (k : Nat) : RatPoly :=
  polyMul (incidentHeat w K extent link)
    (reciprocal (inPlaceNormalizer w K extent link) (starUpper w extent link)
      (starUpper_positive hw0 hw1 extent link) k)

def otherKernel (k : Nat) : RatPoly :=
  polyMul (otherStar w K extent link)
    (reciprocal (otherNormalizer w K extent link) (starUpper w extent link)
      (starUpper_positive hw0 hw1 extent link) k)

variable (hK : headCutoff w ≤ K) (hl : link ∈ boundaryCompleteSlabLinks extent)

/-- Both denominator corrections come with this same geometric error. -/
def firstNormalizerError (k : Nat) : Interval (blocks extent + blocks extent)
    (polyAdd (polyMul (inPlaceNormalizer w K extent link)
      (reciprocal (inPlaceNormalizer w K extent link) (starUpper w extent link)
        (starUpper_positive hw0 hw1 extent link) k)) (polyNeg polyOne))
    ((starRadius hw0 hw1 extent link)^k) :=
  multiplierErrorInterval (support_extend _ (inPlaceNormalizer_supported w K extent link))
    (starUpper_positive hw0 hw1 extent link) (starLower_le_starUpper hw0 hw1 extent link)
    (normalizerLowerCertificate hw0 hw1 K extent hK hl)
    (normalizerUpperCertificate hw0 hw1 K extent hl) k

def otherNormalizerError (k : Nat) : Interval (blocks extent + blocks extent)
    (polyAdd (polyMul (otherNormalizer w K extent link)
      (reciprocal (otherNormalizer w K extent link) (starUpper w extent link)
        (starUpper_positive hw0 hw1 extent link) k)) (polyNeg polyOne))
    ((starRadius hw0 hw1 extent link)^k) :=
  multiplierErrorInterval (reindex_supported (swap extent link) _)
    (starUpper_positive hw0 hw1 extent link) (starLower_le_starUpper hw0 hw1 extent link)
    (otherNormalizerLowerCertificate hw0 hw1 K extent hK hl)
    (otherNormalizerUpperCertificate hw0 hw1 K extent hl) k

include hw0 hw1 in
theorem error_le_tolerance (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : starApproximationCutoff hw0 hw1 extent link epsilon ≤ k) :
    (starRadius hw0 hw1 extent link)^k ≤ epsilon :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
    (PositiveContractionResidual.geometric_bound
      (starRadius_nonnegative hw0 hw1 extent link) (starRadius_lt_one hw0 hw1 extent link)
      Q'.zero_le_one he k hk)

/-- The explicit cutoff is shared, not chosen separately for the two exteriors. -/
def bothNormalizerErrors (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : starApproximationCutoff hw0 hw1 extent link epsilon ≤ k) :
    (Interval (blocks extent + blocks extent)
      (polyAdd (polyMul (inPlaceNormalizer w K extent link)
        (reciprocal (inPlaceNormalizer w K extent link) (starUpper w extent link)
          (starUpper_positive hw0 hw1 extent link) k)) (polyNeg polyOne)) epsilon) ×
    (Interval (blocks extent + blocks extent)
      (polyAdd (polyMul (otherNormalizer w K extent link)
        (reciprocal (otherNormalizer w K extent link) (starUpper w extent link)
          (starUpper_positive hw0 hw1 extent link) k)) (polyNeg polyOne)) epsilon) :=
  ⟨(firstNormalizerError hw0 hw1 K extent link hK hl k).weaken
      (error_le_tolerance hw0 hw1 extent link epsilon he k hk),
    (otherNormalizerError hw0 hw1 K extent link hK hl k).weaken
      (error_le_tolerance hw0 hw1 extent link epsilon he k hk)⟩

/-- Denominator-cleared original-star comparison consumed by actual finite
reciprocals, without assuming the desired conditional-kernel estimate. -/
def kernelComparisonCertificate (k : Nat) : Certificate (blocks extent + blocks extent)
    (polyAdd
      (polyMul (cap (starUpper w extent link * starUpper w extent link))
        (firstKernel hw0 hw1 K extent link k))
      (polyNeg (polyMul (cap (starLower w extent link * starLower w extent link))
        (polyMul (polyAdd polyOne (polyNeg (cap ((starRadius hw0 hw1 extent link)^k))))
          (otherKernel hw0 hw1 K extent link k))))) := by
  let P := certificate_extend (blocks extent) (incidentHeat_supported w K extent link)
    (starCertificate hw0 hw1 K extent hK (link := link))
  have H := Certificate.ofCoeff
    ((cap_mul_left _ _).add (RatPolyCoeffEqv.neg (cap_mul_left _ _)))
    (crossStarComparison hw0 hw1 K extent hK hl)
  exact reciprocalCrossComparisonOfCross _ _ _ _ _ _
    (starLower_positive hw0 hw1 extent link) (starUpper_positive hw0 hw1 extent link)
    (starLower_le_starUpper hw0 hw1 extent link)
    (support_extend _ (inPlaceNormalizer_supported w K extent link))
    P (reindex_certificate (swap extent link) (support_extend _ (incidentHeat_supported w K extent link)) P)
    H (normalizerUpperCertificate hw0 hw1 K extent hl)
    (normalizerLowerCertificate hw0 hw1 K extent hK hl)
    (otherNormalizerUpperCertificate hw0 hw1 K extent hl) k

private theorem cap_one_sub (r : Q') :
    RatPolyCoeffEqv (polyAdd polyOne (polyNeg (cap r))) (cap (1 + -r)) := by
  have hn : RatPolyCoeffEqv (polyNeg (cap r)) (cap (-r)) := by
    intro weight
    change (-(r*1))*weight []+0 ≈ ((-r)*1)*weight []+0
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv r 1))) (Q'.eqv_refl _)
  exact ((RatPolyCoeffEqv.one_smul polyOne).symm.add hn).trans (cap_add 1 (-r))

private theorem corrected_scale (a r : Q') (p : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (cap a) (polyMul (polyAdd polyOne (polyNeg (cap r))) p))
      (polySmul (a * (1 + -r)) p) := by
  have h := (((cap_one_sub r).mul (.refl p)).trans (cap_mul_left (1 + -r) p)).smul a
  exact (cap_mul_left a _).trans (h.trans (RatPolyCoeffEqv.smul_assoc a (1 + -r) p))

private theorem haar_smul_left (n : Nat) (c : Q') (p r : RatPoly) :
    Q'.eqv (quaternionHaar n (polyMul (polySmul c p) r))
      (c * quaternionHaar n (polyMul p r)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul n c (polyMul p r))

include hK hl in
/-- Quantitative comparison for arbitrary certified nonnegative insertions
depending jointly on both original copies. -/
theorem weighted_kernel_comparison (k : Nat) {r : RatPoly}
    (R : Certificate (blocks extent + blocks extent) r) :
    (starLower w extent link * starLower w extent link *
        (1 + -((starRadius hw0 hw1 extent link)^k))) *
        quaternionHaar (blocks extent + blocks extent)
          (polyMul (otherKernel hw0 hw1 K extent link k) r) ≤
      (starUpper w extent link * starUpper w extent link) *
        quaternionHaar (blocks extent + blocks extent)
          (polyMul (firstKernel hw0 hw1 K extent link k) r) := by
  have H := Certificate.ofCoeff
    ((cap_mul_left _ _).symm.add (RatPolyCoeffEqv.neg (corrected_scale _ _ _).symm))
    (kernelComparisonCertificate hw0 hw1 K extent link hK hl k)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_smul_left _ _ _ _))
    (Q'.le_trans' _ _ _ (haar_order H R) (Q'.le_of_eqv (haar_smul_left _ _ _ _)))

#print axioms firstKernel
#print axioms otherKernel
#print axioms firstNormalizerError
#print axioms otherNormalizerError
#print axioms error_le_tolerance
#print axioms bothNormalizerErrors
#print axioms kernelComparisonCertificate
#print axioms weighted_kernel_comparison

end YMGap.Continuum.BF4ExactSlabConditionalStarComparison
