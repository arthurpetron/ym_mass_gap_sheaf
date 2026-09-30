/-
# Original cross-exterior star comparison with one finite reciprocal

The second exterior normalizer remains literal, so it can be integrated
with its own complementary action to the ORIGINAL partition. Only the
first normalizer is corrected. The loss is one factor 1-rho^k, not two.
This is an actual finite polynomial comparison, not yet the path-energy
Fubini identity or a coercivity theorem.
-/

import YMGap.Continuum.BF4ExactSlabConditionalStarComparison
import YMGap.Continuum.QuaternionHaarOneSidedReciprocalComparison

namespace YMGap.Continuum.BF4ExactSlabOneSidedStarComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabConditionalStarComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarOneSidedReciprocalComparison
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem support_extend {n : Nat} (extra : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+extra) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n extra))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

include hK hl in
/-- Quantitative original-action comparison with the second denominator
uncancelled and arbitrary certified joint-copy insertion. -/
theorem weighted_one_sided_star_comparison (k : Nat) {r : RatPoly}
    (R : Certificate (blocks extent + blocks extent) r) :
    (starLower w extent link * starLower w extent link *
        (1 + -((starRadius hw0 hw1 extent link)^k))) *
        quaternionHaar (blocks extent + blocks extent)
          (polyMul (otherStar w K extent link) r) ≤
      (starUpper w extent link * starUpper w extent link) *
        quaternionHaar (blocks extent + blocks extent)
          (polyMul (polyMul (firstKernel hw0 hw1 K extent link k)
            (otherNormalizer w K extent link)) r) := by
  have hA := support_extend (blocks extent) (incidentHeat_supported w K extent link)
  let P := certificate_extend (blocks extent) (incidentHeat_supported w K extent link)
    (starCertificate hw0 hw1 K extent hK (link := link))
  have H := Certificate.ofCoeff
    ((cap_mul_left _ _).add (RatPolyCoeffEqv.neg (cap_mul_left _ _)))
    (crossStarComparison hw0 hw1 K extent hK hl)
  exact weighted_one_sided_comparison _ _ _ _ _ _ _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (starLower_positive hw0 hw1 extent link))
      (Q'.le_of_lt (starLower_positive hw0 hw1 extent link)))
    (starUpper_positive hw0 hw1 extent link) (starLower_le_starUpper hw0 hw1 extent link)
    (support_extend _ (inPlaceNormalizer_supported w K extent link))
    (reindex_certificate (swap extent link) hA P) H
    (normalizerLowerCertificate hw0 hw1 K extent hK hl)
    (normalizerUpperCertificate hw0 hw1 K extent hl) k R

#print axioms weighted_one_sided_star_comparison

end YMGap.Continuum.BF4ExactSlabOneSidedStarComparison
