/-
# Two actual conditional stars sharing the updated original link

Only the exteriors are exchanged between two copies of the original slab.
The updated link itself stays fixed. Both normalizers are the literal Haar
integrals of their own star, and the first is pinned to the existing head
normalizer and full-action marginal. Actual positive floor/cap certificates
give a denominator-cleared comparison on this doubled carrier.

This is not yet a comparison through limiting conditional inverse pairings,
a canonical-path variance bound, or a useful physical scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabStarBandCertificate
import YMGap.Continuum.BF4ExactSlabStarNormalizer
import YMGap.Continuum.SU2QuaternionSharedBlockExteriorSwap
import YMGap.Continuum.SU2QuaternionReplicaPairBounds
import YMGap.Continuum.QuaternionHaarCrossNormalizedComparison
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

namespace YMGap.Continuum.BF4ExactSlabCrossExteriorStar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.SU2QuaternionSharedBlockExteriorSwap
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (reindex_cap_carrier)
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarCrossNormalizedComparison
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

def slot (extent : Nat) (link : Z4Link) : Nat :=
  (boundaryCompleteSlabLinks extent).idxOf link

def swap (extent : Nat) (link : Z4Link) : QuaternionBlockInvolution (blocks extent + blocks extent) :=
  exteriorSwap (blocks extent) (slot extent link)

/-- The same updated link and a second copy of every other coordinate. -/
def otherStar (w : Q') (K extent : Nat) (link : Z4Link) : RatPoly :=
  reindexQuaternionPolynomial (swap extent link) (incidentHeat w K extent link)

def otherNormalizer (w : Q') (K extent : Nat) (link : Z4Link) : RatPoly :=
  reindexQuaternionPolynomial (swap extent link) (inPlaceNormalizer w K extent link)

def starLower (w : Q') (extent : Nat) (link : Z4Link) : Q' :=
  (headFloor w)^(incidentIds extent link).length

def starUpper (w : Q') (extent : Nat) (link : Z4Link) : Q' :=
  (prefixCap w)^(incidentIds extent link).length

theorem starLower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (link : Z4Link) : (0 : Q') < starLower w extent link :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) _

theorem starUpper_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (extent : Nat) (link : Z4Link) : (0 : Q') ≤ starUpper w extent link :=
  Q'.pow_nonneg _ (prefixCap_nonnegative hw0) _

/-- Both normalizers use the SAME original physical link index. -/
theorem otherNormalizer_project_pin (w : Q') (K extent : Nat) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    RatPolyCoeffEqv (otherNormalizer w K extent link)
      (project (slot extent link) (otherStar w K extent link)) :=
  reindex_project_commutes _ _ (List.idxOf_lt_length_of_mem hl) _

/-- After the updated link has been integrated, its normalizer is exactly
the independent upper-copy normalizer under all Haar insertions. -/
theorem otherNormalizer_lift_pin (w : Q') (K extent : Nat) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    HaarCarrierEqv (blocks extent + blocks extent) (otherNormalizer w K extent link)
      (liftBoundary (blocks extent) (inPlaceNormalizer w K extent link)) :=
  normalizer_transport_to_lift _ _ (List.idxOf_lt_length_of_mem hl) _
    (inPlaceNormalizer_supported w K extent link)
    (inPlaceNormalizer_independent w K extent link)

/-- Pin to the already existing head-coordinate normalizer, restored to
the original coordinates. No replacement denominator is introduced. -/
theorem inPlaceNormalizer_head_pin (w : Q') (K extent : Nat) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    HaarCarrierEqv (blocks extent) (inPlaceNormalizer w K extent link)
      (headProbe (linkHeadSwap extent link hl)
        (BF4ExactSlabStarNormalizer.normalizer w K extent link hl)) :=
  (carrierOfPrefix (headProbe_supported _ _) (inPlaceNormalizer_supported w K extent link)
    (restored_prefix _ _ (List.idxOf_lt_length_of_mem hl) (incidentHeat w K extent link))).symm

/-- The entire complementary action remains in the actual marginal. -/
theorem full_marginal_pin (w : Q') (K extent : Nat) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    RatPolyCoeffEqv
      (project (slot extent link)
        (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)))
      (polyMul (inPlaceNormalizer w K extent link) (complementHeat w K extent link)) :=
  (project_congr _ (heatProduct_partition w K extent link)).trans
    (project_mul_right_of_independent _ _ _
      (degree_zero_independent (complementHeat_degree_zero w K extent link hl)))

private theorem support_extend {n : Nat} (extra : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n + extra) p := by
  intro t ht
  exact Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n extra))

private theorem cap_supported (n : Nat) (c : Q') : SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem neg_supported {n : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def reindexLower {n : Nat} (s : QuaternionBlockInvolution n) {p : RatPoly} {ell : Q'}
    (hp : SupportedQuaternionBlocks n p)
    (L : Certificate n (polyAdd p (polyNeg (cap ell)))) :
    Certificate n (polyAdd (reindexQuaternionPolynomial s p) (polyNeg (cap ell))) := by
  have C := reindex_certificate s (supported_add hp (neg_supported (cap_supported n ell))) L
  rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg] at C
  exact .transport (HaarCarrierEqv.add (.refl _ _)
    (HaarCarrierEqv.neg (reindex_cap_carrier s ell).symm)) C

private def reindexUpper {n : Nat} (s : QuaternionBlockInvolution n) {p : RatPoly} {U : Q'}
    (hp : SupportedQuaternionBlocks n p)
    (C : Certificate n (polyAdd (cap U) (polyNeg p))) :
    Certificate n (polyAdd (cap U) (polyNeg (reindexQuaternionPolynomial s p))) := by
  have H := reindex_certificate s (supported_add (cap_supported n U) (neg_supported hp)) C
  rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg] at H
  exact .transport (HaarCarrierEqv.add (reindex_cap_carrier s U).symm (.refl _ _)) H

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) {link : Z4Link}
  (hl : link ∈ boundaryCompleteSlabLinks extent)

def starCertificate : Certificate (blocks extent) (incidentHeat w K extent link) :=
  headProduct_certificate hw0 hw1 K extent hK _ (fun _ hi => incidentIds_physical hi)

def normalizerCertificate : Certificate (blocks extent) (inPlaceNormalizer w K extent link) :=
  project_certificate _ _ (List.idxOf_lt_length_of_mem hl)
    (incidentHeat_supported w K extent link) (starCertificate hw0 hw1 K extent hK (link := link))

/-- Original first-copy floor on the doubled carrier. -/
def normalizerLowerCertificate : Certificate (blocks extent + blocks extent)
    (polyAdd (inPlaceNormalizer w K extent link) (polyNeg (cap (starLower w extent link)))) :=
  certificate_extend _
    (supported_add (inPlaceNormalizer_supported w K extent link) (neg_supported (cap_supported _ _)))
    (inPlaceNormalizer_lowerCertificate hw0 hw1 K extent hK hl)

def normalizerUpperCertificate : Certificate (blocks extent + blocks extent)
    (polyAdd (cap (starUpper w extent link)) (polyNeg (inPlaceNormalizer w K extent link))) :=
  certificate_extend _
    (supported_add (cap_supported _ _) (neg_supported (inPlaceNormalizer_supported w K extent link)))
    (inPlaceNormalizer_upperCertificate hw0 hw1 K extent hl)

def otherNormalizerLowerCertificate : Certificate (blocks extent + blocks extent)
    (polyAdd (otherNormalizer w K extent link) (polyNeg (cap (starLower w extent link)))) :=
  reindexLower (swap extent link) (support_extend _ (inPlaceNormalizer_supported w K extent link))
    (normalizerLowerCertificate hw0 hw1 K extent hK hl)

def otherNormalizerUpperCertificate : Certificate (blocks extent + blocks extent)
    (polyAdd (cap (starUpper w extent link)) (polyNeg (otherNormalizer w K extent link))) :=
  reindexUpper (swap extent link) (support_extend _ (inPlaceNormalizer_supported w K extent link))
    (normalizerUpperCertificate hw0 hw1 K extent hl)

/-- A constructed denominator-cleared comparison between the two actual
stars at the shared link. Both actual exterior normalizers are retained. -/
def crossStarComparison : Certificate (blocks extent + blocks extent)
    (polyAdd
      (polySmul (starUpper w extent link * starUpper w extent link)
        (polyMul (incidentHeat w K extent link) (otherNormalizer w K extent link)))
      (polyNeg (polySmul (starLower w extent link * starLower w extent link)
        (polyMul (otherStar w K extent link) (inPlaceNormalizer w K extent link))))) := by
  let P := certificate_extend (blocks extent) (incidentHeat_supported w K extent link)
    (starCertificate hw0 hw1 K extent hK (link := link))
  let D := certificate_extend (blocks extent) (inPlaceNormalizer_supported w K extent link)
    (normalizerCertificate hw0 hw1 K extent hK hl)
  exact crossProductComparison_smul _ _ _ _ _ _
    (Q'.le_of_lt (starLower_positive hw0 hw1 extent link)) (starUpper_nonnegative hw0 extent link)
    P (reindex_certificate (swap extent link) (support_extend _ (incidentHeat_supported w K extent link)) P)
    D (reindex_certificate (swap extent link) (support_extend _ (inPlaceNormalizer_supported w K extent link)) D)
    (certificate_extend _
      (supported_add (incidentHeat_supported w K extent link) (neg_supported (cap_supported _ _)))
      (incidentHeatLowerCertificate hw0 hw1 K extent hK link))
    (otherNormalizerLowerCertificate hw0 hw1 K extent hK hl)
    (reindexUpper (swap extent link) (support_extend _ (incidentHeat_supported w K extent link))
      (certificate_extend _
        (supported_add (cap_supported _ _) (neg_supported (incidentHeat_supported w K extent link)))
        (incidentHeatUpperCertificate hw0 hw1 K extent link)))
    (normalizerUpperCertificate hw0 hw1 K extent hl)

#print axioms slot
#print axioms swap
#print axioms otherStar
#print axioms otherNormalizer
#print axioms starLower
#print axioms starUpper
#print axioms starLower_positive
#print axioms starUpper_nonnegative
#print axioms otherNormalizer_project_pin
#print axioms otherNormalizer_lift_pin
#print axioms inPlaceNormalizer_head_pin
#print axioms full_marginal_pin
#print axioms starCertificate
#print axioms normalizerCertificate
#print axioms normalizerLowerCertificate
#print axioms normalizerUpperCertificate
#print axioms otherNormalizerLowerCertificate
#print axioms otherNormalizerUpperCertificate
#print axioms crossStarComparison

end YMGap.Continuum.BF4ExactSlabCrossExteriorStar
