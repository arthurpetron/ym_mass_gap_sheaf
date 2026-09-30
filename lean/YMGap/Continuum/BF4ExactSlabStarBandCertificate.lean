/-
# Finite positive band for one actual original link star

The incident heat product consists of at most six original slab-face factors.
At the retained all-nome cutoff each factor has the existing strict face
floor, while every face has the existing prefix-cap interval. These produce
two-sided sum-of-squares certificates for the product, and conditional
projection at the actual physical link index transports both certificates.

`inPlaceNormalizer` below means exactly this finite polynomial projection of
the incident heat product. It is not an inverse, and no exterior-factor or
completed marginal identity is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabLinkStarGeometry
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
import YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.SU2QuaternionHaarBlockCertificate
import YMGap.Continuum.SU2QuaternionHaarBlockProjection

namespace YMGap.Continuum.BF4ExactSlabStarBandCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
  (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
  (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor headFloor_positive faceHead_floorCertificate
    headProduct_certificate)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
  (prefixCap facePrefixInterval)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor
  (Certificate.productFloor)

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem cap_supported (n : Nat) (c : Q') :
    SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- The star product retains one explicit Jacobi floor for every incident
original physical face. -/
private def heatProductFloorCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      Certificate (blocks extent)
        (polyAdd (polynomialProduct (faceHeatPolynomial w K extent) ids)
          (polyNeg (cap ((headFloor w) ^ ids.length))))
  | [], _ => by
      have hzero : Certificate (blocks extent) (cap (0 : Q')) :=
        Certificate.constant _ 0 (Q'.le_refl' _)
      have hone : RatPolyCoeffEqv (cap (1 : Q')) polyOne :=
        RatPolyCoeffEqv.one_smul polyOne
      have hcancel : RatPolyCoeffEqv
          (polyAdd polyOne (polyNeg polyOne)) (cap (0 : Q')) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
          (fun _ => polyOne)
      apply Certificate.ofCoeff
        (p := polyAdd polyOne (polyNeg (cap 1))) (q := cap 0)
      · exact ((RatPolyCoeffEqv.refl polyOne).add (RatPolyCoeffEqv.neg hone)).trans hcancel
      · exact hzero
  | id :: ids, hi => by
      have htail : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent :=
        fun j hj => hi j (List.mem_cons_of_mem id hj)
      have hq : Certificate (blocks extent)
          (polynomialProduct (faceHeatPolynomial w K extent) ids) :=
        headProduct_certificate hw0 hw1 K extent hK ids htail
      have hple : Certificate (blocks extent)
          (polyAdd (faceHeatPolynomial w K extent id)
            (polyNeg (cap (headFloor w)))) :=
        faceHead_floorCertificate hw0 hw1 K extent id
          (hi id List.mem_cons_self) hK
      have hqeta : Certificate (blocks extent)
          (polyAdd (polynomialProduct (faceHeatPolynomial w K extent) ids)
            (polyNeg (cap ((headFloor w) ^ ids.length)))) :=
        heatProductFloorCertificate hw0 hw1 K extent hK ids htail
      have hprod := Certificate.productFloor hq hple hqeta
        (Q'.le_of_lt (headFloor_positive hw0 hw1))
      simpa [polynomialProduct, Q'.pow_succ] using hprod

/-- The actual incident-star heat product has the product floor
`headFloor(w) ^ incidentIds.length`. -/
def incidentHeatLowerCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link) :
    Certificate (blocks extent)
      (polyAdd (incidentHeat w K extent link)
        (polyNeg (cap ((headFloor w) ^ (incidentIds extent link).length)))) := by
  exact heatProductFloorCertificate hw0 hw1 K extent hK
    (incidentIds extent link) (fun _ hi => incidentIds_physical hi)

/-- The same incident-star product is bounded above by the product of the
individual prefix caps. -/
def incidentHeatUpperCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (link : Z4Link) :
    Certificate (blocks extent)
      (polyAdd (cap ((prefixCap w) ^ (incidentIds extent link).length))
        (polyNeg (incidentHeat w K extent link))) := by
  exact (Interval.productUniform (faceHeatPolynomial w K extent) (prefixCap w)
    (incidentIds extent link)
    (fun id hi => facePrefixInterval hw0 hw1 K extent id (incidentIds_physical hi))).upper

/-- The actual in-place conditional projection of the incident star at the
selected link's physical block index. This is only a polynomial definition;
it makes no completed marginal or exterior-factor claim. -/
def inPlaceNormalizer (w : Q') (K extent : Nat) (link : Z4Link) : RatPoly :=
  project ((boundaryCompleteSlabLinks extent).idxOf link)
    (incidentHeat w K extent link)

theorem inPlaceNormalizer_supported (w : Q') (K extent : Nat) (link : Z4Link) :
    SupportedQuaternionBlocks (blocks extent) (inPlaceNormalizer w K extent link) :=
  project_supported _ (incidentHeat_supported w K extent link)

theorem inPlaceNormalizer_independent (w : Q') (K extent : Nat) (link : Z4Link) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf link)
      (inPlaceNormalizer w K extent link) :=
  project_independent _ _

private def projectLowerCertificate {n j : Nat} (hj : j < n)
    {p : RatPoly} {c : Q'} (hp : SupportedQuaternionBlocks n p)
    (P : Certificate n (polyAdd p (polyNeg (cap c)))) :
    Certificate n (polyAdd (project j p) (polyNeg (cap c))) := by
  have h : RatPolyCoeffEqv (project j (polyAdd p (polyNeg (cap c))))
      (polyAdd (project j p) (polyNeg (cap c))) := by
    rw [project_add]
    exact (RatPolyCoeffEqv.refl _).add
      ((project_neg j _).trans (RatPolyCoeffEqv.neg (project_cap j c)))
  exact .ofCoeff h.symm
    (project_certificate n j hj
      (supported_add hp (neg_supported (cap_supported n c))) P)

private def projectUpperCertificate {n j : Nat} (hj : j < n)
    {p : RatPoly} {c : Q'} (hp : SupportedQuaternionBlocks n p)
    (P : Certificate n (polyAdd (cap c) (polyNeg p))) :
    Certificate n (polyAdd (cap c) (polyNeg (project j p))) := by
  have h : RatPolyCoeffEqv (project j (polyAdd (cap c) (polyNeg p)))
      (polyAdd (cap c) (polyNeg (project j p))) := by
    rw [project_add]
    exact (project_cap j c).add (project_neg j p)
  exact .ofCoeff h.symm
    (project_certificate n j hj
      (supported_add (cap_supported n c) (neg_supported hp)) P)

/-- Projection at the actual physical link preserves the strict star floor. -/
def inPlaceNormalizer_lowerCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    Certificate (blocks extent)
      (polyAdd (inPlaceNormalizer w K extent link)
        (polyNeg (cap ((headFloor w) ^ (incidentIds extent link).length)))) := by
  exact projectLowerCertificate (List.idxOf_lt_length_of_mem hl)
    (incidentHeat_supported w K extent link)
    (incidentHeatLowerCertificate hw0 hw1 K extent hK link)

/-- Projection at the actual physical link preserves the prefix-cap ceiling. -/
def inPlaceNormalizer_upperCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    Certificate (blocks extent)
      (polyAdd (cap ((prefixCap w) ^ (incidentIds extent link).length))
        (polyNeg (inPlaceNormalizer w K extent link))) := by
  exact projectUpperCertificate (List.idxOf_lt_length_of_mem hl)
    (incidentHeat_supported w K extent link)
    (incidentHeatUpperCertificate hw0 hw1 K extent link)

end YMGap.Continuum.BF4ExactSlabStarBandCertificate

#print axioms YMGap.Continuum.BF4ExactSlabStarBandCertificate.incidentHeatLowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabStarBandCertificate.incidentHeatUpperCertificate
#print axioms YMGap.Continuum.BF4ExactSlabStarBandCertificate.inPlaceNormalizer
#print axioms YMGap.Continuum.BF4ExactSlabStarBandCertificate.inPlaceNormalizer_supported
#print axioms YMGap.Continuum.BF4ExactSlabStarBandCertificate.inPlaceNormalizer_independent
#print axioms YMGap.Continuum.BF4ExactSlabStarBandCertificate.inPlaceNormalizer_lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabStarBandCertificate.inPlaceNormalizer_upperCertificate
