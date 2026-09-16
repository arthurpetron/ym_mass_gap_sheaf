/-
# All-nome certificates for the ORIGINAL reflected spatial Gram heat factors

The existing faceHeat_pin identifies each factor with the heat prefix of
the original lower link times its literal reflected upper inverse. The
general Haar-unit-word theorem removes the old small-nome guards once the
explicit headCutoff(w) is reached. Products retain all shared variables;
the interface and spectator lists are the existing physical lists.

These are ordinary positive certificates and weighted finite comparisons,
not strict centered OS contraction or thermodynamic/continuum estimates.
-/

import YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
import YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate

namespace YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- The original Gram factor minus the same explicit positive floor. -/
def faceFloorCertificate (K half id : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (polyAdd (faceHeatPolynomial w K half id) (polyNeg (cap (headFloor w)))) :=
  .transport (HaarCarrierEqv.add (faceHeat_pin w K half id) (.refl _ _))
    (QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
      (spatialWord_supported _ _) (spatialWord_unit _ _) K hK)

def faceCertificate (K half id : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (faceHeatPolynomial w K half id) :=
  .transport (faceHeat_pin w K half id)
    (QuaternionHaarAllNomeHeatCertificate.prefixCertificate hw0 hw1
      (spatialWord_supported _ _) (spatialWord_unit _ _) K hK)

/-- No late-cutoff condition is needed for the absolute upper interval. -/
def faceInterval (K : Nat) {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    Interval (blocks half) (faceHeatPolynomial w K half id) (prefixCap w) :=
  let P := QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1
    (spatialScalarBound (centralExtent half) (faceLinkA (slabPlaquetteAt (centralExtent half) id))) K
  { support := (faceExpansion (Q'.le_of_lt hw0) K hi).polynomialSupported
    nonnegative := P.nonnegative
    upper := .transport (HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg (faceHeat_pin w K half id))) P.upper
    lower := .transport (HaarCarrierEqv.add (.refl _ _) (faceHeat_pin w K half id)) P.lower }

def productCertificate (K half : Nat) (hK : headCutoff w ≤ K) : (ids : List Nat) →
    Certificate (blocks half) (polynomialProduct (faceHeatPolynomial w K half) ids)
  | [] => .one _
  | id::ids => (faceCertificate hw0 hw1 K half id hK).mul (productCertificate K half hK ids)

/-- Existing full crossing interface, not a replacement factor count. -/
def interfaceCertificate (K half : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (interfacePolynomial w K half) :=
  productCertificate hw0 hw1 K half hK (centralFixedFaceIds half)

/-- Existing spectator action retains all of its original reflected links. -/
def spectatorCertificate (K half : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (spectatorInterface w K half) :=
  productCertificate hw0 hw1 K half hK (spectatorIds half)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly, quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_floor {n : Nat} {p h : RatPoly} {c : Q'}
    (P : Certificate n p) (C : Certificate n (polyAdd h (polyNeg (cap c)))) :
    c*quaternionHaar n p ≤ quaternionHaar n (polyMul p h) := by
  have hpos := (P.mul C).haar_nonnegative
  have hc : quaternionHaar n (polyMul p (cap c)) ≈ c*quaternionHaar n p :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left c p)))
      (quaternionHaar_polySmul n c p)
  have he : quaternionHaar n (polyMul p (polyAdd h (polyNeg (cap c)))) ≈
      quaternionHaar n (polyMul p h) + -(c*quaternionHaar n p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => p | 1 => h | _ => cap c)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (haar_neg n _) (Q'.neg_eqv_congr _ _ hc))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

include hw0 hw1 in
theorem face_weighted_floor (K half id : Nat) (hK : headCutoff w ≤ K)
    {p : RatPoly} (P : Certificate (blocks half) p) :
    headFloor w * quaternionHaar (blocks half) p ≤
      quaternionHaar (blocks half) (polyMul p (faceHeatPolynomial w K half id)) :=
  weighted_floor P (faceFloorCertificate hw0 hw1 K half id hK)

include hw0 hw1 in
/-- Only the number of inserted factors is paid; the positive background is unchanged. -/
theorem product_weighted_floor (K half : Nat) (hK : headCutoff w ≤ K)
    {p : RatPoly} (P : Certificate (blocks half) p) : ∀ ids : List Nat,
    (headFloor w)^ids.length * quaternionHaar (blocks half) p ≤
      quaternionHaar (blocks half) (polyMul p (polynomialProduct (faceHeatPolynomial w K half) ids))
  | [] => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))
  | id::ids => by
      have h := face_weighted_floor hw0 hw1 K half id hK
        (P.mul (productCertificate hw0 hw1 K half hK ids))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
          (product_weighted_floor K half hK P ids) (Q'.le_of_lt (headFloor_positive hw0 hw1)))
          (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
            ((RatPolyCoeffEqv.mul_assoc _ _ _).trans ((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm _ _)))))))

include hw0 hw1 in
theorem product_weighted_upper (K half : Nat) {p : RatPoly} (P : Certificate (blocks half) p)
    (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) :
    quaternionHaar (blocks half) (polyMul p (polynomialProduct (faceHeatPolynomial w K half) ids)) ≤
      (prefixCap w)^ids.length * quaternionHaar (blocks half) p :=
  Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    ((Interval.productUniform (faceHeatPolynomial w K half) (prefixCap w) ids
      (fun id hid => faceInterval hw0 hw1 K (hi id hid))).weighted_haar_bound P)

include hw0 hw1 in
theorem interface_weighted_floor (K half : Nat) (hK : headCutoff w ≤ K)
    {p : RatPoly} (P : Certificate (blocks half) p) :
    (headFloor w)^(centralFixedFaceIds half).length * quaternionHaar (blocks half) p ≤
      quaternionHaar (blocks half) (polyMul p (interfacePolynomial w K half)) :=
  product_weighted_floor hw0 hw1 K half hK P (centralFixedFaceIds half)

include hw0 hw1 in
theorem interface_weighted_upper (K half : Nat) {p : RatPoly} (P : Certificate (blocks half) p) :
    quaternionHaar (blocks half) (polyMul p (interfacePolynomial w K half)) ≤
      (prefixCap w)^(centralFixedFaceIds half).length * quaternionHaar (blocks half) p :=
  product_weighted_upper hw0 hw1 K half P (centralFixedFaceIds half) (fun _ h => h)

end YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.faceFloorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.faceCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.faceInterval
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.productCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.interfaceCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.spectatorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.face_weighted_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.product_weighted_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.product_weighted_upper
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.interface_weighted_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate.interface_weighted_upper
