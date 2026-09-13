/-
# The Jacobi Haar floor on the WEIGHTED original face heat terms

The coefficient pin is applied to the actual ordered slab plaquettes and
their existing faceHeatTerm. Every finite face product, arbitrary Haar
insertion, square certificate, and strict integrated floor transports to
that weighted original polynomial without changing the shared link carrier.

The finite weights are NOT removed here. A quantified original-Haar limit
comparison is still required for the original unweighted action limit,
completed-unit non-nullness, physical vacuum, and spectral gap.
-/

import YMGap.Continuum.JacobiWeightedHeatPolynomial
import YMGap.Continuum.BF4ExactSlabJacobiHaarFloor

namespace YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabJacobiHaarFloor
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The EXISTING original face terms with the finite Jacobi weights.
N is the number of labels; an unweighted cutoff K would contain K+1. -/
def weightedFace (w : Q') (N extent id : Nat) : RatPoly :=
  finitePolySum (fun r => polySmul (JacobiWeightedHeatPolynomial.weight w N r)
    (faceHeatTerm w extent id r)) (List.range N)

/-- Strong coefficient identity, not just scalar evaluation equality. -/
theorem face_coeffEqv {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent id : Nat) : RatPolyCoeffEqv (faceApprox w N extent id) (weightedFace w N extent id) :=
  JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial hw0 hw1 N (faceScalar extent id)

/-- Every shared-link product is pinned, even before choosing a Haar probe. -/
theorem product_coeffEqv {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent : Nat) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polynomialProduct (faceApprox w N extent) ids)
      (polynomialProduct (weightedFace w N extent) ids)
  | [] => RatPolyCoeffEqv.refl _
  | id :: ids => (face_coeffEqv hw0 hw1 N extent id).mul (product_coeffEqv hw0 hw1 N extent ids)

/-- The actual Haar value agrees with EVERY insertion polynomial present.
No disjointness of its variables from the face product is required. -/
theorem product_haar_insertion {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent blocks : Nat) (ids : List Nat) (insertion : RatPoly) :
    quaternionHaar blocks (polyMul insertion (polynomialProduct (faceApprox w N extent) ids))
      ≈ quaternionHaar blocks (polyMul insertion (polynomialProduct (weightedFace w N extent) ids)) :=
  RatPolyCoeffEqv.haarCarrier (product_coeffEqv hw0 hw1 N extent ids) insertion

/-- Explicit ordinary square certificate for the weighted original action. -/
def weighted_product_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (polynomialProduct (weightedFace w N extent) ids) :=
  .ofCoeff (product_coeffEqv hw0 hw1 N extent ids).symm (product_certificate hw0 hw1 N extent ids hids)

/-- The finite original-weighted Haar floor is uniform in N>=1 at the
explicit supplied w and face list, NOT coupling/volume/spacing uniform. -/
theorem productFloor_le_weightedHaar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent : Nat) (hN : 1 ≤ N) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    productFloor w ids ≤ quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polynomialProduct (weightedFace w N extent) ids) :=
  Q'.le_trans' _ _ _ (productFloor_le_haar hw0 hw1 N extent hN ids hids)
    (Q'.le_of_eqv (haar_of_coeff (product_coeffEqv hw0 hw1 N extent ids)))

theorem full_weightedHaar_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent : Nat) (hN : 1 ≤ N) :
    (0 : Q') < quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polynomialProduct (weightedFace w N extent) (slabPhysicalFaceEdges extent)) :=
  Q'.pos_of_lt_of_le (productFloor_pos hw0 hw1 _)
    (productFloor_le_weightedHaar hw0 hw1 N extent hN _ (fun _ h => h))

end YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin

#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin.weightedFace
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin.face_coeffEqv
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin.product_coeffEqv
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin.product_haar_insertion
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin.weighted_product_certificate
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin.productFloor_le_weightedHaar
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin.full_weightedHaar_positive
