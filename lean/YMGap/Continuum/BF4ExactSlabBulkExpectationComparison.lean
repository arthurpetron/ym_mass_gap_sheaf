/-
# Exact inter-slab comparison for the ORIGINAL normalized action

The source polynomial and original source heat action are embedded together.
The interior integral is the smaller-slab integral, so the previously proved
boundary-response determinant gives the exact difference

    E_large(embed p) - E_small(p) = D(embed p) / (Z_large Z_small).

Both reciprocals are the existing proved original partition reciprocals.
The difference carries explicit QCauchy data, and the bulk image of every
original lower plaquette expression is pinned to the same polynomial map.
All parameters remain explicit. This identity supplies no smallness in the
padding, no volume-uniform reciprocal bound, and no physical transfer gap.
-/

import YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin

namespace YMGap.Continuum.BF4ExactSlabBulkExpectationComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-- The literal bulk observable, not an independently chosen image algebra. -/
theorem lower_bulk_image {half : Nat} (padding : Nat) :
    ∀ e : PlaquetteExpression half,
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
      ((slabEmbedding half padding).polynomial (lower e))
      (lower (bulkAtTime padding ⟨0, Nat.zero_lt_succ padding⟩ e))
  | .unit => (slabEmbedding half padding).polynomial_one_prefix
  | .character id hi spin => by
      change QuaternionPrefixPolynomialEqv _ _ (characterPolynomial _ spin)
      have hp := (mem_centralLowerFaceIds.mp hi).1
      rw [bulkFaceId_pin hp, Nat.sub_zero]
      exact character_pin (half := half) (padding := padding) (slabPlaquetteAt_mem hp) spin
  | .add e f => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding half padding).polynomial (polyAdd (lower e) (lower f))) _
      rw [BlockEmbedding.polynomial_add]
      exact (lower_bulk_image padding e).append (lower_bulk_image padding f)
  | .mul e f => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding half padding).polynomial (polyMul (lower e) (lower f))) _
      rw [BlockEmbedding.polynomial_mul]
      exact (lower_bulk_image padding e).mul (lower_bulk_image padding f)
  | .smul c e => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding half padding).polynomial (polySmul c (lower e))) _
      rw [BlockEmbedding.polynomial_smul]
      exact (lower_bulk_image padding e).smul c

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Prefix equality is used only with supported insertions and the actual
full heat product. No variables outside the carrier are discarded. -/
theorem expectation_prefix (half : Nat) {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent half)).length p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length q) :
    Equiv (expectation w hw0 hw1 half p) (expectation w hw0 hw1 half q) := by
  apply Pivot2.mul_congr_left
  apply Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ _ _ p)
    (numerator_converges w hw0 hw1 _ _ _ q)
  intro epsilon he
  refine ⟨0, fun K _ => eqv_close ?_ epsilon he⟩
  exact quaternionHaar_prefixPolynomialEqv _ (h.mul (.refl _ _))
    (supported_polyMul hp (fullHeatProduct_supported w K half))
    (supported_polyMul hq (fullHeatProduct_supported w K half))

variable (half padding : Nat)

local notation "E" => slabEmbedding half padding
local notation "Zs" => fullActionLimit w hw0 hw1 half
local notation "Ls" => actionReciprocal w hw0 hw1 half
local notation "Ll" => actionReciprocal w hw0 hw1 (half+padding)
local notation "Ns" => numeratorLimit w hw0 hw1 (List.length (boundaryCompleteSlabLinks (centralExtent half)))
  (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))

theorem comparison_cross (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p) :
    Equiv (CReal.sub (CReal.mul (expectation w hw0 hw1 (half+padding) ((E).polynomial p)) Zs) (Ns p))
      (CReal.mul (boundaryResponse w hw0 hw1 half padding ((E).polynomial p)) Ll) := by
  have hpin := (CReal.sub_congr_left (Pivot2.mul_congr_right
    (A := expectation w hw0 hw1 (half+padding) ((E).polynomial p))
    (interiorPartition_small w hw0 hw1 half padding))).trans
    (CReal.sub_congr_right (interiorLimit_small w hw0 hw1 half padding p hp))
  exact hpin.symm.trans (normalized_boundary_response w hw0 hw1 half padding ((E).polynomial p))

def expectationDifference (p : RatPoly) : CReal :=
  CReal.sub (expectation w hw0 hw1 (half+padding) ((E).polynomial p)) (expectation w hw0 hw1 half p)

/-- All original normalization factors are retained. This is an equality,
not a decay estimate or a claim of consistency between finite-volume laws. -/
theorem expectationDifference_formula (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p) :
    Equiv (expectationDifference w hw0 hw1 half padding p)
      (CReal.mul (CReal.mul (boundaryResponse w hw0 hw1 half padding ((E).polynomial p)) Ll) Ls) := by
  apply Equiv.symm
  refine (Pivot2.mul_congr_left (comparison_cross w hw0 hw1 half padding p hp).symm).trans ?_
  have hd : Equiv
      (CReal.mul (CReal.sub (CReal.mul (expectation w hw0 hw1 (half+padding) ((E).polynomial p)) Zs) (Ns p)) Ls)
      (CReal.sub (CReal.mul (CReal.mul (expectation w hw0 hw1 (half+padding) ((E).polynomial p)) Zs) Ls)
        (CReal.mul (Ns p) Ls)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.sub_mul_eqv _ _ _)
  refine hd.trans (CReal.sub_congr_left ?_)
  exact (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right (action_mul_reciprocal w hw0 hw1 half)).trans (CRealAlg.cmul_cone _))

/-- Modulus for the representative index, at each fixed pair of slabs.
It is explicitly NOT a modulus of convergence as padding increases. -/
def expectationDifferenceCauchy (p : RatPoly) : QCauchy (expectationDifference w hw0 hw1 half padding p).approx :=
  scalarAddCauchy _ _ (expectationCauchy w hw0 hw1 (half+padding) ((E).polynomial p))
    (scalarNegCauchy _ (expectationCauchy w hw0 hw1 half p))

theorem bulk_mean_comparison (e : PlaquetteExpression half) :
    Equiv
      (CReal.sub (expectation w hw0 hw1 (half+padding) (lower (bulkAtTime padding ⟨0, Nat.zero_lt_succ padding⟩ e)))
        (expectation w hw0 hw1 half (lower e)))
      (CReal.mul (CReal.mul (boundaryResponse w hw0 hw1 half padding ((E).polynomial (lower e))) Ll) Ls) :=
  (CReal.sub_congr_left (expectation_prefix w hw0 hw1 (half+padding) (lower_bulk_image padding e)
    ((E).polynomial_supported _) (lower_supported _)).symm).trans
      (expectationDifference_formula w hw0 hw1 half padding (lower e) (lower_supported e))

end YMGap.Continuum.BF4ExactSlabBulkExpectationComparison

#print axioms YMGap.Continuum.BF4ExactSlabBulkExpectationComparison.lower_bulk_image
#print axioms YMGap.Continuum.BF4ExactSlabBulkExpectationComparison.expectation_prefix
#print axioms YMGap.Continuum.BF4ExactSlabBulkExpectationComparison.comparison_cross
#print axioms YMGap.Continuum.BF4ExactSlabBulkExpectationComparison.expectationDifference
#print axioms YMGap.Continuum.BF4ExactSlabBulkExpectationComparison.expectationDifference_formula
#print axioms YMGap.Continuum.BF4ExactSlabBulkExpectationComparison.expectationDifferenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkExpectationComparison.bulk_mean_comparison
