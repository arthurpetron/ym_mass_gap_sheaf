/-
# Positive normalized polynomial expectations for the ORIGINAL slab action

For every rational 0<w<1 and odd slab, E(p) is the original interacting
Haar numerator divided by the SAME original partition function Z.
It is linear, normalized, respects quaternion-Haar relations and is
positive on supported ordinary squares. Its CReal representative has
an explicit rational Cauchy modulus depending on w, the slab and p.

Ordinary square positivity is not reflected OS positivity. No observable
action on the previous boundary completion, compatible slab maps, physical
time transfer, stationary vacuum or uniform physical gap is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
import YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
import YMGap.Continuum.BoundedRationalCauchyProduct

namespace YMGap.Continuum.BF4ExactSlabPolynomialExpectation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BoundedRationalCauchyProduct

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "faces" => slabPhysicalFaceEdges (centralExtent half)
local notation "N" => numeratorLimit w hw0 hw1 blocks (centralExtent half) faces
local notation "lambda" => actionReciprocal w hw0 hw1 half

def expectation (p : RatPoly) : CReal := CReal.mul (N p) lambda

theorem expectation_one : CReal.Equiv (expectation w hw0 hw1 half polyOne) CReal.cone :=
  (Pivot2.mul_congr_left (numeratorLimit_one w hw0 hw1 blocks (centralExtent half) faces)).trans
    (action_mul_reciprocal w hw0 hw1 half)

theorem expectation_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    CReal.Equiv (expectation w hw0 hw1 half p) (expectation w hw0 hw1 half q) :=
  Pivot2.mul_congr_left (numeratorLimit_congr w hw0 hw1 blocks (centralExtent half) faces h)

theorem expectation_carrier_congr {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    CReal.Equiv (expectation w hw0 hw1 half p) (expectation w hw0 hw1 half q) :=
  Pivot2.mul_congr_left (numeratorLimit_carrier_congr w hw0 hw1 blocks (centralExtent half) faces h)

theorem expectation_add (p q : RatPoly) :
    CReal.Equiv (expectation w hw0 hw1 half (polyAdd p q))
      (CReal.add (expectation w hw0 hw1 half p) (expectation w hw0 hw1 half q)) :=
  (Pivot2.mul_congr_left (numeratorLimit_add w hw0 hw1 blocks (centralExtent half) faces p q)).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_mul_eqv ((N p).approx n) ((N q).approx n) ((lambda).approx n)))

theorem expectation_smul (c : Q') (p : RatPoly) :
    CReal.Equiv (expectation w hw0 hw1 half (polySmul c p))
      (CReal.mul (CReal.ofQ' c) (expectation w hw0 hw1 half p)) :=
  (Pivot2.mul_congr_left (numeratorLimit_smul w hw0 hw1 blocks (centralExtent half) faces c p)).trans
    (CRealAlg.cmul_assoc _ _ _)

theorem reciprocal_nonnegative : CReal.leEv (CReal.ofQ' 0) lambda :=
  CReal.leEv_ofQ'_of_approx_ge (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))

theorem expectation_certificate_nonnegative (p : RatPoly) (P : Certificate blocks p) :
    CReal.leEv (CReal.ofQ' 0) (expectation w hw0 hw1 half p) :=
  CReal.mul_nonneg
    (numeratorLimit_certificate_nonnegative w hw0 hw1 (centralExtent half) faces (fun _ h => h) p P)
    (reciprocal_nonnegative w hw0 hw1 half)

/-- Positivity is on ordinary squares of supported real polynomial observables. -/
theorem expectation_square_nonnegative (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    CReal.leEv (CReal.ofQ' 0) (expectation w hw0 hw1 half (polyMul p p)) :=
  expectation_certificate_nonnegative w hw0 hw1 half _ (.square p hp)

/-- Multiplication by the SAME original partition function recovers the original numerator. -/
theorem expectation_recover (p : RatPoly) :
    CReal.Equiv (CReal.mul (expectation w hw0 hw1 half p) (fullActionLimit w hw0 hw1 half)) (N p) :=
  (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right ((CRealAlg.cmul_comm _ _).trans (action_mul_reciprocal w hw0 hw1 half))).trans
      (CRealAlg.cmul_cone (N p)))

def numeratorBound (p : RatPoly) : Q' :=
  polynomialCoefficientL1 p * heatProductBound w (centralExtent half) faces

include hw0 in
theorem numeratorBound_nonnegative (p : RatPoly) : (0 : Q') ≤ numeratorBound w half p :=
  Q'.mul_nonneg _ _ (polynomialCoefficientL1_nonnegative p)
    (heatProductBound_nonnegative (Q'.le_of_lt hw0) _ _)

theorem numerator_approx_abs_le (p : RatPoly) (n : Nat) : Q'.abs ((N p).approx n) ≤ numeratorBound w half p :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (heatProduct_coefficientL1_bound hw0 hw1 _ _ _)
        (polynomialCoefficientL1_nonnegative p)))

/-- A computed common absolute bound on the two unmultiplied representatives. -/
def productBound (p : RatPoly) : Q' := numeratorBound w half p + reciprocalCeiling w hw0 hw1 half + 1

theorem productBound_pos (p : RatPoly) : (0 : Q') < productBound w hw0 hw1 half p :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _
      (Q'.zero_le_add _ _ (numeratorBound_nonnegative w hw0 half p)
        (Q'.le_of_lt (reciprocalCeiling_pos w hw0 hw1 half))))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem numerator_approx_productBound (p : RatPoly) (n : Nat) :
    Q'.abs ((N p).approx n) ≤ productBound w hw0 hw1 half p :=
  Q'.le_trans' _ _ _ (numerator_approx_abs_le w hw0 hw1 half p n)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (reciprocalCeiling_pos w hw0 hw1 half)))
      (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one))

theorem reciprocal_approx_productBound (p : RatPoly) (n : Nat) :
    Q'.abs ((lambda).approx n) ≤ productBound w hw0 hw1 half p := by
  rw [ExpNeg.abs_of_nonneg (Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))]
  exact Q'.le_trans' _ _ _ (actionReciprocal_approx_le w hw0 hw1 half n)
    (Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (numeratorBound_nonnegative w hw0 half p))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
      (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one))

/-- Explicit modulus for the ACTUAL normalized CReal approximants. -/
def expectationCauchy (p : RatPoly) : CReal.QCauchy (expectation w hw0 hw1 half p).approx :=
  productCauchy
    (representativeCauchy _ (numeratorCauchy w hw0 hw1 blocks (centralExtent half) faces p))
    (representativeCauchy _ (PositiveRationalCauchyReciprocal.reciprocalCauchy
      (positiveSampleCauchy w hw0 hw1 half) (fullActionFloorCertificate w hw0 hw1 half).floor
      (fullActionFloorCertificate w hw0 hw1 half).floor_pos (positiveSample_floor w hw0 hw1 half)))
    (productBound w hw0 hw1 half p) (productBound_pos w hw0 hw1 half p)
    (numerator_approx_productBound w hw0 hw1 half p) (reciprocal_approx_productBound w hw0 hw1 half p)

def expectationModulus (p : RatPoly) (epsilon : Q') : Nat := (expectationCauchy w hw0 hw1 half p).M epsilon

theorem expectationModulus_eq (p : RatPoly) (epsilon : Q') :
    expectationModulus w hw0 hw1 half p epsilon =
      (BoundedRationalCauchyProduct.tolerance (productBound w hw0 hw1 half p)
        (productBound_pos w hw0 hw1 half p) epsilon).den := by
  change max _ _ = _
  exact Nat.max_self _

theorem expectation_approx_close (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (i j : Nat) (hi : expectationModulus w hw0 hw1 half p epsilon ≤ i)
    (hj : expectationModulus w hw0 hw1 half p epsilon ≤ j) :
    (expectation w hw0 hw1 half p).approx i ≤ (expectation w hw0 hw1 half p).approx j + epsilon ∧
    (expectation w hw0 hw1 half p).approx j ≤ (expectation w hw0 hw1 half p).approx i + epsilon :=
  (expectationCauchy w hw0 hw1 half p).bound epsilon he i j hi hj

end YMGap.Continuum.BF4ExactSlabPolynomialExpectation

#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_one
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_congr
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_add
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_smul
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.reciprocal_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_certificate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_square_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_recover
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.numeratorBound
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.numeratorBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.numerator_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.productBound
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.productBound_pos
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.numerator_approx_productBound
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.reciprocal_approx_productBound
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectationCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectationModulus
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectationModulus_eq
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialExpectation.expectation_approx_close
