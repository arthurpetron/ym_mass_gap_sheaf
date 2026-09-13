/-
# Reflected positivity for the ORIGINAL normalized plaquette functional

An arbitrary expression in lower-half plaquette characters is multiplied
by the ORIGINAL lower heat product. The proved temporal change of variables
retains its gauge-invariant characters and changes only the crossing action
to the actual spatial Gram interface. Its finite reflected-square expansion
therefore equals the original full-action numerator, not an auxiliary law.

Passing through the existing original numerator CReal and SAME positive Z
proves E(theta(p)*p)>=0 on this concrete plaquette-generated algebra.
This does not assert its completeness among all gauge observables, identify
the previous completion with the physical OS carrier, or construct transfer,
a stationary vacuum, a uniform gap or a continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
import YMGap.Continuum.BF4ExactSlabPolynomialExpectation

namespace YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem sum_supported {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a :: xs => supported_add (h a) (sum_supported f h xs)

private theorem product_supported {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (polynomialProduct f xs)
  | [] => supported_one blocks
  | a :: xs => supported_polyMul (h a) (product_supported f h xs)

theorem fullHeatProduct_supported (w : Q') (K half : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (fullHeatProduct w K half) :=
  product_supported _ (fun _ => sum_supported _
    (fun _ => supported_smul (original_character_support _ _ _) _) _) _

private theorem haar_temporal {half : Nat} {p q : RatPoly} (h : TemporalImage half p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length q) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length q :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (applyTemporalTranslationLedger_haar _ _ _ hp))
    (PaddedPolynomialCoeffEqv.haar h (applyTemporalTranslationLedger_supported _ _ _ hp) hq)

private theorem rearrange (u p L I U : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul u p) (polyMul L (polyMul I U)))
      (polyMul (polyMul p L) (polyMul I (polyMul u U))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4))))
    (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.mul (.var 0) (.var 4))))
    (by decide) (fun n => match n with | 0 => u | 1 => p | 2 => L | 3 => I | _ => U)

variable (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half)

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "L" => lowerObservable w K half (fun _ => 1)
local notation "U" => upperObservable w K half (fun _ => 1)
local notation "I" => interfaceHeatProduct w K half
local notation "G" => interfacePolynomial w K half
local notation "base" => polyMul L (polyMul I U)
local notation "temporalBase" => temporalObservableIntegrand w K half (fun _ => 1) (fun _ => 1)

theorem unit_product : RatPolyCoeffEqv base (fullHeatProduct w K half) :=
  ((lowerObservable_one w K half).mul ((RatPolyCoeffEqv.refl I).mul (upperObservable_one w K half))).trans
    (central_product_factorization half (BF4ExactSlabAllExtentObservableHaarForm.faceHeatPolynomial w K (centralExtent half))).symm

def dressedLower : RatPoly := polyMul (lower e) L
def dressedUpper : RatPoly := polyMul (upper e) U

theorem dressedLower_supported : SupportedQuaternionBlocks blocks (dressedLower w K e) :=
  supported_polyMul (lower_supported e) (lowerObservable_support w K half _)

theorem dressedUpper_supported : SupportedQuaternionBlocks blocks (dressedUpper w K e) :=
  supported_polyMul (upper_supported e) (upperObservable_support w K half _)

theorem dressed_reflection : ReflectionImage (centralExtent half) (dressedLower w K e) (dressedUpper w K e) :=
  (lower_reflection e).mul (lowerObservable_reflection w K half _)

def squareExpansion (hw : (0 : Q') ≤ w) : LocalSquareExpansion half
    (reflectedInterfacePolynomial w K half (dressedLower w K e)) :=
  reflectedInterfaceExpansion hw K half _ (dressedLower_supported w K e)
    ((lower_local e).mul (lowerObservable_local w K half _))

/-- Same full action numerator, with the independently defined reflected observable. -/
theorem upper_numerator_spatialGram :
    numerator w blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (polyMul (upper e) (lower e)) K ≈
      quaternionHaar blocks (polyMul (dressedLower w K e) (polyMul G (dressedUpper w K e))) := by
  have hb : SupportedQuaternionBlocks blocks base := supported_polyMul (lowerObservable_support w K half _)
    (supported_polyMul (interfaceHeatProduct_support w K half) (upperObservable_support w K half _))
  have hi : TemporalImage half base temporalBase := observableProduct_image w K half _ _
  have ht := haar_temporal (((upper_image e).mul (lower_image e)).mul hi)
    (supported_polyMul (supported_polyMul (upper_supported e) (lower_supported e)) hb)
    (supported_polyMul (supported_polyMul (temporalUpper_supported e) (temporalLower_supported e))
      (temporalObservableIntegrand_support w K half _ _))
  have hg : HaarCarrierEqv blocks
      (polyMul (polyMul (temporalUpper e) (temporalLower e)) temporalBase)
      (polyMul (polyMul (upper e) (lower e)) (polyMul L (polyMul G U))) :=
    HaarCarrierEqv.mul (HaarCarrierEqv.mul (temporalUpper_original e) (temporalLower_original e))
      (HaarCarrierEqv.mul (temporalLower_haar_original w K half _)
        (HaarCarrierEqv.mul (temporalInterface_haar_gram w K half) (temporalUpper_haar_original w K half _)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks ((unit_product w K (half := half)).symm.mul_left _))
    (Q'.eqv_trans _ _ _ ht (Q'.eqv_trans _ _ _ (QuaternionHaarSquareCertificate.haar_of_carrier hg)
      (haar_of_coeff_eqv blocks (rearrange _ _ _ _ _))))

theorem upper_numerator_eq_squareValue (hw : (0 : Q') ≤ w) :
    numerator w blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (polyMul (upper e) (lower e)) K ≈ (squareExpansion w K e hw).squareValue := by
  have hG := (interfaceExpansion hw K half).polynomialSupported
  have hd := dressedLower_supported w K e
  have ht := reflectCorrectedSlabPolynomial_support (centralExtent half) (dressedLower w K e)
  have hr := ((PaddedPolynomialCoeffEqv.refl blocks (dressedLower w K e)).mul
    ((PaddedPolynomialCoeffEqv.refl blocks G).mul (dressed_reflection w K e))).haar
      (supported_polyMul hd (supported_polyMul hG ht))
      (supported_polyMul hd (supported_polyMul hG (dressedUpper_supported w K e)))
  have horder : RatPolyCoeffEqv
      (polyMul (dressedLower w K e) (polyMul G (reflectCorrectedSlabPolynomial (centralExtent half) (dressedLower w K e))))
      (reflectedInterfacePolynomial w K half (dressedLower w K e)) :=
    ((RatPolyCoeffEqv.mul_comm _ _).mul_left _).trans
      ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans ((RatPolyCoeffEqv.mul_comm _ _).mul_right _))
  exact Q'.eqv_trans _ _ _ (upper_numerator_spatialGram w K e)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hr)
      (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks horder) (squareExpansion w K e hw).haar_eq_squareValue))

def reflectedInsertion : RatPoly := polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (lower e)) (lower e)

/-- Literal link reflection for any two independently supplied plaquette expressions. -/
theorem reflected_upper_numerator (f : PlaquetteExpression half) :
    numerator w blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (lower e)) (lower f)) K ≈
    numerator w blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (polyMul (upper e) (lower f)) K :=
  ((PaddedPolynomialCoeffEqv.mul (lower_reflection e) (PaddedPolynomialCoeffEqv.refl blocks (lower f))).mul
    (PaddedPolynomialCoeffEqv.refl blocks (fullHeatProduct w K half))).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (lower_supported f))
        (fullHeatProduct_supported w K half))
      (supported_polyMul (supported_polyMul (upper_supported e) (lower_supported f)) (fullHeatProduct_supported w K half))

/-- The literal link reflection, with all physical action variables retained. -/
theorem reflected_numerator_eq_squareValue (hw : (0 : Q') ≤ w) :
    numerator w blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e) K ≈
      (squareExpansion w K e hw).squareValue :=
  Q'.eqv_trans _ _ _ (reflected_upper_numerator w K e e) (upper_numerator_eq_squareValue w K e hw)

theorem reflected_numerator_nonnegative (hw : (0 : Q') ≤ w) :
    (0 : Q') ≤ numerator w blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e) K :=
  Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (squareExpansion w K e hw).haar_nonnegative
      (Q'.le_of_eqv (squareExpansion w K e hw).haar_eq_squareValue))
    (Q'.ge_of_eqv (reflected_numerator_eq_squareValue w K e hw))

theorem reflected_numeratorLimit_nonnegative (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.leEv (CReal.ofQ' 0)
      (numeratorLimit w hw0 hw1 blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e)) :=
  CReal.leEv_ofQ'_of_approx_ge (fun _ => reflected_numerator_nonnegative w _ e (Q'.le_of_lt hw0))

/-- Reflection positivity of the ORIGINAL normalized functional, on this concrete algebra. -/
theorem expectation_reflection_nonnegative (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.leEv (CReal.ofQ' 0) (expectation w hw0 hw1 half (reflectedInsertion e)) :=
  CReal.mul_nonneg (reflected_numeratorLimit_nonnegative w e hw0 hw1)
    (BF4ExactSlabPolynomialExpectation.reciprocal_nonnegative w hw0 hw1 half)

theorem expectation_reflection_eq_upper (f : PlaquetteExpression half)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.Equiv
      (expectation w hw0 hw1 half (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (lower e)) (lower f)))
      (expectation w hw0 hw1 half (polyMul (upper e) (lower f))) :=
  Pivot2.mul_congr_left (CReal.Equiv_of_ofQ'_limit_close
    (numerator_converges w hw0 hw1 blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) _)
    (numerator_converges w hw0 hw1 blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) _)
    (fun epsilon he => ⟨0, fun k _ => eqv_close (reflected_upper_numerator w k e f) epsilon he⟩))

/-- The distinguished unit has reflected value one, so this is not a zero functional. -/
theorem expectation_reflected_unit (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    CReal.Equiv (expectation w hw0 hw1 half (reflectedInsertion (.unit : PlaquetteExpression half))) CReal.cone :=
  (expectation_reflection_eq_upper w (.unit : PlaquetteExpression half) .unit hw0 hw1).trans
    ((expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.one_mul polyOne)).trans
      (expectation_one w hw0 hw1 half))

end YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.fullHeatProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.unit_product
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.dressedLower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.dressedUpper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.dressedLower_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.dressedUpper_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.dressed_reflection
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.squareExpansion
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.upper_numerator_spatialGram
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.upper_numerator_eq_squareValue
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.reflectedInsertion
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.reflected_upper_numerator
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.reflected_numerator_eq_squareValue
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.reflected_numerator_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.reflected_numeratorLimit_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.expectation_reflection_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.expectation_reflection_eq_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity.expectation_reflected_unit
