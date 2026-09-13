/-
# GNS data for the ORIGINAL finite-cutoff plaquette reflected form

The carrier consists of actual plaquette expressions; its equivalence retains
both original lower and reflected-upper coefficient identities. The form is
the full original interacting Haar numerator. Its symmetry, bilinearity and
positivity supply the existing GNSData, hence sharp Cauchy--Schwarz and
radical descent, with no new analytic input.

The cutoff is still finite. This is not the physical cutoff-limit completion,
an inter-slab identification, a time operator or a spectral-gap claim.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance

namespace YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def expressionEqv {half : Nat} (e f : PlaquetteExpression half) : Prop :=
  RatPolyCoeffEqv (lower e) (lower f) ∧ RatPolyCoeffEqv (upper e) (upper f)

def rawForm (w : Q') (K : Nat) {half : Nat} (e f : PlaquetteExpression half) : Q' :=
  numerator w (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
    (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) (lower f)) K

theorem rawForm_symm (w : Q') (K : Nat) {half : Nat} (e f : PlaquetteExpression half) :
    rawForm w K e f ≈ rawForm w K f e :=
  Q'.eqv_trans _ _ _
    (numerator_reflection_image w K half ((upper_reflection e).mul (lower_reflection f))
      (supported_polyMul (upper_supported e) (lower_supported f))
      (supported_polyMul (lower_supported e) (upper_supported f)))
    (haar_of_coeff_eqv _ ((RatPolyCoeffEqv.mul_comm (lower e) (upper f)).mul_right _))

theorem rawForm_add_left (w : Q') (K : Nat) {half : Nat} (e f g : PlaquetteExpression half) :
    rawForm w K (.add e f) g ≈ rawForm w K e g + rawForm w K f g := by
  change quaternionHaar _ (polyMul (polyMul (polyAdd (upper e) (upper f)) (lower g)) _) ≈ _
  rw [polyMul_add_left_exact, polyMul_add_left_exact]
  exact quaternionHaar_append _ _ _

theorem rawForm_smul_left (w : Q') (K : Nat) {half : Nat} (c : Q') (e f : PlaquetteExpression half) :
    rawForm w K (.smul c e) f ≈ c * rawForm w K e f :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    (((RatPolyCoeffEqv.polyMul_smul_left c (upper e) (lower f)).mul_right (fullHeatProduct w K half)).trans
      (RatPolyCoeffEqv.polyMul_smul_left _ _ _)))
    (quaternionHaar_polySmul _ _ _)

theorem rawForm_nonnegative (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    (0 : Q') ≤ rawForm w K e e :=
  Q'.le_trans' _ _ _ (reflected_numerator_nonnegative w K e hw)
    (Q'.le_of_eqv (reflected_upper_numerator w K e e))

/-- The unit diagonal is the SAME full original action integral at this cutoff. -/
theorem rawForm_unit (w : Q') (K half : Nat) :
    rawForm w K (.unit : PlaquetteExpression half) .unit ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (fullHeatProduct w K half) :=
  haar_of_coeff_eqv _ (((RatPolyCoeffEqv.one_mul polyOne).mul_right _).trans (RatPolyCoeffEqv.one_mul _))

private theorem zero_add (p : RatPoly) : RatPolyCoeffEqv (polyAdd (polySmul 0 polyOne) p) p :=
  ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl p)).trans (RatPolyCoeffEqv.zero_add p)

private theorem neg_add (p : RatPoly) : RatPolyCoeffEqv (polyAdd (polySmul (-1) p) p) (polySmul 0 polyOne) :=
  (RatPolyCoeffEqv.add_comm _ _).trans
    ((RatPolyCoeffEqv.add_neg_smul p).trans (RatPolyCoeffEqv.zero_smul polyOne).symm)

def finiteGNSData (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : GNSData where
  V := PlaquetteExpression half
  veq := expressionEqv
  veq_refl := fun _ => ⟨RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _⟩
  veq_symm := fun h => ⟨h.1.symm, h.2.symm⟩
  veq_trans := fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  zero := .smul 0 .unit
  add := .add
  neg := .smul (-1)
  smul := .smul
  add_congr := fun h h' => ⟨h.1.add h'.1, h.2.add h'.2⟩
  neg_congr := fun h => ⟨RatPolyCoeffEqv.smul _ h.1, RatPolyCoeffEqv.smul _ h.2⟩
  smul_congr := fun c {_ _} h => ⟨RatPolyCoeffEqv.smul c h.1, RatPolyCoeffEqv.smul c h.2⟩
  add_assoc := fun _ _ _ => ⟨RatPolyCoeffEqv.add_assoc _ _ _, RatPolyCoeffEqv.add_assoc _ _ _⟩
  add_comm := fun _ _ => ⟨RatPolyCoeffEqv.add_comm _ _, RatPolyCoeffEqv.add_comm _ _⟩
  zero_add := fun _ => ⟨zero_add _, zero_add _⟩
  neg_add := fun _ => ⟨neg_add _, neg_add _⟩
  B := rawForm w K
  B_congr_left := fun b h => haar_of_coeff_eqv _ ((h.2.mul_right (lower b)).mul_right (fullHeatProduct w K half))
  B_add_left := rawForm_add_left w K
  B_smul_left := rawForm_smul_left w K
  B_symm := rawForm_symm w K
  self_nonneg := rawForm_nonnegative w hw K

theorem rawForm_cauchySchwarz (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat} (e f : PlaquetteExpression half) :
    rawForm w K e f * rawForm w K e f ≤ rawForm w K e e * rawForm w K f f :=
  (finiteGNSData w hw K half).cauchy_schwarz e f

theorem rawForm_radical_zero (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat}
    (e f : PlaquetteExpression half) (he : rawForm w K e e ≈ 0) : rawForm w K e f ≈ 0 :=
  (finiteGNSData w hw K half).radical_form_zero e f he

end YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.expressionEqv
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm_add_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm_unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.finiteGNSData
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS.rawForm_radical_zero
