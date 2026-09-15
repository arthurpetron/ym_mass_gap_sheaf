/-
# The finite interface floor is pinned to the ORIGINAL full-action numerator

The existing temporal-gauge/reflection identity identifies the ORIGINAL
reflected numerator with Q_w(p), where p is the observable multiplied by
the ORIGINAL lower bulk heat product. Apply the finite interface comparison
to that SAME p. The resulting reference changes only crossing coefficients
to their nome-one values; it retains all original bulk dressing and shared
links. It is not a different normalized Gibbs state.

This proves a positive, explicit w/cutoff/extent-dependent lower factor
and the exact finite nullity equivalence. It does not pass that factor
through cutoff or thermodynamic limits, construct a transfer preimage, or
identify the reference form with the completed norm. Completed T2 range
density, full-space zero-time continuity, physical Hamiltonian and
continuum/Clay conclusions remain open.
-/

import YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity
import YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity

namespace YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity (lowerObservable_local)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def originalQuadratic (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  numerator w (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
    (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e) K

/-- The original lower interaction remains inside the same polynomial. -/
def retainedBulkReference (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  interfaceForm 1 K half (dressedLower w K e)

theorem dressedLower_local (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    LowerLocal half (dressedLower w K e) :=
  (lower_local e).mul (lowerObservable_local w K half (fun _ => 1))

/-- SAME complete original numerator, not a selected sub-action. -/
theorem original_interface_pin (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {half : Nat} (e : PlaquetteExpression half) :
    originalQuadratic w K e ≈ interfaceForm w K half (dressedLower w K e) :=
  Q'.eqv_trans _ _ _ (reflected_numerator_eq_squareValue w K e hw)
    (Q'.eqv_symm (squareExpansion w K e hw).haar_eq_squareValue)

theorem original_lower (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    interfaceFloor w K half * retainedBulkReference w K e ≤ originalQuadratic w K e :=
  Q'.le_trans' _ _ _
    (interface_form_lower w hw0 hw1 K half (dressedLower w K e)
      (dressedLower_supported w K e) (dressedLower_local w K e))
    (Q'.ge_of_eqv (original_interface_pin w hw0 K e))

theorem original_upper (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    originalQuadratic w K e ≤ retainedBulkReference w K e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (original_interface_pin w hw0 K e))
    (interface_form_upper w hw0 hw1 K half (dressedLower w K e)
      (dressedLower_supported w K e) (dressedLower_local w K e))

theorem original_null_iff (w : Q') (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    originalQuadratic w K e ≈ 0 ↔ retainedBulkReference w K e ≈ 0 := by
  have hpin := original_interface_pin w (Q'.le_of_lt hw0) K e
  have hzero := interface_form_zero_iff w hw0 hw1 K half (dressedLower w K e)
    (dressedLower_supported w K e) (dressedLower_local w K e)
  exact ⟨fun h => hzero.mp (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpin) h),
    fun h => Q'.eqv_trans _ _ _ hpin (hzero.mpr h)⟩

/-- A computed finite physical comparison, not a uniform asymptotic floor. -/
def originalComparisonCertificate (w : Q') (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    Σ' rho : Q', ((0 : Q') < rho) ×'
      (rho * retainedBulkReference w K e ≤ originalQuadratic w K e) ×'
      (originalQuadratic w K e ≤ retainedBulkReference w K e) ×'
      (rho ≈ qpow w (K*(K+2)*(centralFixedFaceIds half).length)) :=
  ⟨interfaceFloor w K half, interfaceFloor_positive w hw0 K half,
    original_lower w (Q'.le_of_lt hw0) hw1 K e,
    original_upper w (Q'.le_of_lt hw0) hw1 K e,
    interfaceFloor_exponent w K half⟩

end YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.originalQuadratic
#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.retainedBulkReference
#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.dressedLower_local
#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.original_interface_pin
#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.original_lower
#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.original_upper
#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.original_null_iff
#print axioms YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity.originalComparisonCertificate
