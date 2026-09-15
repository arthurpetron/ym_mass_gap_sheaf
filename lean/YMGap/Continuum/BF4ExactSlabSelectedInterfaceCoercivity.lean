/-
# Crossing-cutoff-independent floor for each FIXED original bulk insertion

The all-extent exposed-link selection theorem computes a finite cutoff N
from the original bulk-dressed insertion. Above N, the original crossing
pairing is exactly constant, at every crossing nome. The mixed-cutoff pin
transfers this fact to the SAME spatial Gram form. Its positive comparison
factor is therefore v^(N*(N+2)*F), independent of all later crossing cutoffs.

The cutoff N still depends on the fixed bulk cutoff, the original observable
and extent; the floor still depends on v. Neither growing bulk cutoffs nor
thermodynamic/continuum limits are controlled here. No completed transfer
inverse, zero kernel, full-space time-zero continuity or Clay claim.
-/

import YMGap.Continuum.BF4ExactSlabMixedInterfacePin

namespace YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabMixedInterfacePin
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

/-- Computed from the ORIGINAL insertion, before temporal gauge change. -/
def selectedCutoff (b : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) : Nat :=
  interfaceBound half (mixedInsertion b B e)

theorem mixed_stable (b v : Q') (B K : Nat) {half : Nat} (e : PlaquetteExpression half)
    (hK : selectedCutoff b B e ≤ K) :
    mixedQuadratic b v B K e ≈ mixedQuadratic b v B (selectedCutoff b B e) e :=
  interfacePairing_stable v K half (mixedInsertion b B e) (mixedInsertion_supported b B e) hK

/-- Selection is applied only after pinning both cutoffs to the original pairing. -/
theorem gram_stable (b v : Q') (hv : (0 : Q') ≤ v) (B K : Nat)
    {half : Nat} (e : PlaquetteExpression half) (hK : selectedCutoff b B e ≤ K) :
    interfaceForm v K half (dressedLower b B e) ≈
      interfaceForm v (selectedCutoff b B e) half (dressedLower b B e) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (mixed_interface_pin b v B K e hv))
    (Q'.eqv_trans _ _ _ (mixed_stable b v B K e hK)
      (mixed_interface_pin b v B (selectedCutoff b B e) e hv))

/-- Finite nome-one crossing reference, with original b,B bulk dressing retained. -/
def selectedReference (b : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  mixedQuadratic b 1 B (selectedCutoff b B e) e

def selectedFloor (b v : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  interfaceFloor v (selectedCutoff b B e) half

theorem selectedFloor_positive (b v : Q') (hv : (0 : Q') < v) (B : Nat)
    {half : Nat} (e : PlaquetteExpression half) : (0 : Q') < selectedFloor b v B e :=
  interfaceFloor_positive v hv (selectedCutoff b B e) half

theorem selectedFloor_exponent (b v : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) :
    selectedFloor b v B e ≈
      qpow v (selectedCutoff b B e * (selectedCutoff b B e + 2) * (centralFixedFaceIds half).length) :=
  interfaceFloor_exponent v (selectedCutoff b B e) half

/-- The factor and reference do not depend on the later crossing cutoff K. -/
theorem selected_lower (b v : Q') (hv0 : (0 : Q') ≤ v) (hv1 : v ≤ (1 : Q'))
    (B K : Nat) {half : Nat} (e : PlaquetteExpression half) (hK : selectedCutoff b B e ≤ K) :
    selectedFloor b v B e * selectedReference b B e ≤ mixedQuadratic b v B K e := by
  have hfinite := interface_form_lower v hv0 hv1 (selectedCutoff b B e) half (dressedLower b B e)
    (dressedLower_supported b B e) (dressedLower_local b B e)
  have hleft := Q'.mul_eqv_congr_left (selectedFloor b v B e) _ _
    (mixed_interface_pin b 1 B (selectedCutoff b B e) e (by decide))
  have hright := Q'.eqv_trans _ _ _ (mixed_stable b v B K e hK)
    (mixed_interface_pin b v B (selectedCutoff b B e) e hv0)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hfinite (Q'.ge_of_eqv hright))

theorem selected_upper (b v : Q') (hv0 : (0 : Q') ≤ v) (hv1 : v ≤ (1 : Q'))
    (B K : Nat) {half : Nat} (e : PlaquetteExpression half) (hK : selectedCutoff b B e ≤ K) :
    mixedQuadratic b v B K e ≤ selectedReference b B e := by
  have hfinite := interface_form_upper v hv0 hv1 (selectedCutoff b B e) half (dressedLower b B e)
    (dressedLower_supported b B e) (dressedLower_local b B e)
  have hleft := Q'.eqv_trans _ _ _ (mixed_stable b v B K e hK)
    (mixed_interface_pin b v B (selectedCutoff b B e) e hv0)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hfinite
      (Q'.ge_of_eqv (mixed_interface_pin b 1 B (selectedCutoff b B e) e (by decide))))

theorem selected_null_iff (b v : Q') (hv0 : (0 : Q') < v) (hv1 : v ≤ (1 : Q'))
    (B K : Nat) {half : Nat} (e : PlaquetteExpression half) (hK : selectedCutoff b B e ≤ K) :
    mixedQuadratic b v B K e ≈ 0 ↔ selectedReference b B e ≈ 0 := by
  have hleft := Q'.eqv_trans _ _ _ (mixed_stable b v B K e hK)
    (mixed_interface_pin b v B (selectedCutoff b B e) e (Q'.le_of_lt hv0))
  have hright := mixed_interface_pin b 1 B (selectedCutoff b B e) e (by decide)
  have hz := interface_form_zero_iff v hv0 hv1 (selectedCutoff b B e) half (dressedLower b B e)
    (dressedLower_supported b B e) (dressedLower_local b B e)
  exact ⟨fun h => Q'.eqv_trans _ _ _ hright
      (hz.mp (Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft) h)),
    fun h => Q'.eqv_trans _ _ _ hleft
      (hz.mpr (Q'.eqv_trans _ _ _ (Q'.eqv_symm hright) h))⟩

/-- The existing exact original-interface limit, not a different completion. -/
def mixedCutoffLimit (b v : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) : CReal :=
  interfacePairingLimit v half (mixedInsertion b B e)

theorem mixedCutoffLimit_exact (b v : Q') (B K : Nat) {half : Nat} (e : PlaquetteExpression half)
    (hK : selectedCutoff b B e ≤ K) (precision : Nat) :
    mixedQuadratic b v B K e ≈ (mixedCutoffLimit b v B e).approx precision :=
  interfacePairingLimit_exact v K half (mixedInsertion b B e) (mixedInsertion_supported b B e) hK precision

/-- One computed cutoff and strictly positive factor certify EVERY later crossing cutoff.
The fixed bulk cutoff B, observable, extent and crossing nome remain parameters. -/
def selectedComparisonCertificate (b v : Q') (hv0 : (0 : Q') < v) (hv1 : v ≤ (1 : Q'))
    (B : Nat) {half : Nat} (e : PlaquetteExpression half) :
    Σ' N : Nat, Σ' rho : Q', ((0 : Q') < rho) ×'
      (N = selectedCutoff b B e) ×'
      (rho ≈ qpow v (N*(N+2)*(centralFixedFaceIds half).length)) ×'
      (∀ K, N ≤ K →
        (rho * selectedReference b B e ≤ mixedQuadratic b v B K e) ∧
        (mixedQuadratic b v B K e ≤ selectedReference b B e)) :=
  ⟨selectedCutoff b B e, selectedFloor b v B e,
    selectedFloor_positive b v hv0 B e, rfl, selectedFloor_exponent b v B e,
    fun K hK => ⟨selected_lower b v (Q'.le_of_lt hv0) hv1 B K e hK,
      selected_upper b v (Q'.le_of_lt hv0) hv1 B K e hK⟩⟩

end YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selectedCutoff
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.mixed_stable
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.gram_stable
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selectedReference
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selectedFloor
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selectedFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selectedFloor_exponent
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selected_lower
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selected_upper
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selected_null_iff
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.mixedCutoffLimit
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.mixedCutoffLimit_exact
#print axioms YMGap.Continuum.BF4ExactSlabSelectedInterfaceCoercivity.selectedComparisonCertificate
