/-
# The actual Wilson excitation still vanishes after power renormalization

Multiply the already constructed unit excitation by a_j^(-p), using the
original rational scalar operation. Its exact squared norm is a_j^(-2p),
and its actual sampled positive-time response still vanishes with the proved
explicit modulus. Nome, carrier, action and time operator are unchanged.

This is a physical-instance obstruction to obtaining a surviving channel by
power rescaling this fixed guarded lattice theory. It does not rule out a
justified changing-coupling continuum trajectory or faster norm growth.
-/

import YMGap.Continuum.BF4WilsonPolynomialScalingObstruction
import YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws

namespace YMGap.Continuum.BF4WilsonPolynomialRenormalizedExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero (floorLatticeSteps)
open YMGap.Continuum.PhysicalSamplingPolynomialEnvelope
open YMGap.Continuum.BF4WilsonPolynomialScalingObstruction
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate_positive)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs

/-- A computed scaling of the actual nonzero unit excitation, not a new state. -/
def renormalizedExcitation (A : PhysicalSpacing) (p j : Nat) : V :=
  completedSmul nome_pos nome_lt_one hsmall hd hs ((inverseSpacing A j)^p) unitExcitation

theorem renormalizedExcitation_orthogonal (A : PhysicalSpacing) (p j : Nat) :
    B (renormalizedExcitation A p j) U = RCzero := by
  rw [renormalizedExcitation, completedInner_smul_left, unitExcitation_orthogonal]
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_zero_eqv _)

/-- Exact polynomial norm growth on the SAME carrier, with no supplied cap. -/
theorem renormalizedExcitation_norm (A : PhysicalSpacing) (p j : Nat) :
    B (renormalizedExcitation A p j) (renormalizedExcitation A p j) =
      Quotient.mk crealSetoid (ofQ' ((inverseSpacing A j)^(p+p))) := by
  rw [renormalizedExcitation, completedInner_smul_left, completedInner_smul_right,
    unitExcitation_norm]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv (((inverseSpacing A j)^p) * (((inverseSpacing A j)^p) * 1))
    ((inverseSpacing A j)^(p+p))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))
    (Q'.eqv_symm (Q'.pow_add_eqv _ p p))

/-- At any fixed positive integer physical time, every power-rescaled original
probe obeys the computed tolerance tail. No scalar response is substituted. -/
theorem renormalizedResponse_small
    (A : PhysicalSpacing) (Z : SpacingToZero A) (p t : Nat) (ht : 0 < t)
    (epsilon : Q') (he : (0 : Q') < epsilon) (j : Nat)
    (hj : polynomialPhysicalModulus Z rayleighCeiling 1 (p+p) t epsilon ≤ j) :
    RCle (B (renormalizedExcitation A p j)
      (T (2*floorLatticeSteps A j t) (renormalizedExcitation A p j)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  apply sampled_polynomial_small
    (fun _ => nome_pos) (fun _ => nome_lt_one) (fun _ => hsmall)
    (fun _ => hd) (fun _ => hs) (renormalizedExcitation A p) A Z t ht
    rayleighCeiling 1 (p+p) (Q'.le_of_lt (twoStepRate_positive nome_pos hd))
    rayleighCeiling_lt_one Q'.zero_le_one epsilon he j hj
    (renormalizedExcitation_orthogonal A p j) (Q'.le_refl' _)
  rw [renormalizedExcitation_norm]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.ge_of_eqv (Q'.one_mul_eqv _))

end YMGap.Continuum.BF4WilsonPolynomialRenormalizedExcitation

#print axioms YMGap.Continuum.BF4WilsonPolynomialRenormalizedExcitation.renormalizedExcitation
#print axioms YMGap.Continuum.BF4WilsonPolynomialRenormalizedExcitation.renormalizedExcitation_orthogonal
#print axioms YMGap.Continuum.BF4WilsonPolynomialRenormalizedExcitation.renormalizedExcitation_norm
#print axioms YMGap.Continuum.BF4WilsonPolynomialRenormalizedExcitation.renormalizedResponse_small
