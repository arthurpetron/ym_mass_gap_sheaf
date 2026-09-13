/-
# Kernel certificate for a positive original-action nome and insertion budget

The exact-rational pilot is
`computations/original_plaquette_small_nome_minor.py`. This module checks
the actual unreduced Lean face/probe/channel polynomials independently.
No evaluated pilot value is admitted as an axiom or native oracle.

At w=1/1024 every original lower-face guard holds and the shared-link
product error budget is at most 1/65536. The actual polynomial coefficient
norms and channel-weight bound are also checked. This module alone does
not prove an interacting determinant sign or a completed spectral claim.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def nome : Q' := Q'.invSucc 1023

def errorCeiling : Q' := Q'.invSucc 65535

theorem nome_pos : (0 : Q') < nome := by decide

theorem nome_lt_one : nome < (1 : Q') := by decide

theorem lower_guards : ∀ id, id ∈ centralLowerFaceIds 0 →
    firstRatio nome (faceScalar 1 id) ≤ HalfPow.half := by
  have h : (centralLowerFaceIds 0).all
      (fun id => decide (firstRatio nome (faceScalar 1 id) ≤ HalfPow.half)) = true := by decide +kernel
  intro id hi
  exact of_decide_eq_true (List.all_eq_true.mp h id hi)

theorem lowerBudget_small : lowerBudget nome ≤ errorCeiling := by decide +kernel

theorem probe_coefficientL1 : polynomialCoefficientL1 (lower probe) ≤ (128 : Q') := by decide +kernel

theorem mixed_coefficientL1 : polynomialCoefficientL1 (polyMul (lower probe) scalarPolynomial) ≤ (128 : Q') := by decide +kernel

theorem unit_coefficientL1 : polynomialCoefficientL1 polyOne ≤ (1 : Q') := by decide

theorem scalar_coefficientL1 : polynomialCoefficientL1 scalarPolynomial ≤ (1 : Q') := by decide +kernel

theorem channelWeight_le_one : channelWeightPower nome 4 ≤ (1 : Q') := by decide

end YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.nome
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.errorCeiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.lower_guards
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.lowerBudget_small
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.probe_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.mixed_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.unit_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.scalar_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.channelWeight_le_one
