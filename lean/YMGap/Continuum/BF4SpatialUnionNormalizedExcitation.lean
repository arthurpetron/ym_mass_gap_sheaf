/-
# A norm-one excitation and positive strict Rayleigh interval on the SAME union

Scale the existing centered original plaquette vector by the constructed
inverse square root of its ACTUAL union norm. Its supplied QCauchy data
and the proved positive local-star floor determine the scalar and modulus.
The existing spatial geometric prefactor gives a computed rational norm
ceiling, without evaluating a large Cauchy sample or changing the carrier.

The recently proved positive original two-step response and the universal
union strict form bound give a rational interval [responseFloor/P,q],
with positive lower endpoint and q<1, for this actual unit vector.
All guards are discharged at the existing SU(2) nome 1/1024.

This is an RC-valued result on the existing discrete-time spatial union.
It does not inhabit the Q'-valued canonical OS/GNS interfaces, assert full
observable coverage, calibrate a physical continuum mass, or prove Clay.
-/

import YMGap.Continuum.BF4SpatialUnionRealScalarAlgebra
import YMGap.Continuum.BF4SpatialUnionPositiveResponse
import YMGap.Continuum.PositiveCRealNormalizationScalar

namespace YMGap.Continuum.BF4SpatialUnionNormalizedExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4SpatialUnionCompletedRealScalar
open YMGap.Continuum.BF4SpatialUnionRealScalarAlgebra
open YMGap.Continuum.BF4SpatialUnionUnitComplement (UnitComplement)
open YMGap.Continuum.BF4SpatialUnionCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4SpatialUnionCenteredForm
  (centeredMoment centeredMomentCauchy centeredMoment_diagonal_pin)
open YMGap.Continuum.BF4SpatialUnionExcitation
  (centralStage excitation excitation_orthogonal excitationNorm excitationNormCauchy
    excitation_norm_pin excitation_norm_floor excitation_correlator_pin)
open YMGap.Continuum.BF4SpatialUnionPositiveResponse (lagTwo_floor)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (positivePrefactor positivePrefactor_pos spatialCenteredMoment_le_geometric
    twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor (responseFloor responseFloor_positive)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarMulCauchy)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "v" => excitation nome_pos nome_lt_one hsmall hd hs
local notation "N" => excitationNorm nome_pos nome_lt_one hsmall hd hs
local notation "cN" => excitationNormCauchy nome_pos nome_lt_one hsmall hd hs
local notation "S" => completedRealSmul nome_pos nome_lt_one hsmall hd hs

/-- A computed upper budget for the same original centered norm. -/
def normCeiling : Q' :=
  positivePrefactor nome_pos 1 hd hs 0 centralStage.value centralStage.value

theorem normCeiling_positive : (0 : Q') < normCeiling :=
  positivePrefactor_pos nome_pos 1 hd hs 0 centralStage.value centralStage.value
    (by decide) (by decide)

theorem originalNorm_floor : leEv (ofQ' (starRatio nome)) N := by
  have h := excitation_norm_floor nome_pos nome_lt_one hsmall hd hs
  rw [excitation_norm_pin] at h
  exact h

/-- The prefactor bound is applied to this exact base-one observable at
lag zero, then pinned to the existing union norm representative. -/
theorem originalNorm_ceiling : leEv N (ofQ' normCeiling) :=
  leEv_trans
    (leEv_of_equiv (centeredMoment_diagonal_pin nome_pos nome_lt_one hsmall hd hs 0 centralStage))
    (leEv_trans
      (spatialCenteredMoment_le_geometric nome_pos nome_lt_one 1 hsmall hd hs (by decide)
        0 0 centralStage.value centralStage.value (by decide) (by decide))
      (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv
        (fun _ => Q'.mul_one_eqv normCeiling))))

/-- Explicit clamped Heron/inverse-root construction, retaining its QCauchy data. -/
def normalizer : CReal :=
  PositiveCRealNormalizationScalar.scalar N cN (starRatio nome) (starRatio_positive nome_pos nome_lt_one)

def normalizerCauchy : QCauchy normalizer.approx :=
  PositiveCRealNormalizationScalar.scalarCauchy N cN
    (starRatio nome) (starRatio_positive nome_pos nome_lt_one)

/-- The actual scaled excitation belongs to the existing unit complement. -/
def unitExcitation : UnitComplement nome_pos nome_lt_one hsmall hd hs where
  val := S normalizer normalizerCauchy v
  property := by
    rw [completedInner_realSmul_left, excitation_orthogonal]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.mul_zero_eqv (normalizer.approx n)))

theorem unitExcitation_orthogonal : B unitExcitation.val U = RCzero := unitExcitation.property

theorem unitExcitation_norm : B unitExcitation.val unitExcitation.val = Quotient.mk crealSetoid cone := by
  change B (S normalizer normalizerCauchy v) (S normalizer normalizerCauchy v) = _
  rw [completedInner_realSmul_left, completedInner_realSmul_right, excitation_norm_pin]
  exact Quotient.sound (PositiveCRealNormalizationScalar.scalar_normalizes N cN
    (starRatio nome) (starRatio_positive nome_pos nome_lt_one) originalNorm_floor)

/-- The actual unscaled two-step response already pinned to the union pairing. -/
def responseRepresentative : CReal := centeredMoment nome_pos nome_lt_one hsmall hd hs
  2 centralStage centralStage

def responseCauchy : QCauchy responseRepresentative.approx :=
  centeredMomentCauchy nome_pos nome_lt_one hsmall hd hs 2 centralStage centralStage

theorem response_floor : leEv (ofQ' responseFloor) responseRepresentative := by
  have h := lagTwo_floor
  rw [excitation_correlator_pin] at h
  exact h

def normalizedResponse : CReal := CReal.mul normalizer (CReal.mul normalizer responseRepresentative)

def normalizedResponseCauchy : QCauchy normalizedResponse.approx :=
  scalarMulCauchy _ _ normalizerCauchy (scalarMulCauchy _ _ normalizerCauchy responseCauchy)

/-- The Rayleigh scalar is the pairing with the SAME actual two-step time map. -/
theorem normalizedResponse_pin :
    B unitExcitation.val (T 2 unitExcitation.val) = Quotient.mk crealSetoid normalizedResponse := by
  change B (S normalizer normalizerCauchy v) (T 2 (S normalizer normalizerCauchy v)) = _
  rw [completedTime_realSmul, completedInner_realSmul_left, completedInner_realSmul_right,
    excitation_correlator_pin]
  rfl

def rayleighFloor : Q' := Q'.divPos responseFloor normCeiling normCeiling_positive

theorem rayleighFloor_positive : (0 : Q') < rayleighFloor :=
  Q'.divPos_pos _ _ _ responseFloor_positive

def rayleighCeiling : Q' := twoStepRate nome hd

theorem rayleighCeiling_lt_one : rayleighCeiling < (1 : Q') :=
  twoStepRate_lt_one nome_pos hd hs

theorem normalizedResponse_floor : leEv (ofQ' rayleighFloor) normalizedResponse :=
  PositiveCRealNormalizationScalar.normalized_weight_floor N cN
    (starRatio nome) (starRatio_positive nome_pos nome_lt_one) originalNorm_floor
    normCeiling responseFloor normCeiling_positive responseFloor_positive originalNorm_ceiling
    responseRepresentative response_floor

theorem normalizedResponse_ceiling : leEv normalizedResponse (ofQ' rayleighCeiling) := by
  have h := completed_twoStep_form_gap nome_pos nome_lt_one hsmall hd hs
    unitExcitation.val unitExcitation_orthogonal
  rw [unitExcitation_norm, normalizedResponse_pin] at h
  exact leEv_trans h (leEv_of_equiv (CRealAlg.cmul_cone (ofQ' rayleighCeiling)))

/-- Returned witness, exact norm, actual operator pin, explicit scalar modulus
and strict positive rational Rayleigh interval on the existing union carrier. -/
def normalizedCertificate :
    Σ' x : UnitComplement nome_pos nome_lt_one hsmall hd hs,
    Σ' lower : Q', Σ' upper : Q', Σ' r : CReal,
      ((0 : Q') < lower) ×' (upper < (1 : Q')) ×' QCauchy r.approx ×'
      (B x.val x.val = Quotient.mk crealSetoid cone) ×'
      (B x.val (T 2 x.val) = Quotient.mk crealSetoid r) ×'
      leEv (ofQ' lower) r ×' leEv r (ofQ' upper) :=
  ⟨unitExcitation, rayleighFloor, rayleighCeiling, normalizedResponse,
    rayleighFloor_positive, rayleighCeiling_lt_one, normalizedResponseCauchy,
    unitExcitation_norm, normalizedResponse_pin, normalizedResponse_floor, normalizedResponse_ceiling⟩

end YMGap.Continuum.BF4SpatialUnionNormalizedExcitation

#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normCeiling
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normCeiling_positive
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.originalNorm_floor
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.originalNorm_ceiling
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizer
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizerCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.unitExcitation
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.unitExcitation_orthogonal
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.unitExcitation_norm
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.responseRepresentative
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.responseCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.response_floor
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizedResponse
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizedResponseCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizedResponse_pin
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.rayleighFloor
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.rayleighFloor_positive
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.rayleighCeiling
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.rayleighCeiling_lt_one
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizedResponse_floor
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizedResponse_ceiling
#print axioms YMGap.Continuum.BF4SpatialUnionNormalizedExcitation.normalizedCertificate
