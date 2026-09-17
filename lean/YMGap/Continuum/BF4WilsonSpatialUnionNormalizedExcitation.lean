/-
# Norm-one positive response of the EXISTING Wilson excitation

The proved scalar pin supplies the actual norm and two-step response of
SmallNomeGap.vector, with their existing explicit Cauchy data. Its positive
norm floor constructs an inverse square root, and the SAME Wilson real
action scales that vector to norm one. The original norm ceiling converts
the positive response floor into a positive rational Rayleigh lower bound.
The universal Wilson strict form bound supplies the upper endpoint below one.

All guards are discharged at nome 1/1024. The output retains this carrier,
its actual time map, orthogonality, and the response modulus as data. It is
a fixed-spacing SU(2) result, not a canonical Q'-valued GNS instance, full
Hilbert/OS/QFT reconstruction, physical mass calibration or Clay closure.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionRealScalarAlgebra
import YMGap.Continuum.BF4WilsonSpatialUnionPositiveResponse
import YMGap.Continuum.PositiveCRealNormalizationScalar

namespace YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar
open YMGap.Continuum.BF4WilsonSpatialUnionRealScalarAlgebra
open YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap
  (vector vector_orthogonal vector_norm_floor)
open YMGap.Continuum.BF4WilsonSpatialUnionPositiveResponse
  (vector_spatial_correlator_pin lagTwo_floor)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
  (spatialCenteredMoment spatialCenteredMomentCauchy)
open YMGap.Continuum.BF4SpatialUnionResponseProbePins (centralProbe)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (positivePrefactor positivePrefactor_pos spatialCenteredMoment_le_geometric
    twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor
  (responseFloor responseFloor_positive)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarMulCauchy)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "S" => completedRealSmul nome_pos nome_lt_one hsmall hd hs

/-- An original scalar representative, pinned below to THIS Wilson norm. -/
def originalNorm : CReal :=
  spatialCenteredMoment nome_pos nome_lt_one 1 hsmall hd hs (by decide)
    0 centralProbe centralProbe

def originalNormCauchy : QCauchy originalNorm.approx :=
  spatialCenteredMomentCauchy nome_pos nome_lt_one 1 hsmall hd hs (by decide)
    0 centralProbe centralProbe

theorem originalNorm_pin : B vector vector = Quotient.mk crealSetoid originalNorm := by
  have h := vector_spatial_correlator_pin 0
  rw [completedTime_zero] at h
  exact h

theorem originalNorm_floor : leEv (ofQ' (starRatio nome)) originalNorm := by
  have h := vector_norm_floor
  rw [originalNorm_pin] at h
  exact h

/-- Computed bound for this exact original norm, not a bound on a surrogate. -/
def normCeiling : Q' := positivePrefactor nome_pos 1 hd hs 0 centralProbe centralProbe

theorem normCeiling_positive : (0 : Q') < normCeiling :=
  positivePrefactor_pos nome_pos 1 hd hs 0 centralProbe centralProbe (by decide) (by decide)

theorem originalNorm_ceiling : leEv originalNorm (ofQ' normCeiling) :=
  leEv_trans
    (spatialCenteredMoment_le_geometric nome_pos nome_lt_one 1 hsmall hd hs (by decide)
      0 0 centralProbe centralProbe (by decide) (by decide))
    (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.mul_one_eqv normCeiling)))

/-- Clamped Heron/inverse-root construction using the proved positive floor. -/
def normalizer : CReal :=
  PositiveCRealNormalizationScalar.scalar originalNorm originalNormCauchy
    (starRatio nome) (starRatio_positive nome_pos nome_lt_one)

def normalizerCauchy : QCauchy normalizer.approx :=
  PositiveCRealNormalizationScalar.scalarCauchy originalNorm originalNormCauchy
    (starRatio nome) (starRatio_positive nome_pos nome_lt_one)

/-- The existing vector, scaled by its actual inverse norm on the SAME carrier. -/
def unitExcitation : V := S normalizer normalizerCauchy vector

theorem unitExcitation_orthogonal : B unitExcitation U = RCzero :=
  completedRealSmul_orthogonal nome_pos nome_lt_one hsmall hd hs
    normalizer normalizerCauchy vector U vector_orthogonal

theorem unitExcitation_norm : B unitExcitation unitExcitation = Quotient.mk crealSetoid cone := by
  change B (S normalizer normalizerCauchy vector) (S normalizer normalizerCauchy vector) = _
  rw [completedInner_realSmul_left, completedInner_realSmul_right, originalNorm_pin]
  exact Quotient.sound (PositiveCRealNormalizationScalar.scalar_normalizes
    originalNorm originalNormCauchy (starRatio nome)
    (starRatio_positive nome_pos nome_lt_one) originalNorm_floor)

/-- The scalar pin retains the original time map at physical lag TWO. -/
def responseRepresentative : CReal :=
  spatialCenteredMoment nome_pos nome_lt_one 1 hsmall hd hs (by decide)
    2 centralProbe centralProbe

def responseCauchy : QCauchy responseRepresentative.approx :=
  spatialCenteredMomentCauchy nome_pos nome_lt_one 1 hsmall hd hs (by decide)
    2 centralProbe centralProbe

theorem response_floor : leEv (ofQ' responseFloor) responseRepresentative := by
  have h := lagTwo_floor
  rw [vector_spatial_correlator_pin] at h
  exact h

def normalizedResponse : CReal := mul normalizer (mul normalizer responseRepresentative)

def normalizedResponseCauchy : QCauchy normalizedResponse.approx :=
  scalarMulCauchy _ _ normalizerCauchy (scalarMulCauchy _ _ normalizerCauchy responseCauchy)

/-- Exact pairing of the normalized vector with its SAME completed two-step map. -/
theorem normalizedResponse_pin :
    B unitExcitation (T 2 unitExcitation) = Quotient.mk crealSetoid normalizedResponse := by
  change B (S normalizer normalizerCauchy vector) (T 2 (S normalizer normalizerCauchy vector)) = _
  rw [completedTime_realSmul, completedInner_realSmul_left, completedInner_realSmul_right,
    vector_spatial_correlator_pin]
  rfl

def rayleighFloor : Q' := Q'.divPos responseFloor normCeiling normCeiling_positive

theorem rayleighFloor_positive : (0 : Q') < rayleighFloor :=
  Q'.divPos_pos _ _ _ responseFloor_positive

def rayleighCeiling : Q' := twoStepRate nome hd

theorem rayleighCeiling_lt_one : rayleighCeiling < (1 : Q') :=
  twoStepRate_lt_one nome_pos hd hs

theorem normalizedResponse_floor : leEv (ofQ' rayleighFloor) normalizedResponse :=
  PositiveCRealNormalizationScalar.normalized_weight_floor originalNorm originalNormCauchy
    (starRatio nome) (starRatio_positive nome_pos nome_lt_one) originalNorm_floor
    normCeiling responseFloor normCeiling_positive responseFloor_positive originalNorm_ceiling
    responseRepresentative response_floor

theorem normalizedResponse_ceiling : leEv normalizedResponse (ofQ' rayleighCeiling) := by
  have h := completed_twoStep_form_gap nome_pos nome_lt_one hsmall hd hs
    unitExcitation unitExcitation_orthogonal
  rw [unitExcitation_norm, normalizedResponse_pin] at h
  exact leEv_trans h (leEv_of_equiv (CRealAlg.cmul_cone (ofQ' rayleighCeiling)))

/-- Actual witness, orthogonality, norm one, time pin, scalar modulus and
strict positive rational interval, with no unsupplied analytic hypothesis. -/
def normalizedCertificate :
    Σ' x : V, Σ' lower : Q', Σ' upper : Q', Σ' r : CReal,
      ((0 : Q') < lower) ×' (upper < (1 : Q')) ×' QCauchy r.approx ×'
      (B x U = RCzero) ×' (B x x = Quotient.mk crealSetoid cone) ×'
      (B x (T 2 x) = Quotient.mk crealSetoid r) ×'
      leEv (ofQ' lower) r ×' leEv r (ofQ' upper) :=
  ⟨unitExcitation, rayleighFloor, rayleighCeiling, normalizedResponse,
    rayleighFloor_positive, rayleighCeiling_lt_one, normalizedResponseCauchy,
    unitExcitation_orthogonal, unitExcitation_norm, normalizedResponse_pin,
    normalizedResponse_floor, normalizedResponse_ceiling⟩

#print axioms originalNorm
#print axioms originalNormCauchy
#print axioms originalNorm_pin
#print axioms originalNorm_floor
#print axioms normCeiling
#print axioms normCeiling_positive
#print axioms originalNorm_ceiling
#print axioms normalizer
#print axioms normalizerCauchy
#print axioms unitExcitation
#print axioms unitExcitation_orthogonal
#print axioms unitExcitation_norm
#print axioms responseRepresentative
#print axioms responseCauchy
#print axioms response_floor
#print axioms normalizedResponse
#print axioms normalizedResponseCauchy
#print axioms normalizedResponse_pin
#print axioms rayleighFloor
#print axioms rayleighFloor_positive
#print axioms rayleighCeiling
#print axioms rayleighCeiling_lt_one
#print axioms normalizedResponse_floor
#print axioms normalizedResponse_ceiling
#print axioms normalizedCertificate

end YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
