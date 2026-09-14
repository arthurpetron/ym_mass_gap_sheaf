/-
# A norm-one ORIGINAL excitation with a witnessed strict Rayleigh interval

Normalize the existing thermodynamic centered probe, using its SAME norm
representative and the constructed inverse-square-root modulus. The vector
remains in the existing unit complement. Its actual two-step response lies
in [responseFloor/P,1/2], with positive lower endpoint and strict upper
endpoint. Every positive-time translate retains a computed positive floor.

This is RC-valued normalization in the existing plaquette-generated OS
completion at SU(2) nome 1/1024, fixed spacing. It does NOT inhabit the
Q'-valued CanonicalOSRoot, enlarge the observable algebra, prove full
quotient-level completeness, or construct continuous time/continuum YM.
-/

import YMGap.Continuum.PositiveCRealNormalizationScalar
import YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor

namespace YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (UnitComplement center)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap (complement_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation (state state_orthogonal)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (response responseRepresentative responseCauchy response_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse (original_response_floor)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbitFloor
  (probePresentation normCeiling normCeiling_positive initial_moment_ceiling first_moment_floor
    positiveTimeFloor positiveTimeFloor_positive positiveTimeFloor_bound)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor (responseFloor responseFloor_positive)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarMulCauchy)

def originalNorm : CReal := moment probePresentation 0

def originalNormCauchy : QCauchy originalNorm.approx := momentCauchy probePresentation 0

theorem originalNorm_pin : completedInner state.val state.val=Quotient.mk crealSetoid originalNorm :=
  moment_zero probePresentation

theorem originalNorm_floor : leEv (ofQ' responseFloor) originalNorm :=
  leEv_trans first_moment_floor (moment_le_zero probePresentation 1)

def normalizer : CReal :=
  PositiveCRealNormalizationScalar.scalar originalNorm originalNormCauchy responseFloor responseFloor_positive

def normalizerCauchy : QCauchy normalizer.approx :=
  PositiveCRealNormalizationScalar.scalarCauchy originalNorm originalNormCauchy responseFloor responseFloor_positive

/-- The actual scaled original state, not a new abstract unit vector. -/
def unitProbe : UnitComplement where
  val := completedRealSmul normalizer normalizerCauchy state.val
  property := by
    rw [completedInner_realSmul_left,state_orthogonal,RCmul_comm]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (normalizer.approx n)))

theorem unitProbe_norm : completedInner unitProbe.val unitProbe.val=Quotient.mk crealSetoid cone := by
  change completedInner (completedRealSmul normalizer normalizerCauchy state.val)
    (completedRealSmul normalizer normalizerCauchy state.val)=_
  rw [completedInner_realSmul_left,completedInner_realSmul_right,originalNorm_pin]
  exact Quotient.sound (PositiveCRealNormalizationScalar.scalar_normalizes
    originalNorm originalNormCauchy responseFloor responseFloor_positive originalNorm_floor)

theorem unitProbe_orthogonal : completedInner unitProbe.val completedUnit=RCzero := unitProbe.property

def normalizedResponse : CReal := CReal.mul normalizer (CReal.mul normalizer responseRepresentative)

def normalizedResponseCauchy : QCauchy normalizedResponse.approx :=
  scalarMulCauchy _ _ normalizerCauchy (scalarMulCauchy _ _ normalizerCauchy responseCauchy)

theorem normalizedResponse_pin :
    completedInner unitProbe.val (twoStepTransfer unitProbe.val)=Quotient.mk crealSetoid normalizedResponse := by
  change completedInner (completedRealSmul normalizer normalizerCauchy state.val)
    (completedTime 2 (completedRealSmul normalizer normalizerCauchy state.val))=_
  rw [completedTime_realSmul,completedInner_realSmul_left,completedInner_realSmul_right]
  change RCmul (Quotient.mk crealSetoid normalizer)
    (RCmul (Quotient.mk crealSetoid normalizer) response)=_
  rw [response_pin]
  rfl

def rayleighFloor : Q' := Q'.divPos responseFloor normCeiling normCeiling_positive

theorem rayleighFloor_positive : (0 : Q')<rayleighFloor := Q'.divPos_pos _ _ _ responseFloor_positive

theorem normalizedResponse_floor : leEv (ofQ' rayleighFloor) normalizedResponse :=
  PositiveCRealNormalizationScalar.normalized_weight_floor
    originalNorm originalNormCauchy responseFloor responseFloor_positive originalNorm_floor
    normCeiling responseFloor normCeiling_positive responseFloor_positive initial_moment_ceiling
    responseRepresentative original_response_floor

theorem normalizedResponse_upper : leEv normalizedResponse (ofQ' HalfPow.half) := by
  have h := (complement_twoStep_form_gap unitProbe).2
  rw [unitProbe_norm,normalizedResponse_pin] at h
  exact leEv_trans h (leEv_of_equiv (CRealAlg.cmul_cone (ofQ' HalfPow.half)))

theorem unitProbe_time_norm (n : Nat) :
    completedInner (completedTime n unitProbe.val) (completedTime n unitProbe.val)=
      Quotient.mk crealSetoid (CReal.mul normalizer (CReal.mul normalizer (moment probePresentation n))) := by
  change completedInner (completedTime n (completedRealSmul normalizer normalizerCauchy state.val))
    (completedTime n (completedRealSmul normalizer normalizerCauchy state.val))=_
  rw [completedTime_realSmul,completedInner_realSmul_left,completedInner_realSmul_right]
  change RCmul (Quotient.mk crealSetoid normalizer)
    (RCmul (Quotient.mk crealSetoid normalizer)
      (completedInner (completedTime n (center (embedPresentation probePresentation)))
        (completedTime n (center (embedPresentation probePresentation)))))=_
  rw [moment_pin]
  rfl

def orbitFloor (k : Nat) : Q' := Q'.divPos (positiveTimeFloor k) normCeiling normCeiling_positive

theorem orbitFloor_positive (k : Nat) : (0 : Q')<orbitFloor k :=
  Q'.divPos_pos _ _ _ (positiveTimeFloor_positive k)

theorem unitProbe_orbit_floor (k : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (orbitFloor k)))
      (completedInner (completedTime (k+1) unitProbe.val) (completedTime (k+1) unitProbe.val)) := by
  rw [unitProbe_time_norm]
  exact PositiveCRealNormalizationScalar.normalized_weight_floor
    originalNorm originalNormCauchy responseFloor responseFloor_positive originalNorm_floor
    normCeiling (positiveTimeFloor k) normCeiling_positive (positiveTimeFloor_positive k)
    initial_moment_ceiling (moment probePresentation (k+1)) (positiveTimeFloor_bound k)

/-- Norm-one state and actual Rayleigh interval, returned with real/modulus data. -/
def normalizedCertificate :
    Σ' v : UnitComplement, Σ' lower : Q', Σ' upper : Q', Σ' r : CReal,
      ((0 : Q')<lower) ×' (upper<(1 : Q')) ×' QCauchy r.approx ×'
      (completedInner v.val v.val=Quotient.mk crealSetoid cone) ×'
      (completedInner v.val (twoStepTransfer v.val)=Quotient.mk crealSetoid r) ×'
      leEv (ofQ' lower) r ×' leEv r (ofQ' upper) :=
  ⟨unitProbe,rayleighFloor,HalfPow.half,normalizedResponse,rayleighFloor_positive,by decide,normalizedResponseCauchy,
    unitProbe_norm,normalizedResponse_pin,normalizedResponse_floor,normalizedResponse_upper⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.originalNorm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.originalNormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.originalNorm_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.originalNorm_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizer
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.unitProbe
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.unitProbe_norm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.unitProbe_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizedResponse
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizedResponseCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizedResponse_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.rayleighFloor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.rayleighFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizedResponse_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizedResponse_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.unitProbe_time_norm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.orbitFloor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.orbitFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.unitProbe_orbit_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe.normalizedCertificate
