/-
# The exact ORIGINAL excited two-step response and its finite-volume target

For the already-constructed centered plaquette excitation x, <x,T_2 x>
is exactly ||T_1 x||^2. Its representative is the original thermodynamic
covariance of the ONE-SLICE OUTWARD translated plaquette with itself.
Both the finite-volume covariance and its rational representative modulus
are exposed, without replacing the action, reciprocal, or observable.

The previous positive floor for ||x||^2 is NOT a floor for this response.
This file proves the target pins, nonnegativity, upper bound and exact
zero-response criterion, but does NOT assert strict positive response.
SU(2), nome 1/1024 and spacing are fixed; the full observable realization,
continuous-time and continuum/Clay requirements remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (probe)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding (bulkAtTime)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
open YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation (state)

local notation "B" => completedInner

/-- The probe moves away from the reflection plane, not merely into a larger box. -/
def shiftedProbe : PlaquetteExpression 1 := bulkAtTime 1 ⟨1, by decide⟩ probe

def translatedState : UnitComplement := complementTime 1 state

theorem translatedState_pin : translatedState.val =
    center (embedPresentation ⟨1,shiftedProbe⟩) := by
  have h := complementTime_centeredState 1 ⟨0,probe⟩
  exact congrArg Subtype.val h

def response : RC := B state.val (twoStepTransfer state.val)

theorem response_norm_pin : response = B translatedState.val translatedState.val :=
  (completedTime_moments 1 1 state.val state.val).symm

def responseRepresentative : CReal := covarianceLimit shiftedProbe shiftedProbe

def responseCauchy : QCauchy responseRepresentative.approx :=
  covarianceLimitCauchy shiftedProbe shiftedProbe

theorem response_pin : response = Quotient.mk crealSetoid responseRepresentative := by
  rw [response_norm_pin, translatedState_pin]
  exact centered_inner_sameBase shiftedProbe shiftedProbe

def finiteResponse (margin : Nat) : CReal := covarianceSequence shiftedProbe shiftedProbe margin

def finiteResponseCauchy (margin : Nat) : QCauchy (finiteResponse margin).approx :=
  BF4ExactSlabPlaquetteConnectedCovariance.connectedCovarianceCauchy nome nome_pos nome_lt_one
    (enlarge margin shiftedProbe) (enlarge margin shiftedProbe)

def volumeModulus : Q' → Nat := covarianceVolumeModulus shiftedProbe shiftedProbe

/-- This is an index into the original nested rational approximants, not a
claim that all numerator and partition cutoffs are the same integer. -/
def representativeModulus (margin : Nat) : Q' → Nat := (finiteResponseCauchy margin).M

theorem response_volume_error (epsilon : Q') (he : (0 : Q') < epsilon)
    (margin : Nat) (hm : volumeModulus epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub responseRepresentative (finiteResponse margin))) (ofQ' epsilon) :=
  covariance_error_le shiftedProbe shiftedProbe epsilon he margin hm

theorem response_nonnegative : leEv czero responseRepresentative :=
  covariance_nonnegative shiftedProbe

theorem response_upper : RCle response (RCscale HalfPow.half (B state.val state.val)) :=
  (complement_twoStep_form_gap state).2

/-- The unresolved issue is precisely whether geometric time kills the probe. -/
theorem response_zero_iff : response = RCzero ↔ translatedState.val = completedZero := by
  rw [response_norm_pin]
  exact completedInner_posdef translatedState.val

theorem response_zero_iff_twoStep_zero : response = RCzero ↔
    twoStepTransfer state.val = completedZero := by
  constructor
  · intro h
    have hz := response_zero_iff.mp h
    have ht := congrArg (completedTime 1) hz
    change completedTime 1 (completedTime 1 state.val) = completedTime 1 completedZero at ht
    rw [completedTime_comp, completedTime_zeroState] at ht
    exact ht
  · intro h
    change B state.val (twoStepTransfer state.val) = RCzero
    rw [h, completedInner_zero_right]

end YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.shiftedProbe
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.translatedState
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.translatedState_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response_norm_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.responseRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.responseCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.finiteResponse
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.finiteResponseCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.volumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.representativeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response_volume_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse.response_zero_iff_twoStep_zero
