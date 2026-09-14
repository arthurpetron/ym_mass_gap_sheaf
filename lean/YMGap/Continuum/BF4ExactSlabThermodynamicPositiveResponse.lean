/-
# The ORIGINAL thermodynamic excited response is strictly positive

The proved complete original numerator floor survives representation-cutoff
removal, exact SAME-partition cancellation and the existing thermodynamic
covariance limit. For the existing centered probe x and existing two-step
operator T2, <x,T2 x> >= (1/16)*w^36 > 0, at SU(2) nome w=1/1024.

This inhabits the existing response-certificate format with computed
tolerance, margin and representative index. Acceptance is proved from the
original analytic floor, not asserted from a numerical sample or a
replacement model. No exhaustive evaluation of that large sample is needed.
The original one-step translate and T2 x are both nonzero. Full observable
realization, continuous-time spectral identification, continuum scaling,
other groups and the Clay theorem remain open.
-/

import YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor
import YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport
import YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor
open YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay (reflected_covariance_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation (state)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

theorem finite_response_floor (margin : Nat) : leEv (ofQ' responseFloor) (finiteResponse margin) := by
  let e := enlarge margin shiftedProbe
  have h := covariance_floor nome nome_pos nome_lt_one (1+margin)
    (lower e) (upper e) responseFloor 1 (fun K hK => original_numerator_floor K margin hK)
  have he := (covariance_swap nome nome_pos nome_lt_one (1+margin) (lower e) (upper e)).trans
    (reflected_covariance_pin nome nome_pos nome_lt_one e e).symm
  exact leEv_trans h (leEv_of_equiv he)

theorem original_response_floor : leEv (ofQ' responseFloor) responseRepresentative :=
  leEv_of_convergesTo_le (convergesTo_const _) (covariance_converges shiftedProbe shiftedProbe)
    finite_response_floor

theorem original_operator_floor : RCle (Quotient.mk crealSetoid (ofQ' responseFloor)) response := by
  rw [response_pin]
  exact original_response_floor

theorem translated_norm_floor : RCle (Quotient.mk crealSetoid (ofQ' responseFloor))
    (completedInner translatedState.val translatedState.val) := by
  rw [← response_norm_pin]
  exact original_operator_floor

/-- The EXISTING finite certificate is now concretely inhabited, with its
computed moduli and an independently kernel-checked acceptance proof. -/
def responseCertificate : Certificate :=
  certificateOfFloor responseFloor responseFloor_positive original_response_floor

theorem responseCertificate_accepted :
    check responseCertificate.tolerance responseCertificate.margin responseCertificate.index responseCertificate.floor=true :=
  responseCertificate.accepted

theorem responseCertificate_floor : responseCertificate.floor=HalfPow.half*responseFloor :=
  certificateOfFloor_floor responseFloor responseFloor_positive original_response_floor

def original_positive_response :
    Σ' rho : Q', ((0 : Q') < rho) ×' leEv (ofQ' rho) responseRepresentative :=
  ⟨responseFloor,responseFloor_positive,original_response_floor⟩

theorem original_response_ne_zero : response ≠ RCzero := responseCertificate.response_ne_zero

theorem original_translatedState_ne_zero : translatedState.val ≠ completedZero :=
  responseCertificate.translatedState_ne_zero

theorem original_twoStep_ne_zero : twoStepTransfer state.val ≠ completedZero :=
  responseCertificate.twoStep_ne_zero

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.finite_response_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.original_response_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.original_operator_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.translated_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.responseCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.responseCertificate_accepted
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.responseCertificate_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.original_positive_response
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.original_response_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.original_translatedState_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse.original_twoStep_ne_zero
