/-
# Time-separation decay of the ORIGINAL completed OS operator moments

Two separate, fixed-size probe boxes realize the reflected and lower
translated expressions. Their root distance is exactly s+t, independently
of the common padding and receding boundary margin. The normalized original
covariance estimate therefore passes through the ALREADY constructed
thermodynamic covariance limit and its exact completed-time operator pin.

The rate is the proved small-nome rate at nome 1/1024; the amplitude retains
the original observable bounds and base size, not the time separation.
This is decay of the actual operator moments, not boundary-error decay.
Removing the observable prefactor to obtain a strict uniform form gap,
nonzero excitations and continuum scaling are subsequent obligations.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay
import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding (bulkAtTime)
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm (form form_reflected)
open YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (center)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion (embedPresentation)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression (embed)
open YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry
open YMGap.Continuum.BF4ExactSlabTwoProbeCovariance (covariance)
open YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.SepLatticeZ4Linf (natDist)

private theorem deltaGuard : QuaternionHaarCharacterInterval.heatRemainderBound nome < 1 :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
private theorem countGuard : entropyRate 625 (adjustedCoreRate nome deltaGuard) < 1 :=
  BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
local notation "hd" => deltaGuard
local notation "hs" => countGuard

/-- This is an identity of the original normalized finite-slab covariances. -/
theorem reflected_covariance_pin (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (e f : PlaquetteExpression half) :
    Equiv (connectedCovariance w hw0 hw1 e f) (covariance w hw0 hw1 half (upper e) (lower f)) := by
  have hu : Equiv (expectation w hw0 hw1 half (upper e)) (mean w hw0 hw1 e) :=
    (expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.mul_one (upper e)).symm).trans
      (form_unit_right_mean w hw0 hw1 e)
  exact (CReal.sub_congr_left (form_reflected w hw0 hw1 e f).symm).trans
    (CReal.sub_congr_right (Pivot2.mul_congr_left hu.symm))

def timeBudget {base : Nat} (e f : PlaquetteExpression base) (lag : Nat) : Q' :=
  boxPairBudget base nome hd hs (bound (fromUpper e)+1) (bound (fromLower f)+1) lag

theorem reflected_offset_distance (padding : Nat) (s t : Fin (padding+1)) :
    natDist (padding+padding-(padding-s.val)) (padding-t.val) = s.val+t.val := by
  have hs' := s.isLt
  have ht' := t.isLt
  unfold natDist
  omega

/-- Each probe retains its ORIGINAL base size, although the ambient slab grows. -/
theorem finite_time_covariance_bound {base : Nat} (padding : Nat) (s t : Fin (padding+1))
    (e f : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (covarianceSequence (bulkAtTime padding s e) (bulkAtTime padding t f) margin))
      (ofQ' (timeBudget e f (s.val+t.val))) := by
  have hp := reflected_covariance_pin nome nome_pos nome_lt_one
    (enlarge margin (bulkAtTime padding s e)) (enlarge margin (bulkAtTime padding t f))
  rw [← evaluate_fromUpper, ← evaluate_lower_enlarge, fromUpper_bulkAtTime, fromLower_bulkAtTime] at hp
  have h := placed_covariance_bound nome nome_pos nome_lt_one
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1 hd hs base padding
    (padding+padding-(padding-s.val)) (padding-t.val) margin (Nat.sub_le _ _)
    (Nat.le_trans (Nat.sub_le _ _) (by omega)) (fromUpper e) (fromLower f)
  rw [reflected_offset_distance padding s t] at h
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr hp)) h

/-- The existing thermodynamic limit, not a newly chosen limiting state. -/
theorem covarianceLimit_time_bound {base : Nat} (padding : Nat) (s t : Fin (padding+1))
    (e f : PlaquetteExpression base) :
    leEv (CReal.abs (covarianceLimit (bulkAtTime padding s e) (bulkAtTime padding t f)))
      (ofQ' (timeBudget e f (s.val+t.val))) :=
  leEv_of_convergesTo_le (convergesTo_abs (covariance_converges _ _))
    (convergesTo_const _) (finite_time_covariance_bound padding s t e f)

/-- Actual time separation, with no common-padding or volume parameter in the bound. -/
theorem timeCovariance_bound {base : Nat} (s t : Nat) (e f : PlaquetteExpression base) :
    leEv (CReal.abs (timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).1)
      (ofQ' (timeBudget e f (s+t))) := by
  let si : Fin (max s t+1) := ⟨s, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩
  let ti : Fin (max s t+1) := ⟨t, Nat.lt_succ_of_le (Nat.le_max_right _ _)⟩
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr
    (timeCovarianceRepresentative_bulk (max s t) si ti e f)))
    (covarianceLimit_time_bound (max s t) si ti e f)

/-- Witness, modulus, SAME operator pin and decay estimate are returned together. -/
def operatorDecayRepresentative {base : Nat} (s t : Nat) (e f : PlaquetteExpression base) :
    Σ' r : CReal, QCauchy r.approx ×'
      (completedInner (center (embedPresentation ⟨base,e⟩))
        (completedTime (s+t) (center (embedPresentation ⟨base,f⟩))) = Quotient.mk crealSetoid r) ×'
      leEv (CReal.abs r) (ofQ' (timeBudget e f (s+t))) :=
  ⟨(timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).1,
    (timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).2.1,
    (timeCovariance_operator_sum s t ⟨base,e⟩ ⟨base,f⟩).symm.trans
      (timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).2.2,
    timeCovariance_bound s t e f⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay.reflected_covariance_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay.timeBudget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay.reflected_offset_distance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay.finite_time_covariance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay.covarianceLimit_time_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay.timeCovariance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay.operatorDecayRepresentative
