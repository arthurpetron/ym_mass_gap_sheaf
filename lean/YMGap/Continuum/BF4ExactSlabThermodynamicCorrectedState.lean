/-
# Jointly cutoff-removed ORIGINAL collar corrections and their cancellation

The existing correctedExpression K K e now defines an actual Cauchy state
in the existing thermodynamic completion. Both heat cutoff and geometric
correction order tend to infinity with one source-dependent modulus.
Re-dressing the SAME samples by their SAME finite heat collar gives a
second Cauchy representative whose completed state equals the original e.

These are computed sequences of original expressions. No product on OS
quotient classes is defined or assumed. In particular the corrected limit
is not yet identified with a time-transfer preimage. The action remains
SU(2), nome 1/1024 and fixed spacing; the physical continuum goal is open.
-/

import YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm
import YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound (bound bound_nonnegative)
open YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector (correctedExpression)
open YMGap.Continuum.BF4ExactSlabCollarTestNorm (collarApproximation approximationError)
open YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient (subtract)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity (thermodynamic_approximation_error_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (correctionOrder correctionOrder_budget)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local notation "Rq" q => Quotient.mk crealSetoid (ofQ' q)

private theorem geometric_budget (c : Q') (hc : (0 : Q') ≤ c)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat) (hK : correctionOrder c hc epsilon ≤ K) :
    c*(HalfPow.half^K*HalfPow.half^K) ≤ epsilon := by
  have hpow : (0 : Q') ≤ HalfPow.half^K := Q'.pow_nonneg _ (by decide) K
  have hsmall : HalfPow.half^K ≤ (1 : Q') := half_pow_antitone 0 K (Nat.zero_le _)
  have hsquare : HalfPow.half^K*HalfPow.half^K ≤ HalfPow.half^K :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall hpow)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hsquare hc)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (half_pow_antitone _ K hK) hc)
      (correctionOrder_budget c hc epsilon he))

def cutoffConstant {half : Nat} (e : PlaquetteExpression half) : Q' := bound e*(tailCap half*tailCap half)

theorem cutoffConstant_nonnegative {half : Nat} (e : PlaquetteExpression half) : (0 : Q') ≤ cutoffConstant e :=
  Q'.mul_nonneg _ _ (bound_nonnegative e) (Q'.mul_nonneg _ _ (tailCap_nonnegative half) (tailCap_nonnegative half))

def cutoffModulus {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  correctionOrder (cutoffConstant e) (cutoffConstant_nonnegative e) epsilon

theorem cutoff_budget {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K : Nat) (hK : cutoffModulus e epsilon ≤ K) :
    bound e*((tailCap half*HalfPow.half^K)*(tailCap half*HalfPow.half^K)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
    (by decide) (fun | 0 => bound e | 1 => tailCap half | _ => HalfPow.half^K)))
    (geometric_budget (cutoffConstant e) (cutoffConstant_nonnegative e) epsilon he K hK)

def sample {half : Nat} (e : PlaquetteExpression half) (K : Nat) : Presentation :=
  ⟨half,correctedExpression K K e⟩

private theorem sameBase_subtract {base : Nat} (e f : PlaquetteExpression base) :
    subtract (embed ⟨base,e⟩) (embed ⟨base,f⟩) =
      embed ⟨base,BF4ExactSlabPlaquetteNullQuotient.subtract e f⟩ := by
  change embed (presentationSubtract ⟨base,e⟩ ⟨base,f⟩) = _
  apply embed_eq_of_coeff _ _ (base+base) (Nat.le_refl _) (Nat.le_add_right _ _)
  intro volume hv
  rw [show presentationSubtract ⟨base,e⟩ ⟨base,f⟩ = add ⟨base,e⟩ (smul (-1) ⟨base,f⟩) from rfl,
    polynomial_add _ _ volume hv]
  exact RatPolyCoeffEqv.refl _

theorem sample_distance {half : Nat} (e : PlaquetteExpression half) (K L : Nat) :
    Equiv (distSq (sample e (K+L)) (sample e K))
      (formLimit (correctedDifference K L e) (correctedDifference K L e)) := by
  apply Quotient.exact (s := crealSetoid)
  rw [distSq_pin]
  unfold sample
  rw [sameBase_subtract,pairing_sameBase]
  rfl

theorem sample_append_bound {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : cutoffModulus e epsilon ≤ K) :
    leEv (distSq (sample e (K+L)) (sample e K)) (ofQ' epsilon) :=
  leEv_trans (leEv_of_equiv (sample_distance e K L))
    (leEv_trans (thermodynamic_norm_bound K L e)
      (leEv_ofQ'_of_approx_ge (fun _ => cutoff_budget e epsilon he K hK)))

theorem sample_cauchy {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : cutoffModulus e epsilon ≤ m) (hn : cutoffModulus e epsilon ≤ n) :
    leEv (distSq (sample e m) (sample e n)) (ofQ' epsilon) := by
  cases Nat.le_total m n with
  | inl h =>
      have hb := sample_append_bound e epsilon he m (n-m) hm
      rw [Nat.add_sub_of_le h] at hb
      exact leEv_trans (leEv_of_equiv (distSq_symm _ _)) hb
  | inr h =>
      have hb := sample_append_bound e epsilon he n (m-n) hn
      rwa [Nat.add_sub_of_le h] at hb

def cauchy {half : Nat} (e : PlaquetteExpression half) : seminorm.Cauchy where
  seq := sample e
  modulus := cutoffModulus e
  isCauchy := sample_cauchy e

def state {half : Nat} (e : PlaquetteExpression half) : Completion :=
  Quotient.mk seminorm.completionSetoid (cauchy e)

theorem state_approximation {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat) (hK : cutoffModulus e epsilon ≤ K) :
    RCle (completedDist (embedPresentation (sample e K)) (state e)) (Rq epsilon) :=
  constantApproximation_bound (cauchy e) epsilon he K hK

/-- Re-dress the SAME correction sample by its SAME cutoff heat collar. -/
def redressedSample {half : Nat} (e : PlaquetteExpression half) (K : Nat) : Presentation :=
  ⟨half,collarApproximation K K e⟩

def redressingModulus {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  correctionOrder (bound e) (bound_nonnegative e) epsilon

theorem redressed_distance {half : Nat} (e : PlaquetteExpression half) (K : Nat) :
    Equiv (distSq (redressedSample e K) ⟨half,e⟩)
      (formLimit (approximationError K K e) (approximationError K K e)) := by
  apply Quotient.exact (s := crealSetoid)
  rw [distSq_pin]
  unfold redressedSample
  rw [sameBase_subtract,pairing_sameBase]
  rfl

theorem redressed_atCutoff {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat) (hK : redressingModulus e epsilon ≤ K) :
    leEv (distSq (redressedSample e K) ⟨half,e⟩) (ofQ' epsilon) :=
  leEv_trans (leEv_of_equiv (redressed_distance e K))
    (leEv_trans (thermodynamic_approximation_error_bound K K e)
      (leEv_ofQ'_of_approx_ge (fun _ => geometric_budget (bound e) (bound_nonnegative e) epsilon he K hK)))

def redressedCauchy {half : Nat} (e : PlaquetteExpression half) : seminorm.Cauchy where
  seq := redressedSample e
  modulus := fun epsilon => redressingModulus e (quarter epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    have hleft : RCle (completedDist (embedPresentation (redressedSample e m)) (embedPresentation ⟨half,e⟩))
        (Rq (quarter epsilon)) := by
      rw [completedDist_embedPresentation]
      exact redressed_atCutoff e (quarter epsilon) (quarter_pos he) m hm
    have hright : RCle (completedDist (embedPresentation ⟨half,e⟩) (embedPresentation (redressedSample e n)))
        (Rq (quarter epsilon)) := by
      rw [completedDist_symm,completedDist_embedPresentation]
      exact redressed_atCutoff e (quarter epsilon) (quarter_pos he) n hn
    have h := completedDist_two_segment _ _ _ epsilon hleft hright
    rw [completedDist_embedPresentation] at h
    exact h

/-- The closeness witness retains its explicit modulus as data. -/
def redressedClose {half : Nat} (e : PlaquetteExpression half) :
    seminorm.Close (redressedCauchy e) (seminorm.constant ⟨half,e⟩) where
  modulus := redressingModulus e
  close := redressed_atCutoff e

theorem redressed_limit_eq {half : Nat} (e : PlaquetteExpression half) :
    Quotient.mk seminorm.completionSetoid (redressedCauchy e) = embedPresentation ⟨half,e⟩ :=
  Quotient.sound ⟨redressedClose e⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.cutoffConstant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.cutoffConstant_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.cutoffModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.cutoff_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.sample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.sample_distance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.sample_append_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.sample_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.cauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.state_approximation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.redressedSample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.redressingModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.redressed_distance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.redressed_atCutoff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.redressedCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.redressedClose
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCorrectedState.redressed_limit_eq
