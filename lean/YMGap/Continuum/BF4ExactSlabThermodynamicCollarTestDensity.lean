/-
# Actual thermodynamic collar tests approximate and separate original states

For each fixed source expression, its SAME collar correction has a uniform
error under the actual enlargements. Passing through the already constructed
original form limit preserves bound(e)*2^(-2n), with the source-derived order.
Supplied original Cauchy representatives then compute collar-dressed nearby
presentations in the SAME thermodynamic completion.

The separating family ranges over source bases and their collar-dressed
expressions. This does not claim density for multiplication by one fixed
collar at all bases, or an OS quotient multiplication operator. No tests are
identified with time-transfer images. T2 range density/injectivity, physical
time zero and the spacing/continuum and all-group Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabBulkCollarApproximation
import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
import YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression (collarExpression)
open YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector (correctedExpression)
open YMGap.Continuum.BF4ExactSlabCollarTestNorm
  (approximationError approximationOrder collarApproximation approximation_order_budget)
open YMGap.Continuum.BF4ExactSlabBulkCollarApproximation (bulk_approximation_error_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound (bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient (subtract)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local notation "D" => seminorm
local notation "B" => completedInner
local notation "j" => embedPresentation
local notation "Rq" q => Quotient.mk crealSetoid (ofQ' q)

theorem thermodynamic_approximation_error_bound (K n : Nat) {base : Nat} (e : PlaquetteExpression base) :
    leEv (formLimit (approximationError K n e) (approximationError K n e))
      (ofQ' (bound e * (HalfPow.half^n * HalfPow.half^n))) :=
  leEv_of_convergesTo_le (form_converges _ _) (convergesTo_const _)
    (fun padding => bulk_approximation_error_bound nome nome_pos nome_lt_one padding ⟨0, Nat.zero_lt_succ _⟩ K n e)

theorem thermodynamic_approximation_error_atOrder (K : Nat) {base : Nat} (e : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    leEv (formLimit (approximationError K (approximationOrder e epsilon) e)
      (approximationError K (approximationOrder e epsilon) e)) (ofQ' epsilon) :=
  leEv_trans (thermodynamic_approximation_error_bound K _ e)
    (leEv_ofQ'_of_approx_ge (fun _ => approximation_order_budget e epsilon he))

private theorem sameBase_subtract {base : Nat} (e f : PlaquetteExpression base) :
    subtract (embed ⟨base, e⟩) (embed ⟨base, f⟩) =
      embed ⟨base, BF4ExactSlabPlaquetteNullQuotient.subtract e f⟩ := by
  change embed (presentationSubtract ⟨base,e⟩ ⟨base,f⟩) = _
  apply embed_eq_of_coeff _ _ (base+base) (Nat.le_refl _) (Nat.le_add_right _ _)
  intro volume hv
  rw [show presentationSubtract ⟨base,e⟩ ⟨base,f⟩ = add ⟨base,e⟩ (smul (-1) ⟨base,f⟩) from rfl,
    polynomial_add _ _ volume hv]
  exact RatPolyCoeffEqv.refl _

theorem collarApproximation_bound (K : Nat) {base : Nat} (e : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist (j ⟨base, collarApproximation K (approximationOrder e epsilon) e⟩) (j ⟨base,e⟩)) (Rq epsilon) := by
  rw [← embedObservable_embed, ← embedObservable_embed, completedDist_embedObservable, sameBase_subtract, pairing_sameBase]
  exact thermodynamic_approximation_error_atOrder K e epsilon he

/-- A test is an actual source presentation, dressed by that source's collar. -/
def dressedTest (K : Nat) (p : Presentation) : Presentation :=
  ⟨p.base, .mul (collarExpression nome K p.base) p.expression⟩

/-- Computes the source base, cofactor and correction order from supplied data. -/
def approximationCofactor (K : Nat) (X : (D).Cauchy) (epsilon : Q') : Presentation :=
  let p := X.seq (X.modulus (quarter epsilon))
  ⟨p.base, correctedExpression K (approximationOrder p.expression (quarter epsilon)) p.expression⟩

theorem approximationCofactor_spec (K : Nat) (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist (j (dressedTest K (approximationCofactor K X epsilon)))
      (Quotient.mk (D).completionSetoid X)) (Rq epsilon) := by
  let p := X.seq (X.modulus (quarter epsilon))
  exact completedDist_two_segment _ (j p) _ epsilon
    (collarApproximation_bound K p.expression (quarter epsilon) (quarter_pos he))
    (constantApproximation_bound X (quarter epsilon) (quarter_pos he) _ (Nat.le_refl _))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem zero_cross_distance (a b : RC) :
    RCsub (RCsub a RCzero) (RCsub RCzero b) = RCadd a b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.const 0))) (.neg (.add (.const 0) (.neg (.var 1)))))
      (.add (.var 0) (.var 1)) (by decide) (fun | 0 => A.approx n | _ => C.approx n)))

private theorem le_add_nonnegative {a b : RC} (hb : RCnonneg b) : RCle a (RCadd a b) := by
  refine Quotient.inductionOn₂ a b ?_ hb
  intro A C hC
  have hzero : Equiv (CReal.add A czero) A :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n))
  exact leEv_trans (leEv_of_equiv hzero.symm) (leEv_add (leEv_refl A) hC)

theorem norm_le_distance_of_orthogonal (x t : Completion) (h : B x t = RCzero) :
    RCle (B x x) (completedDist x t) := by
  have ht : B t x = RCzero := (completedInner_symm t x).trans h
  have hd : completedDist x t = RCadd (B x x) (B t t) := by
    unfold completedDist
    rw [completedInner_sub_left, completedInner_sub_right, completedInner_sub_right, h, ht]
    exact zero_cross_distance _ _
  rw [hd]
  exact le_add_nonnegative (completedInner_nonnegative t)

/-- This family separates the SAME original thermodynamic completed states. -/
theorem completed_zero_of_collar_tests (K : Nat) (x : Completion)
    (h : ∀ p : Presentation, B x (j (dressedTest K p)) = RCzero) : x = completedZero := by
  apply (completedInner_posdef x).mp
  revert h
  refine Quotient.inductionOn x ?_
  intro X h
  apply Quotient.sound
  apply equiv_of_leEv_leEv ?_ (representativeInner_nonnegative X)
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  have hb : leEv (representativeInner X X) (ofQ' (HalfPow.half * epsilon)) := by
    change RCle (B (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid X))
      (Rq (HalfPow.half * epsilon))
    exact RCle_trans
      (norm_le_distance_of_orthogonal _ _ (h (approximationCofactor K X (HalfPow.half * epsilon))))
      (by rw [completedDist_symm]; exact approximationCofactor_spec K X _ hh)
  obtain ⟨N, hN⟩ := hb (HalfPow.half * epsilon) hh
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))⟩

theorem completed_eq_of_collar_tests (K : Nat) (x y : Completion)
    (h : ∀ p : Presentation, B x (j (dressedTest K p)) = B y (j (dressedTest K p))) : x = y := by
  have hz : completedSub x y = completedZero := completed_zero_of_collar_tests K _ (fun p => by
    rw [completedInner_sub_left, h p]
    exact rc_sub_self _)
  apply (completedDist_zero_iff x y).mp
  unfold completedDist
  rw [hz, completedInner_zero_left]

theorem completed_eq_iff_collar_tests_eq (K : Nat) (x y : Completion) : x = y ↔
    ∀ p : Presentation, B x (j (dressedTest K p)) = B y (j (dressedTest K p)) :=
  ⟨fun h _ => congrArg (fun z => B z _) h, completed_eq_of_collar_tests K x y⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.thermodynamic_approximation_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.thermodynamic_approximation_error_atOrder
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.collarApproximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.dressedTest
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.approximationCofactor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.approximationCofactor_spec
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.norm_le_distance_of_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.completed_zero_of_collar_tests
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.completed_eq_of_collar_tests
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCollarTestDensity.completed_eq_iff_collar_tests_eq
