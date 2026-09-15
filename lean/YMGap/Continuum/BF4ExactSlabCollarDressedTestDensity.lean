/-
# Collar-dressed tests separate the SAME original completed states

For every supplied original Cauchy representative and positive squared-
distance tolerance, compute an expression f such that H*f approximates
that representative's class. The collar cutoff K is fixed but arbitrary.
The cofactor is an explicit finite geometric correction of a computed dense
approximant. No representative of an arbitrary quotient is selected.

Consequently a completed state orthogonal to every collar-dressed test is
zero, and agreement on all such tests implies equality of original states.
This is the existing finite-slab cutoff-limit OS completion, not a replacement
state space. The collar uses nome 1/1024; the underlying action may have any
0<w<1. These tests are NOT identified as time-transfer images. Thermodynamic
separation, T2 injectivity/range density and the continuum goal remain open.
-/

import YMGap.Continuum.BF4ExactSlabCollarTestNorm
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression
open YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector
open YMGap.Continuum.BF4ExactSlabCollarTestNorm
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.ScaledGNSCompletionEstimates (mul_mono_left)

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem zero_cross_distance (a b : RC) :
    RCsub (RCsub a RCzero) (RCsub RCzero b) = RCadd a b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.const 0))) (.neg (.add (.const 0) (.neg (.var 1)))))
      (.add (.var 0) (.var 1)) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem le_add_nonnegative {a b : RC} (hb : RCnonneg b) : RCle a (RCadd a b) := by
  refine Quotient.inductionOn₂ a b ?_ hb
  intro A B hB
  have hzero : Equiv (CReal.add A czero) A :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n))
  exact leEv_trans (leEv_of_equiv hzero.symm) (leEv_add (leEv_refl A) hB)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half
local notation "B" => completedInner w hw0 hw1
local notation "j" => embedExpression w hw0 hw1
local notation "Rq" q => Quotient.mk crealSetoid (ofQ' q)

theorem completed_corrected_norm_bound (K n : Nat) (e : PlaquetteExpression half) :
    RCle (B (j (correctedExpression K n e)) (j (correctedExpression K n e))) (Rq (bound e * 4)) := by
  rw [completedInner_embedExpression]
  exact corrected_form_bound w hw0 hw1 K n e

/-- A norm-relative comparison for an arbitrary UNCHANGED original completed state. -/
theorem unchanged_completed_pairing_bound (K n : Nat) (f : PlaquetteExpression half) (x : Completion w hw0 hw1 half) :
    RCle (RCmul (B x (j (correctedExpression K n f))) (B x (j (correctedExpression K n f))))
      (RCmul (B x x) (Rq (bound f * 4))) :=
  RCle_trans (completedInner_cauchySchwarz w hw0 hw1 x _)
    (mul_mono_left (completedInner_nonnegative w hw0 hw1 x) (completed_corrected_norm_bound w hw0 hw1 K n f))

theorem collarApproximation_bound (K : Nat) (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist w hw0 hw1 (j (collarApproximation K (approximationOrder e epsilon) e)) (j e)) (Rq epsilon) := by
  rw [completedDist_embedExpression]
  exact approximation_error_atOrder w hw0 hw1 K e epsilon he

/-- Cofactor data computed from the supplied representative and its own modulus. -/
def approximationCofactor (K : Nat) (X : (D).Cauchy) (epsilon : Q') : PlaquetteExpression half :=
  let e := X.seq (X.modulus (quarter epsilon))
  correctedExpression K (approximationOrder e (quarter epsilon)) e

theorem approximationCofactor_spec (K : Nat) (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist w hw0 hw1
      (j (.mul (collarExpression nome K half) (approximationCofactor w hw0 hw1 K X epsilon)))
      (Quotient.mk (D).completionSetoid X)) (Rq epsilon) := by
  let e := X.seq (X.modulus (quarter epsilon))
  exact completedDist_two_segment w hw0 hw1 _ (j e) _ epsilon
    (collarApproximation_bound w hw0 hw1 K e (quarter epsilon) (quarter_pos he))
    (constantApproximation_bound w hw0 hw1 X (quarter epsilon) (quarter_pos he) _ (Nat.le_refl _))

theorem norm_le_distance_of_orthogonal (x t : Completion w hw0 hw1 half) (h : B x t = RCzero) :
    RCle (B x x) (completedDist w hw0 hw1 x t) := by
  have ht : B t x = RCzero := (completedInner_symm w hw0 hw1 t x).trans h
  have hd : completedDist w hw0 hw1 x t = RCadd (B x x) (B t t) := by
    unfold completedDist
    rw [completedInner_sub_left, completedInner_sub_right, completedInner_sub_right, h, ht]
    exact zero_cross_distance _ _
  rw [hd]
  exact le_add_nonnegative (completedInner_nonnegative w hw0 hw1 t)

/-- No classical density theorem or representative selection is used. -/
theorem completed_zero_of_collar_tests (K : Nat) (x : Completion w hw0 hw1 half)
    (h : ∀ f : PlaquetteExpression half, B x (j (.mul (collarExpression nome K half) f)) = RCzero) :
    x = completedZero w hw0 hw1 half := by
  apply (completedInner_posdef w hw0 hw1 x).mp
  revert h
  refine Quotient.inductionOn x ?_
  intro X h
  apply Quotient.sound
  apply equiv_of_leEv_leEv ?_ (representativeInner_nonnegative w hw0 hw1 X)
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  have hb : leEv (representativeInner w hw0 hw1 X X) (ofQ' (HalfPow.half * epsilon)) := by
    change RCle (B (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid X))
      (Rq (HalfPow.half * epsilon))
    exact RCle_trans
      (norm_le_distance_of_orthogonal w hw0 hw1 _ _ (h (approximationCofactor w hw0 hw1 K X (HalfPow.half * epsilon))))
      (by rw [completedDist_symm]; exact approximationCofactor_spec w hw0 hw1 K X _ hh)
  obtain ⟨N, hN⟩ := hb (HalfPow.half * epsilon) hh
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))⟩

theorem completed_eq_of_collar_tests (K : Nat) (x y : Completion w hw0 hw1 half)
    (h : ∀ f : PlaquetteExpression half,
      B x (j (.mul (collarExpression nome K half) f)) = B y (j (.mul (collarExpression nome K half) f))) : x = y := by
  have hz : completedSub w hw0 hw1 x y = completedZero w hw0 hw1 half :=
    completed_zero_of_collar_tests w hw0 hw1 K _ (fun f => by
      rw [completedInner_sub_left, h f]
      exact rc_sub_self _)
  apply (completedDist_zero_iff w hw0 hw1 x y).mp
  unfold completedDist
  rw [hz, completedInner_zero_left]

theorem completed_eq_iff_collar_tests_eq (K : Nat) (x y : Completion w hw0 hw1 half) : x = y ↔
    ∀ f : PlaquetteExpression half,
      B x (j (.mul (collarExpression nome K half) f)) = B y (j (.mul (collarExpression nome K half) f)) :=
  ⟨fun h _ => congrArg (fun z => B z _) h, completed_eq_of_collar_tests w hw0 hw1 K x y⟩

end YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity

#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.completed_corrected_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.unchanged_completed_pairing_bound
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.collarApproximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.approximationCofactor
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.approximationCofactor_spec
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.norm_le_distance_of_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.completed_zero_of_collar_tests
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.completed_eq_of_collar_tests
#print axioms YMGap.Continuum.BF4ExactSlabCollarDressedTestDensity.completed_eq_iff_collar_tests_eq
