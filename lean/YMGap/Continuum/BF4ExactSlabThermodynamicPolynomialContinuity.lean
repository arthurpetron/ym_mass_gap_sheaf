/-
# Explicit continuity of polynomial action on the ORIGINAL completion

The finite coefficient recursion K([])=0, K(c::p)=2*c^2+2*K(p)
bounds squared norm on every original completed vector. It is used only
to supply continuity and identify limits of the existing polynomial action;
it does not replace the sharper cyclic bound or a physical gap estimate.
Input tolerance epsilon/(K+1) is explicit, with no square-root selection.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
import YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (norm_add_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero scale_add)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def normFactor : QPoly.Poly → Q'
  | [] => 0
  | c::p => (c*c+c*c)+(normFactor p+normFactor p)

theorem normFactor_nonnegative (p : QPoly.Poly) : (0 : Q')≤normFactor p := by
  induction p with
  | nil => exact Q'.le_refl' _
  | cons c p ih =>
      exact Q'.zero_le_add _ _
        (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg c) (SumOfSquares.q_mul_self_nonneg c))
        (Q'.zero_le_add _ _ ih ih)

theorem smul_norm (c : Q') (x : Completion) :
    completedInner (completedSmul c x) (completedSmul c x)=RCscale (c*c) (completedInner x x) := by
  rw [completedInner_smul_left,completedInner_smul_right]
  refine Quotient.inductionOn (completedInner x x) ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.mul_assoc_eqv c c (A.approx n))))

theorem vector_norm_bound (p : QPoly.Poly) (x : Completion) (r : Nat) :
    RCle (completedInner (polynomialVector x p r) (polynomialVector x p r))
      (RCscale (normFactor p) (completedInner x x)) := by
  induction p generalizing r with
  | nil =>
      simp only [polynomialVector,normFactor,completedInner_zero_left,scale_zero]
      exact RCle_refl _
  | cons c p ih =>
      have hs : RCle (completedInner (completedSmul c (completedTime (r+r) x))
          (completedSmul c (completedTime (r+r) x))) (RCscale (c*c) (completedInner x x)) := by
        rw [smul_norm]
        exact RCscale_mono (SumOfSquares.q_mul_self_nonneg c) (completedTime_contraction _ x)
      have h := RCle_trans (norm_add_bound (completedSmul c (completedTime (r+r) x))
        (polynomialVector x p (r+1)))
        (RCadd_le_add (RCadd_le_add hs hs) (RCadd_le_add (ih (r+1)) (ih (r+1))))
      rw [← scale_add,← scale_add,← scale_add] at h
      exact h

theorem operator_distance_bound (p : QPoly.Poly) (x y : Completion) :
    RCle (completedDist (polynomialOperator p x) (polynomialOperator p y))
      (RCscale (normFactor p) (completedDist x y)) := by
  unfold polynomialOperator completedDist
  rw [← vector_base_sub]
  exact vector_norm_bound p (completedSub x y) 0

theorem positiveBudget (B : Q') (hB : (0 : Q')≤B) : (0 : Q')<B+1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q')<1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 B hB) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

def linearTolerance (B : Q') (hB : (0 : Q')≤B) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (B+1) (positiveBudget B hB)

theorem linearTolerance_pos (B : Q') (hB : (0 : Q')≤B) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<linearTolerance B hB epsilon := Q'.divPos_pos _ _ _ he

theorem linearTolerance_total (B : Q') (hB : (0 : Q')≤B) (epsilon : Q') :
    Q'.eqv ((B+1)*linearTolerance B hB epsilon) epsilon :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)

theorem linearTolerance_budget (B : Q') (hB : (0 : Q')≤B) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    B*linearTolerance B hB epsilon≤epsilon :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.add_le_self_of_nonneg B 1 Q'.zero_le_one) (Q'.le_of_lt (linearTolerance_pos B hB he)))
    (Q'.le_of_eqv (linearTolerance_total B hB epsilon))

def operatorTolerance (p : QPoly.Poly) (epsilon : Q') : Q' :=
  linearTolerance (normFactor p) (normFactor_nonnegative p) epsilon

theorem operatorTolerance_pos (p : QPoly.Poly) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<operatorTolerance p epsilon := linearTolerance_pos _ _ he

theorem operator_close (p : QPoly.Poly) (x y : Completion) (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : RCle (completedDist x y) (rat (operatorTolerance p epsilon))) :
    RCle (completedDist (polynomialOperator p x) (polynomialOperator p y)) (rat epsilon) :=
  RCle_trans (operator_distance_bound p x y) (RCle_trans
    (RCscale_mono (normFactor_nonnegative p) h)
    (leEv_le_ofQ'_of_approx_le (fun _ => linearTolerance_budget (normFactor p) (normFactor_nonnegative p) he)))

end YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.normFactor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.normFactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.smul_norm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.vector_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.operator_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.positiveBudget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.linearTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.linearTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.linearTolerance_total
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.linearTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.operatorTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.operatorTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity.operator_close
