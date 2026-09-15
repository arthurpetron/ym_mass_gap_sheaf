/-
# Repeated roots square to the SAME ORIGINAL input operator

The constructed interval-sequence root transformation induces a positive
symmetric contraction on the full original completion. Exact polynomial
pairings prove its square is the original input sequence action, not an
independently supplied root target. Centering and the possible kernel are
preserved. A positive square-root argument shows every fixed vector of
the parent is fixed by the root; in particular the first original root
fixes the original unit. Output representatives and rates remain explicit.

These laws enable coherent finite dyadic refinement, but do not establish
time injectivity, continuity at zero, geometric T1 identification, physical
scaling, a continuum theory or the Clay target. Nome and spacing are fixed.
-/

import YMGap.Continuum.UniformPolynomialRootTransform
import YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction

namespace YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence (abs_of_nonneg)
open YMGap.Continuum.UniformSquareRootIteration (residualStage)
open YMGap.Continuum.UniformPolynomialRootTransform
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef (completedInner_posdef)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer_unit)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus (center_polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction
  (rootAction rootAction_square rootAction_nonnegative)

local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem intervalAction_nonnegative (P : IntervalSequence) (x : Completion) :
    RCnonneg (completedInner (sequenceAction P.sequence x) x) :=
  sequenceAction_form_nonnegative _ (fun n t ht h1 => (P.bounds n t ht h1).1) x

theorem intervalAction_contraction (P : IntervalSequence) (x : Completion) :
    RCle (completedInner (sequenceAction P.sequence x) (sequenceAction P.sequence x)) (completedInner x x) := by
  have h := sequenceAction_tail_norm_bound P.sequence 0 1 Q'.zero_le_one (by
    intro n _ t ht h1
    rw [abs_of_nonneg (P.bounds n t ht h1).1]
    exact (P.bounds n t ht h1).2) x
  rw [scale_congr (by decide : Q'.eqv ((1 : Q')*1) 1),RCscale_one] at h
  exact h

def transformedAction (P : IntervalSequence) : Completion → Completion :=
  sequenceAction (rootTransform P).sequence

theorem transformedAction_symmetric (P : IntervalSequence) (x y : Completion) :
    completedInner (transformedAction P x) y=completedInner x (transformedAction P y) := sequenceAction_symmetric _ x y

theorem transformedAction_nonnegative (P : IntervalSequence) (x : Completion) :
    RCnonneg (completedInner (transformedAction P x) x) := intervalAction_nonnegative (rootTransform P) x

theorem transformedAction_contraction (P : IntervalSequence) (x : Completion) :
    RCle (completedInner (transformedAction P x) (transformedAction P x)) (completedInner x x) :=
  intervalAction_contraction (rootTransform P) x

theorem squareSequence_action (P : IntervalSequence) (x : Completion) :
    sequenceAction (squareSequence P) x=sequenceAction P.sequence x := by
  apply sequenceAction_congr _ _ residualStage
  intro epsilon he n hn t ht h1
  exact ⟨Q'.le_trans' _ _ _ (transformedSquare_le P n t ht h1) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)),
    transformedSquare_error P epsilon he n hn t ht h1⟩

theorem transformedAction_pairing (P : IntervalSequence) (x y : Completion) :
    completedInner (transformedAction P x) (transformedAction P y)=completedInner (sequenceAction P.sequence x) y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (actionRows (rootTransform P).sequence X) (actionRows (rootTransform P).sequence Y)
    (actionRows (squareSequence P) X) (constantRows Y) (by
      intro n
      rw [actionRows_pin,actionRows_pin,actionRows_pin,constantRows_pin]
      change completedInner (polynomialOperator (transformedPolynomial P n) (point X))
        (polynomialOperator (transformedPolynomial P n) (point Y))=
          completedInner (polynomialOperator (QPoly.pmul (transformedPolynomial P n) (transformedPolynomial P n)) (point X)) (point Y)
      rw [operator_mul]
      exact (operator_symmetric _ _ _).symm)
  rw [rowLimit_constant] at h
  change completedInner (transformedAction P (point X)) (transformedAction P (point Y))=
    completedInner (sequenceAction (squareSequence P) (point X)) (point Y) at h
  rw [squareSequence_action] at h
  exact h

/-- Every constructed root squares to the SAME input action, on every original vector. -/
theorem transformedAction_square (P : IntervalSequence) (x : Completion) :
    transformedAction P (transformedAction P x)=sequenceAction P.sequence x := by
  apply completed_eq_of_pairings
  intro y
  rw [transformedAction_symmetric,transformedAction_pairing]

theorem intervalAction_center (P : IntervalSequence) (x : Completion) :
    sequenceAction P.sequence (center x)=center (sequenceAction P.sequence x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h : representedAction P.sequence (centerCauchy X)=rowLimit (centeredRows (actionRows P.sequence X)) := by
    apply rowLimit_independent
    intro n
    rw [actionRows_pin,centeredRows_rowPoint,actionRows_pin]
    exact (center_polynomialVector (point X) (P.sequence.polynomial n) 0).symm
  exact h.trans (rowLimit_centeredRows _)

/-- Positivity forces a square-fixed vector to be fixed; no spectral uniqueness theorem is used. -/
theorem positive_square_fixed (S : Completion → Completion)
    (hsub : ∀ x y,S (completedSub x y)=completedSub (S x) (S y))
    (hpos : ∀ x,RCnonneg (completedInner (S x) x)) (x : Completion) (hsquare : S (S x)=x) : S x=x := by
  let d := completedSub (S x) x
  have hcancel : completedAdd (S d) d=completedZero := by
    change completedAdd (S (completedSub (S x) x)) (completedSub (S x) x)=completedZero
    rw [hsub,hsquare]
    unfold completedSub
    rw [completedAdd_assoc,← completedAdd_assoc (completedNeg (S x)) (S x) (completedNeg x),
      completedNeg_add,completedZero_add,completedAdd_comm,completedNeg_add]
  have h := RCadd_le_add (hpos d) (RCle_refl (completedInner d d))
  rw [rc_zero_add,← completedInner_add_left,hcancel,completedInner_zero_left] at h
  exact (completedDist_zero_iff _ _).mp (RCle_antisymm h (completedInner_nonnegative d))

theorem transformedAction_preserves_fixed (P : IntervalSequence) (x : Completion)
    (hx : sequenceAction P.sequence x=x) : transformedAction P x=x :=
  positive_square_fixed (transformedAction P) (sequenceAction_sub _) (transformedAction_nonnegative P) x
    ((transformedAction_square P x).trans hx)

theorem originalRoot_unit : rootAction completedUnit=completedUnit :=
  positive_square_fixed rootAction (sequenceAction_sub _) rootAction_nonnegative completedUnit
    ((rootAction_square completedUnit).trans twoStepTransfer_unit)

theorem sequenceAction_zero (P : UniformSequence) : sequenceAction P completedZero=completedZero := by
  have h := sequenceAction_smul P 0 completedZero
  simpa only [completedSmul_zero] using h

/-- Kernel equality is retained at each refinement; it is NOT a zero-kernel assertion. -/
theorem transformedAction_kernel (P : IntervalSequence) (x : Completion) :
    transformedAction P x=completedZero ↔ sequenceAction P.sequence x=completedZero := by
  constructor
  · intro h
    rw [← transformedAction_square,h]
    exact sequenceAction_zero _
  · intro h
    apply (completedInner_posdef _).mp
    rw [transformedAction_pairing,h,completedInner_zero_left]

def transformedActionCertificate (P : IntervalSequence) (X : seminorm.Cauchy) :=
  sequenceActionCertificate (rootTransform P).sequence X

end YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.intervalAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.intervalAction_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.squareSequence_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.intervalAction_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.positive_square_fixed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction_preserves_fixed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.originalRoot_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.sequenceAction_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedAction_kernel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction.transformedActionCertificate
