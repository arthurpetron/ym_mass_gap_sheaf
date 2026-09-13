/-
# Linear operations on the ORIGINAL plaquette completion

Addition has the squared-distance bound 2*d(x,x')+2*d(y,y'). Rational
scaling multiplies squared distance by c^2; epsilon/(c^2+1) is its
explicit positive input tolerance. These estimates construct operations
on the existing Cauchy completion, retaining all moduli as data.

The additive-group and rational-module laws descend from actual original
plaquette coefficient identities, through pointwise-null closeness with
modulus zero. No alternate carrier or analytic input is introduced.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

private theorem polynomial_smul_comm (a b : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul a (polySmul b p)) (polySmul b (polySmul a p)) :=
  (RatPolyCoeffEqv.smul_assoc a b p).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv a b) p).trans
      (RatPolyCoeffEqv.smul_assoc b a p).symm)

private theorem polynomial_smul_sub (c : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul c p) (polySmul (-1) (polySmul c q)))
      (polySmul c (polyAdd p (polySmul (-1) q))) :=
  ((RatPolyCoeffEqv.refl _).add (polynomial_smul_comm (-1) c q)).trans
    (RatPolyCoeffEqv.smul_add c p (polySmul (-1) q)).symm

private theorem polynomial_one_smul (p : RatPoly) : RatPolyCoeffEqv (polySmul 1 p) p :=
  fun weight => Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 1 p) (Q'.one_mul_eqv _)

theorem expression_smul_sub {half : Nat} (c : Q') (e f : PlaquetteExpression half) :
    expressionEqv (subtract (.smul c e) (.smul c f)) (.smul c (subtract e f)) :=
  ⟨polynomial_smul_sub c (lower e) (lower f), polynomial_smul_sub c (upper e) (upper f)⟩

private theorem scalarBudget_pos (c : Q') : (0 : Q') < c * c + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 (c * c) (SumOfSquares.q_mul_self_nonneg c))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

def scalarTolerance (c epsilon : Q') : Q' := Q'.divPos epsilon (c * c + 1) (scalarBudget_pos c)

theorem scalarTolerance_pos (c : Q') {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < scalarTolerance c epsilon := Q'.divPos_pos _ _ _ he

theorem scalarTolerance_bound (c : Q') {epsilon : Q'} (he : (0 : Q') < epsilon) :
    c * c * scalarTolerance c epsilon ≤ epsilon :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_self_of_nonneg (c * c) 1 Q'.zero_le_one) (Q'.le_of_lt (scalarTolerance_pos c he)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

theorem distSq_add (e e' f f' : PlaquetteExpression half) :
    leEv (distSq w hw0 hw1 (.add e f) (.add e' f'))
      (CReal.add (CReal.add (distSq w hw0 hw1 e e') (distSq w hw0 hw1 e e'))
        (CReal.add (distSq w hw0 hw1 f f') (distSq w hw0 hw1 f f'))) := by
  have he : expressionEqv (subtract (.add e f) (.add e' f')) (.add (subtract e e') (subtract f f')) :=
    (finiteGNSData w (Q'.le_of_lt hw0) 0 half).sub_sub_distrib e f e' f'
  exact leEv_trans (leEv_of_equiv (form_congr w hw0 hw1 he he))
    (pairing_add_bound w hw0 hw1 (subtract e e') (subtract f f'))

theorem form_smul_diagonal (c : Q') (e : PlaquetteExpression half) :
    Equiv (form w hw0 hw1 (.smul c e) (.smul c e))
      (CReal.mul (ofQ' (c * c)) (form w hw0 hw1 e e)) :=
  (form_smul_left w hw0 hw1 c e (.smul c e)).trans
    ((Pivot2.mul_congr_right (form_smul_right w hw0 hw1 c e e)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.mul_assoc_eqv c c _))))

theorem distSq_smul (c : Q') (e f : PlaquetteExpression half) :
    Equiv (distSq w hw0 hw1 (.smul c e) (.smul c f))
      (CReal.mul (ofQ' (c * c)) (distSq w hw0 hw1 e f)) :=
  (form_congr w hw0 hw1 (expression_smul_sub c e f) (expression_smul_sub c e f)).trans
    (form_smul_diagonal w hw0 hw1 c (subtract e f))

def addition : (D).BinaryQuadraticLipschitz where
  toFun := .add
  contraction := distSq_add w hw0 hw1

def scalarContinuous (c : Q') : (D).ModulusContinuous where
  toFun := .smul c
  tolerance := scalarTolerance c
  tolerance_pos := fun _ => scalarTolerance_pos c
  contraction := by
    intro epsilon he e f h
    have hc : leEv czero (ofQ' (c * c)) := leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg c)
    have hscaled := leEv_mul_nonneg_left hc h
    exact leEv_trans (leEv_of_equiv (distSq_smul w hw0 hw1 c e f))
      (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he)))

def completedAdd : Completion w hw0 hw1 half → Completion w hw0 hw1 half → Completion w hw0 hw1 half :=
  (addition w hw0 hw1).completionMap

def completedSmul (c : Q') : Completion w hw0 hw1 half → Completion w hw0 hw1 half :=
  (scalarContinuous w hw0 hw1 c).completionMap

def completedNeg : Completion w hw0 hw1 half → Completion w hw0 hw1 half := completedSmul w hw0 hw1 (-1)

theorem null_of_expressionEqv {e f : PlaquetteExpression half} (h : expressionEqv e f) : Null w hw0 hw1 e f :=
  (null_iff_pairing w hw0 hw1 e f).mpr (fun g =>
    pairing_congr w hw0 hw1 h ⟨RatPolyCoeffEqv.refl (lower g), RatPolyCoeffEqv.refl (upper g)⟩)

/-- All algebraic laws use the constant zero closeness modulus. -/
def closeOfPointwiseExpressionEqv {X Y : (D).Cauchy} (h : ∀ n, expressionEqv (X.seq n) (Y.seq n)) : (D).Close X Y :=
  SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => Quotient.exact (null_of_expressionEqv w hw0 hw1 (h n)))

theorem completion_eq_of_pointwise {X Y : (D).Cauchy} (h : ∀ n, expressionEqv (X.seq n) (Y.seq n)) :
    Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y :=
  Quotient.sound ⟨closeOfPointwiseExpressionEqv w hw0 hw1 h⟩

theorem completedAdd_embedExpression (e f : PlaquetteExpression half) :
    completedAdd w hw0 hw1 (embedExpression w hw0 hw1 e) (embedExpression w hw0 hw1 f) =
      embedExpression w hw0 hw1 (.add e f) := rfl

theorem completedSmul_embedExpression (c : Q') (e : PlaquetteExpression half) :
    completedSmul w hw0 hw1 c (embedExpression w hw0 hw1 e) = embedExpression w hw0 hw1 (.smul c e) := rfl

theorem completedAdd_assoc (x y z : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 (completedAdd w hw0 hw1 x y) z =
      completedAdd w hw0 hw1 x (completedAdd w hw0 hw1 y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact completion_eq_of_pointwise w hw0 hw1
    (fun n => (finiteGNSData w (Q'.le_of_lt hw0) 0 half).add_assoc (X.seq n) (Y.seq n) (Z.seq n))

theorem completedAdd_comm (x y : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 x y = completedAdd w hw0 hw1 y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise w hw0 hw1
    (fun n => (finiteGNSData w (Q'.le_of_lt hw0) 0 half).add_comm (X.seq n) (Y.seq n))

theorem completedZero_add (x : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 (completedZero w hw0 hw1 half) x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1
    (fun n => (finiteGNSData w (Q'.le_of_lt hw0) 0 half).zero_add (X.seq n))

theorem completedNeg_add (x : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 (completedNeg w hw0 hw1 x) x = completedZero w hw0 hw1 half := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1
    (fun n => (finiteGNSData w (Q'.le_of_lt hw0) 0 half).neg_add (X.seq n))

theorem completedSmul_one (x : Completion w hw0 hw1 half) : completedSmul w hw0 hw1 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1
    (fun n => ⟨polynomial_one_smul (lower (X.seq n)), polynomial_one_smul (upper (X.seq n))⟩)

theorem completedSmul_zero (x : Completion w hw0 hw1 half) :
    completedSmul w hw0 hw1 0 x = completedZero w hw0 hw1 half := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨(RatPolyCoeffEqv.zero_smul (lower (X.seq n))).trans (RatPolyCoeffEqv.zero_smul polyOne).symm,
     (RatPolyCoeffEqv.zero_smul (upper (X.seq n))).trans (RatPolyCoeffEqv.zero_smul polyOne).symm⟩)

theorem completedSmul_mul (a b : Q') (x : Completion w hw0 hw1 half) :
    completedSmul w hw0 hw1 a (completedSmul w hw0 hw1 b x) = completedSmul w hw0 hw1 (a * b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨RatPolyCoeffEqv.smul_assoc a b (lower (X.seq n)), RatPolyCoeffEqv.smul_assoc a b (upper (X.seq n))⟩)

theorem completedSmul_add (c : Q') (x y : Completion w hw0 hw1 half) :
    completedSmul w hw0 hw1 c (completedAdd w hw0 hw1 x y) =
      completedAdd w hw0 hw1 (completedSmul w hw0 hw1 c x) (completedSmul w hw0 hw1 c y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨RatPolyCoeffEqv.smul_add c (lower (X.seq n)) (lower (Y.seq n)),
     RatPolyCoeffEqv.smul_add c (upper (X.seq n)) (upper (Y.seq n))⟩)

theorem completedAdd_smul (a b : Q') (x : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 (completedSmul w hw0 hw1 a x) (completedSmul w hw0 hw1 b x) =
      completedSmul w hw0 hw1 (a + b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨RatPolyCoeffEqv.add_smul_same a b (lower (X.seq n)), RatPolyCoeffEqv.add_smul_same a b (upper (X.seq n))⟩)

theorem completedSmul_congr {a b : Q'} (h : a.eqv b) (x : Completion w hw0 hw1 half) :
    completedSmul w hw0 hw1 a x = completedSmul w hw0 hw1 b x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise w hw0 hw1 (fun n =>
    ⟨RatPolyCoeffEqv.smul_coefficient h (lower (X.seq n)), RatPolyCoeffEqv.smul_coefficient h (upper (X.seq n))⟩)

end YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.expression_smul_sub
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.scalarTolerance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.scalarTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.scalarTolerance_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.distSq_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.form_smul_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.distSq_smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.addition
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.scalarContinuous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedAdd
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedSmul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedNeg
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.null_of_expressionEqv
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.closeOfPointwiseExpressionEqv
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completion_eq_of_pointwise
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedAdd_embedExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedSmul_embedExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedAdd_assoc
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedAdd_comm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedZero_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedNeg_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedSmul_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedSmul_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedSmul_mul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedSmul_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedAdd_smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear.completedSmul_congr
