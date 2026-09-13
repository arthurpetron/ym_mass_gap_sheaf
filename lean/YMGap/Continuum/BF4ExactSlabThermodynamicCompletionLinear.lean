/-
# Linear operations on the ORIGINAL thermodynamic completion

Semantic observable algebra supplies the difference identities. The SAME
constructed squared distance then has the addition bound 2*d+2*d and
rational scaling law c^2*d. Explicit tolerances construct the completed
operations; all their laws descend by pointwise semantic equality.

Only the generic rational scalar tolerance is reused from the finite
module. No finite-slab carrier, form or physical dynamics is substituted.
Bilinearity and constructive approximation/completeness follow separately.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)

local notation "D" => seminorm

private theorem qadd_shuffle (a b c d : Observable) :
    qadd (qadd a b) (qadd c d) = qadd (qadd a c) (qadd b d) := by
  rw [qadd_assoc a b (qadd c d), ← qadd_assoc b c d, qadd_comm b c,
    qadd_assoc c b d, ← qadd_assoc a c (qadd b d)]

theorem subtract_add (x y x' y' : Observable) :
    subtract (qadd x y) (qadd x' y') = qadd (subtract x x') (subtract y y') := by
  unfold subtract
  rw [qsmul_add]
  exact qadd_shuffle x y (qsmul (-1) x') (qsmul (-1) y')

theorem subtract_smul (c : Q') (x y : Observable) :
    subtract (qsmul c x) (qsmul c y) = qsmul c (subtract x y) := by
  unfold subtract
  rw [qsmul_add, qsmul_assoc, qsmul_assoc]
  exact congrArg (qadd (qsmul c x)) (qsmul_coefficient (Q'.mul_comm_eqv (-1) c) y)

theorem zero_smul (x : Observable) : qsmul 0 x = zero := by
  have h := add_smul 1 (-1) x
  rw [one_smul, qadd_comm, neg_add] at h
  exact (qsmul_coefficient (by decide : Q'.eqv 0 (1 + (-1))) x).trans h

theorem presentedForm_add_left (p q r : Presentation) :
    Equiv (presentedForm (add p q) r) (CReal.add (presentedForm p r) (presentedForm q r)) :=
  Quotient.exact (pairing_add_left (embed p) (embed q) (embed r))

theorem presentedForm_smul_left (c : Q') (p q : Presentation) :
    Equiv (presentedForm (smul c p) q) (CReal.mul (ofQ' c) (presentedForm p q)) :=
  Quotient.exact (pairing_smul_left c (embed p) (embed q))

theorem presentedForm_smul_right (c : Q') (p q : Presentation) :
    Equiv (presentedForm p (smul c q)) (CReal.mul (ofQ' c) (presentedForm p q)) :=
  Quotient.exact (pairing_smul_right c (embed p) (embed q))

theorem presentedForm_smul_diagonal (c : Q') (p : Presentation) :
    Equiv (presentedForm (smul c p) (smul c p))
      (CReal.mul (ofQ' (c * c)) (presentedForm p p)) :=
  (presentedForm_smul_left c p (smul c p)).trans
    ((Pivot2.mul_congr_right (presentedForm_smul_right c p p)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.mul_assoc_eqv c c _))))

theorem distSq_add (p p' q q' : Presentation) :
    leEv (distSq (add p q) (add p' q'))
      (CReal.add (CReal.add (distSq p p') (distSq p p'))
        (CReal.add (distSq q q') (distSq q q'))) := by
  have h := pairing_add_bound (subtract (embed p) (embed p')) (subtract (embed q) (embed q'))
  rw [← subtract_add] at h
  exact h

theorem distSq_smul (c : Q') (p q : Presentation) :
    Equiv (distSq (smul c p) (smul c q)) (CReal.mul (ofQ' (c * c)) (distSq p q)) := by
  have h : Equiv (distSq (smul c p) (smul c q))
      (presentedForm (smul c (presentationSubtract p q)) (smul c (presentationSubtract p q))) := by
    apply Quotient.exact (s := crealSetoid)
    change pairing (subtract (qsmul c (embed p)) (qsmul c (embed q)))
        (subtract (qsmul c (embed p)) (qsmul c (embed q))) =
      pairing (qsmul c (subtract (embed p) (embed q))) (qsmul c (subtract (embed p) (embed q)))
    rw [subtract_smul]
  exact h.trans (presentedForm_smul_diagonal c (presentationSubtract p q))

def addition : (D).BinaryQuadraticLipschitz where
  toFun := add
  contraction := distSq_add

def scalarContinuous (c : Q') : (D).ModulusContinuous where
  toFun := smul c
  tolerance := scalarTolerance c
  tolerance_pos := fun _ => scalarTolerance_pos c
  contraction := by
    intro epsilon he p q h
    have hc : leEv czero (ofQ' (c * c)) := leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg c)
    have hscaled := leEv_mul_nonneg_left hc h
    exact leEv_trans (leEv_of_equiv (distSq_smul c p q))
      (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he)))

def completedAdd : Completion → Completion → Completion := addition.completionMap

def completedSmul (c : Q') : Completion → Completion := (scalarContinuous c).completionMap

def completedNeg : Completion → Completion := completedSmul (-1)

/-- Semantic equality yields a constant-zero closeness modulus. -/
def closeOfPointwiseObservableEq {X Y : (D).Cauchy}
    (h : ∀ n, embed (X.seq n) = embed (Y.seq n)) : (D).Close X Y :=
  SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => (distSq_null_iff _ _).mpr ((null_iff_pairing _ _).mpr
      (fun z => congrArg (fun x => pairing x z) (h n))))

theorem completion_eq_of_pointwise {X Y : (D).Cauchy}
    (h : ∀ n, embed (X.seq n) = embed (Y.seq n)) :
    Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y :=
  Quotient.sound ⟨closeOfPointwiseObservableEq h⟩

theorem completedAdd_embedPresentation (p q : Presentation) :
    completedAdd (embedPresentation p) (embedPresentation q) = embedPresentation (add p q) := rfl

theorem completedSmul_embedPresentation (c : Q') (p : Presentation) :
    completedSmul c (embedPresentation p) = embedPresentation (smul c p) := rfl

theorem completedAdd_embedObservable (x y : Observable) :
    completedAdd (embedObservable x) (embedObservable y) = embedObservable (qadd x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact completedAdd_embedPresentation

theorem completedSmul_embedObservable (c : Q') (x : Observable) :
    completedSmul c (embedObservable x) = embedObservable (qsmul c x) := by
  refine Quotient.inductionOn x ?_
  exact completedSmul_embedPresentation c

theorem completedAdd_embedOSQuotient (x y : Carrier) :
    completedAdd (embedOSQuotient x) (embedOSQuotient y) = embedOSQuotient (osAdd x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact completedAdd_embedObservable

theorem completedSmul_embedOSQuotient (c : Q') (x : Carrier) :
    completedSmul c (embedOSQuotient x) = embedOSQuotient (osSmul c x) := by
  refine Quotient.inductionOn x ?_
  exact completedSmul_embedObservable c

theorem completedAdd_assoc (x y z : Completion) :
    completedAdd (completedAdd x y) z = completedAdd x (completedAdd y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact completion_eq_of_pointwise (fun n => qadd_assoc (embed (X.seq n)) (embed (Y.seq n)) (embed (Z.seq n)))

theorem completedAdd_comm (x y : Completion) : completedAdd x y = completedAdd y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise (fun n => qadd_comm (embed (X.seq n)) (embed (Y.seq n)))

theorem completedZero_add (x : Completion) : completedAdd completedZero x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => zero_add (embed (X.seq n)))

theorem completedNeg_add (x : Completion) : completedAdd (completedNeg x) x = completedZero := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => neg_add (embed (X.seq n)))

theorem completedSmul_one (x : Completion) : completedSmul 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => one_smul (embed (X.seq n)))

theorem completedSmul_zero (x : Completion) : completedSmul 0 x = completedZero := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => zero_smul (embed (X.seq n)))

theorem completedSmul_mul (a b : Q') (x : Completion) :
    completedSmul a (completedSmul b x) = completedSmul (a * b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => qsmul_assoc a b (embed (X.seq n)))

theorem completedSmul_add (c : Q') (x y : Completion) :
    completedSmul c (completedAdd x y) = completedAdd (completedSmul c x) (completedSmul c y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise (fun n => qsmul_add c (embed (X.seq n)) (embed (Y.seq n)))

theorem completedAdd_smul (a b : Q') (x : Completion) :
    completedAdd (completedSmul a x) (completedSmul b x) = completedSmul (a + b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => (add_smul a b (embed (X.seq n))).symm)

theorem completedSmul_congr {a b : Q'} (h : a.eqv b) (x : Completion) :
    completedSmul a x = completedSmul b x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun n => qsmul_coefficient h (embed (X.seq n)))

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.subtract_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.subtract_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.zero_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.presentedForm_add_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.presentedForm_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.presentedForm_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.presentedForm_smul_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.distSq_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.distSq_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.addition
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.scalarContinuous
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedAdd
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedNeg
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.closeOfPointwiseObservableEq
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completion_eq_of_pointwise
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedAdd_embedPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_embedPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedAdd_embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedAdd_embedOSQuotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_embedOSQuotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedAdd_assoc
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedAdd_comm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedZero_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedNeg_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedAdd_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear.completedSmul_congr
