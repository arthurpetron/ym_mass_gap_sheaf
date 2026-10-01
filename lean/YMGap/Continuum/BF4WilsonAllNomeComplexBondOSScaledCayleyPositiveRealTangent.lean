/-
# The original graph controls the constructed positive-real Cayley tangent

The mixed original-action remainder has a constructed positive-real bound.
Subtracting twice the imaginary original Euclidean Taylor remainder cancels
its Euclidean increment exactly.  Both computed radii therefore control
the actual Cayley increment plus 2i times real time times the SAME graph
output.  The real scalar retains the supplied numerical QCauchy witness.

This is fixed-nome/fixed-width positive-real first-order control, not a
physical clock, spacing conversion, Wick analytic continuation or mass gap.
Radii belong to supplied original Points, never selected quotient classes.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickPositiveRealLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input output remainder realTaylorCertificate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction signedAction_positiveTime)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickPositiveRealLimit
  (realWickRemainder realWickRadius realWickRadius_positive real_wick_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (normSq_neg normSq_imagScale add_assoc add_comm add_zero neg_add add_neg
    add_right_cancel)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_add completedSmul_mul completedSmul_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "RH" => BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
  (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "RA" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "RN" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "RS" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def qquarter : Q' := Q'.mkPos 1 4 (by decide)
private def qsixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- Real time times the actual original derivative output, retaining the
supplied time Cauchy data in BOTH physical coordinates. -/
def realOutputTerm (p : P) (D : PositiveTime) : H :=
  (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 D.real D.cauchy
      (output hw0 hw1 (ofPoint hw0 hw1 p)).1,
   BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 D.real D.cauchy
      (output hw0 hw1 (ofPoint hw0 hw1 p)).2)

/-- The actual increment with its exact -2i graph phase, before division
by the supplied positive real time. -/
def realError (p : P) (D : PositiveTime) : H :=
  A (diff hw0 hw1 (positiveAction hw0 hw1 D (input hw0 hw1 (ofPoint hw0 hw1 p)))
      (input hw0 hw1 (ofPoint hw0 hw1 p)))
    (imagScale hw0 hw1 2 (realOutputTerm hw0 hw1 p D))

theorem remainder_eq (p : P) (D : PositiveTime) :
    remainder hw0 hw1 D (input hw0 hw1 (ofPoint hw0 hw1 p))
      (output hw0 hw1 (ofPoint hw0 hw1 p)) =
    diff hw0 hw1
      (diff hw0 hw1 (input hw0 hw1 (ofPoint hw0 hw1 p))
        (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1 (timeValue D)
          (input hw0 hw1 (ofPoint hw0 hw1 p))))
      (realOutputTerm hw0 hw1 p D) := rfl

private theorem scale_add (c : Q') (x y : RH) :
    RS c (RA x y) = RA (RS c x) (RS c y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 c _ _

private theorem neg_additive (x y : RH) : RN (RA x y) = RA (RN x) (RN y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate,bondValue_add]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem scale_neg (c : Q') (x : RH) : RS c (RN x) = RN (RS c x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change BF4WilsonAllNomeLinear.completedSmul hw0 hw1 c
      (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1)
        (BF4WilsonAllNomeBondOSTime.bondValue hw0 hw1 x)) =
    BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1)
      (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 c
        (BF4WilsonAllNomeBondOSTime.bondValue hw0 hw1 x))
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv c (-1)) _

private theorem imag_diff (c : Q') (x y : H) :
    imagScale hw0 hw1 c (diff hw0 hw1 x y) =
      diff hw0 hw1 (imagScale hw0 hw1 c x) (imagScale hw0 hw1 c y) := by
  have ha (u v : H) : imagScale hw0 hw1 c (A u v) =
      A (imagScale hw0 hw1 c u) (imagScale hw0 hw1 c v) :=
    Prod.ext ((congrArg RN (scale_add hw0 hw1 c u.2 v.2)).trans
      (neg_additive hw0 hw1 _ _)) (scale_add hw0 hw1 c u.1 v.1)
  have hn (u : H) : imagScale hw0 hw1 c (cneg hw0 hw1 u) =
      cneg hw0 hw1 (imagScale hw0 hw1 c u) :=
    Prod.ext (congrArg RN (scale_neg hw0 hw1 c u.2)) (scale_neg hw0 hw1 c u.1)
  unfold diff
  rw [ha,hn]

private theorem diff_add_cancel (x y : H) : A (diff hw0 hw1 x y) y = x := by
  unfold diff
  rw [add_assoc,neg_add,add_zero]

private theorem cancel_middle (a b c : H) : A (A a c) (diff hw0 hw1 b c) = A a b := by
  unfold diff
  calc
    A (A a c) (A b (cneg hw0 hw1 c)) = A a (A c (A b (cneg hw0 hw1 c))) :=
      add_assoc hw0 hw1 a c _
    _ = A a (A (A c b) (cneg hw0 hw1 c)) := by
      rw [← add_assoc hw0 hw1 c b (cneg hw0 hw1 c)]
    _ = A a (A (A b c) (cneg hw0 hw1 c)) := by rw [add_comm hw0 hw1 c b]
    _ = A a (A b (A c (cneg hw0 hw1 c))) := by rw [add_assoc hw0 hw1 b c _]
    _ = A a b := by rw [add_neg,add_zero]

private theorem difference_middle (a b c : H) :
    diff hw0 hw1 (A a b) (diff hw0 hw1 b c) = A a c := by
  apply add_right_cancel hw0 hw1 _ _ (diff hw0 hw1 b c)
  rw [diff_add_cancel,cancel_middle]

/-- Exact cancellation, not an assumed Euclidean/unitary correspondence. -/
theorem realError_decomposition (p : P) (D : PositiveTime) :
    realError hw0 hw1 p D =
      diff hw0 hw1 (realWickRemainder hw0 hw1 p D)
        (imagScale hw0 hw1 2
          (remainder hw0 hw1 D (input hw0 hw1 (ofPoint hw0 hw1 p))
            (output hw0 hw1 (ofPoint hw0 hw1 p)))) := by
  unfold realError realWickRemainder
  rw [remainder_eq,imag_diff]
  exact (difference_middle hw0 hw1 _ _ _).symm

/-- Both radii are computed from the SAME supplied original graph Point. -/
def realTangentRadius (p : P) (e : Q') (he : (0 : Q') < e) : Q' :=
  Q'.min'
    (realWickRadius hw0 hw1 p (qquarter*e) (Q'.mul_pos (by decide) he))
    (realTaylorCertificate hw0 hw1 p (qsixteenth*e) (Q'.mul_pos (by decide) he)).1

theorem realTangentRadius_positive (p : P) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < realTangentRadius hw0 hw1 p e he := by
  unfold realTangentRadius
  exact CReal.min_pos (realWickRadius_positive hw0 hw1 p _ _)
    (realTaylorCertificate hw0 hw1 p _ _).2.1

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

private theorem error_budget (time : RC) (e : Q') :
    RCadd
      (RCadd (RCmul (RCmul time time) (rat (qquarter*e)))
        (RCmul (RCmul time time) (rat (qquarter*e))))
      (RCadd (RCscale (2*2) (RCmul (RCmul time time) (rat (qsixteenth*e))))
        (RCscale (2*2) (RCmul (RCmul time time) (rat (qsixteenth*e))))) =
    RCmul (RCmul time time) (rat e) := by
  refine Quotient.inductionOn time ?_
  intro T
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => by
    have hp := poly_identity_of_normal_eq
      (.add
        (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 1)))
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 1))))
        (.add
          (.mul (.mul (.const 2) (.const 2))
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 1))))
          (.mul (.mul (.const 2) (.const 2))
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 1))))))
      (.mul (.mul (.var 0) (.var 0))
        (.mul
          (.add (.add (.var 2) (.var 2))
            (.add (.mul (.mul (.const 2) (.const 2)) (.var 3))
              (.mul (.mul (.const 2) (.const 2)) (.var 3))))
          (.var 1)))
      (by decide) (fun | 0 => T.approx n | 1 => e | 2 => qquarter | _ => qsixteenth)
    have hc : Q'.eqv ((qquarter+qquarter)+
        ((2*2)*qsixteenth+(2*2)*qsixteenth)) 1 := by decide
    exact Q'.eqv_trans _ _ _ hp
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e hc) (Q'.one_mul_eqv e)))))

/-- EVERY supplied sufficiently small positive real increment has the actual
SAME-graph error bound. The exact phase is -2i; no physical clock is asserted. -/
theorem real_tangent_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (D : PositiveTime)
    (ht : RCle (realValue (timeValue D)) (rat (realTangentRadius hw0 hw1 p e he))) :
    RCle (N (realError hw0 hw1 p D))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat e)) := by
  have hW := real_wick_bound hw0 hw1 p (qquarter*e) (Q'.mul_pos (by decide) he) D
    (RCle_trans ht (rat_le (Q'.min_le_left' _ _)))
  have hE := (realTaylorCertificate hw0 hw1 p (qsixteenth*e)
    (Q'.mul_pos (by decide) he)).2.2 D
    (RCle_trans ht (rat_le (Q'.min_le_right' _ _)))
  change RCle (N (remainder hw0 hw1 D (input hw0 hw1 (ofPoint hw0 hw1 p))
    (output hw0 hw1 (ofPoint hw0 hw1 p)))) _ at hE
  have hI := RCscale_mono (by decide : (0 : Q') ≤ (2 : Q')*2) hE
  have hsum := normSq_add_le hw0 hw1 (realWickRemainder hw0 hw1 p D)
    (cneg hw0 hw1 (imagScale hw0 hw1 2
      (remainder hw0 hw1 D (input hw0 hw1 (ofPoint hw0 hw1 p))
        (output hw0 hw1 (ofPoint hw0 hw1 p)))))
  rw [normSq_neg,normSq_imagScale] at hsum
  have hbudget := RCadd_le_add (RCadd_le_add hW hW) (RCadd_le_add hI hI)
  rw [error_budget] at hbudget
  rw [realError_decomposition]
  exact RCle_trans hsum hbudget

/-- A source-computed positive radius and the positive-real small-increment law. -/
def realTangentCertificate (p : P) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ D : PositiveTime, RCle (realValue (timeValue D)) (rat r) →
        RCle (N (realError hw0 hw1 p D))
          (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat e))) :=
  ⟨realTangentRadius hw0 hw1 p e he,realTangentRadius_positive hw0 hw1 p e he,
    real_tangent_bound hw0 hw1 p e he⟩

theorem realError_signed_pin (p : P) (D : PositiveTime) :
    realError hw0 hw1 p D =
      A (diff hw0 hw1
        (signedAction hw0 hw1 (SignedRealTimeData.positiveTime (timeValue D))
          (input hw0 hw1 (ofPoint hw0 hw1 p)))
        (input hw0 hw1 (ofPoint hw0 hw1 p)))
        (imagScale hw0 hw1 2 (realOutputTerm hw0 hw1 p D)) := by
  unfold realError
  rw [signedAction_positiveTime,positiveRealAction_pin]

#print axioms realOutputTerm
#print axioms realError
#print axioms remainder_eq
#print axioms realError_decomposition
#print axioms realTangentRadius
#print axioms realTangentRadius_positive
#print axioms real_tangent_bound
#print axioms realTangentCertificate
#print axioms realError_signed_pin

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealTangent
