/-
# Computed derivative tolerances for the ORIGINAL buffered Wilson words

The actual bounded word operators supply their own spin-only squared-norm
cap. Dividing epsilon by cap+1 pays the matrix-element error with a computed
positive rational tolerance, without inverting a state norm or selecting a
quotient representative. All pairings and signed-time quotients belong to
the same original bond completion. This is fixed-carrier numerical-time
differentiation, not physical calibration or continuum QFT closure.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMatrixTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSeparatedWords
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyWilsonWordTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords (Word)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSeparatedWords
  (wordAct letter_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion inner)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
  (characterBound character_squareBound SquareBound)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyOrbitTangent
  (forwardQuotientAt backwardQuotientAt ofPointOrbitTangent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedGraph
  (signedGraphMap)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData (slope)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMatrixTangent
  (valueSub valueNormSq inner_diff_right forward_matrix_tangent_error_le
    backward_matrix_tangent_error_le)
open YMGap.Continuum.SignedRealTimeData (SignedTimeValue)

variable {width : Nat}

/-- Computed solely from the supplied ordered representation labels. -/
def wordCap : Word width → Q'
  | [] => 1
  | a :: rest => characterBound a.2 * wordCap rest

theorem wordCap_nonnegative (word : Word width) : (0 : Q') ≤ wordCap word := by
  induction word with
  | nil => exact Q'.zero_le_one
  | cons a rest ih =>
      exact Q'.mul_nonneg _ _ (character_squareBound (SquareBound.one 0) a.2).nonnegative ih

private theorem wordBudget_positive (word : Word width) :
    (0 : Q') < wordCap word + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg 1 _ (wordCap_nonnegative word))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- No state norm is inverted; the positive denominator is the computed cap+1. -/
def wordTolerance (word : Word width) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (wordCap word + 1) (wordBudget_positive word)

theorem wordTolerance_positive (word : Word width) {epsilon : Q'}
    (he : (0 : Q') < epsilon) : (0 : Q') < wordTolerance word epsilon :=
  Q'.divPos_pos _ _ _ he

theorem wordTolerance_payment (word : Word width) {epsilon : Q'}
    (he : (0 : Q') < epsilon) : wordCap word * wordTolerance word epsilon ≤ epsilon :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_self_of_nonneg (wordCap word) 1 Q'.zero_le_one)
      (Q'.le_of_lt (wordTolerance_positive word he)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "N" => normSq hw0 hw1
local notation "W" => wordAct hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The actual complete word, not independently supplied operator data. -/
theorem word_norm_bound (word : Word width) (x : H) :
    RCle (N (W word x)) (RCscale (wordCap word) (N x)) := by
  induction word with
  | nil =>
      change RCle (N x) (RCscale 1 (N x))
      rw [RCscale_one]
      exact RCle_refl _
  | cons a rest ih =>
      have hletter := letter_norm_bound hw0 hw1 a.1 a.2 (W rest x)
      have hcap := (character_squareBound (SquareBound.one 0) a.2).nonnegative
      have h := RCle_trans hletter (RCscale_mono hcap ih)
      rw [RCscale_RCscale] at h
      exact h

private theorem scale_rat (a b : Q') : RCscale a (rat b) = rat (a*b) :=
  Quotient.sound (CReal.Equiv.symm (CRealAlg.ofQ'_mul a b))

/-- Unit inputs give a spin-only cap for every original finite word. -/
theorem word_norm_unit_bound (word : Word width) (x : H) (hx : RCle (N x) (rat 1)) :
    RCle (N (W word x)) (rat (wordCap word)) := by
  have h := RCle_trans (word_norm_bound hw0 hw1 word x)
    (RCscale_mono (wordCap_nonnegative word) hx)
  rw [scale_rat] at h
  have hp : rat (wordCap word * 1) = rat (wordCap word) :=
    Quotient.sound
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv _))
  rw [hp] at h
  exact h

/-- The original Point modulus, evaluated at the computed word tolerance. -/
def wordMatrixRadius (p : P) (word : Word width) (epsilon : Q')
    (he : (0 : Q') < epsilon) : Q' :=
  (ofPointOrbitTangent hw0 hw1 p).radius (wordTolerance word epsilon)
    (wordTolerance_positive word he)

theorem wordMatrixRadius_positive (p : P) (word : Word width) (epsilon : Q')
    (he : (0 : Q') < epsilon) : (0 : Q') < wordMatrixRadius hw0 hw1 p word epsilon he :=
  (ofPointOrbitTangent hw0 hw1 p).positive _ _

private theorem word_weight_payment (word : Word width) (x : H)
    (hx : RCle (N x) (rat 1)) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    RCle (RCmul (N (W word x)) (rat (wordTolerance word epsilon))) (rat epsilon) := by
  rw [RCmul_comm (N (W word x)) (rat (wordTolerance word epsilon))]
  change RCle (RCscale (wordTolerance word epsilon) (N (W word x))) (rat epsilon)
  have h := RCscale_mono (Q'.le_of_lt (wordTolerance_positive word he))
    (word_norm_unit_bound hw0 hw1 word x hx)
  rw [scale_rat] at h
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (wordTolerance_payment word he)))

/-- BOTH original matrix-element quotients, tested by the actual buffered
Wilson word, have squared modulus error at most epsilon with this computed
radius. The Type-level pair retains both checked bounds; the radius is
independent of the unit input and the signed numerical base. -/
def word_matrix_tangent_bound (p : P) (word : Word width) (x : H)
    (hx : RCle (N x) (rat 1)) (epsilon : Q') (he : (0 : Q') < epsilon)
    (s : SignedTimeValue) (D : PositiveTime)
    (htime : RCle (realValue (timeValue D))
      (rat (wordMatrixRadius hw0 hw1 p word epsilon he))) :
    (RCle (valueNormSq (valueSub
      (inner hw0 hw1 (W word x)
        (forwardQuotientAt hw0 hw1 s D (input hw0 hw1 (ofPoint hw0 hw1 p))))
      (inner hw0 hw1 (W word x)
        (slope hw0 hw1 (output hw0 hw1
          (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p))))))) (rat epsilon)) ×'
    (RCle (valueNormSq (valueSub
      (inner hw0 hw1 (W word x)
        (backwardQuotientAt hw0 hw1 s D (input hw0 hw1 (ofPoint hw0 hw1 p))))
      (inner hw0 hw1 (W word x)
        (slope hw0 hw1 (output hw0 hw1
          (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p))))))) (rat epsilon)) := by
  have hp := word_weight_payment hw0 hw1 word x hx he
  constructor
  · have h := forward_matrix_tangent_error_le hw0 hw1 p (W word x)
      (wordTolerance word epsilon) (wordTolerance_positive word he) s D htime
    rw [inner_diff_right] at h
    exact RCle_trans h hp
  · have h := backward_matrix_tangent_error_le hw0 hw1 p (W word x)
      (wordTolerance word epsilon) (wordTolerance_positive word he) s D htime
    rw [inner_diff_right] at h
    exact RCle_trans h hp

#print axioms wordCap
#print axioms wordCap_nonnegative
#print axioms wordTolerance
#print axioms wordTolerance_positive
#print axioms wordTolerance_payment
#print axioms word_norm_bound
#print axioms word_norm_unit_bound
#print axioms wordMatrixRadius
#print axioms wordMatrixRadius_positive
#print axioms word_matrix_tangent_bound

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyWilsonWordTangent
