/-
# Time-zero observables on the SAME all-nome Wilson completion

The original reflected squared-distance bound constructs multiplication by
each supplied spatial Wilson-loop character on the existing literal-width
Cauchy quotient. Its modulus is explicit. Reflection fixes the time-zero
insertion, so the original pairing balance descends to the completion and
proves rational and constructive-real linearity.

The squared-norm cap depends only on the spin, not nome or width. This does
not identify carriers at different widths or spacings, construct a continuum
observable net, or improve the transfer-gap rate. No small-nome spatial-union
form is substituted for the all-nome form; only its parameter-free rational
tolerance arithmetic is reused.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeZeroBound
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier

namespace YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
  (multiplierCap_nonnegative multiplierTolerance multiplierTolerance_pos
    multiplierTolerance_bound)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroBound
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner pairSequence_converges)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1

/-- The explicit tolerance is epsilon/(characterBound spin+1), with no
root extraction or witness choice. The contraction is in the original OS norm. -/
def multiplierContinuous (L : SourceLoop width) (spin : Nat) : (D).ModulusContinuous where
  toFun := multiply L spin
  tolerance := multiplierTolerance spin
  tolerance_pos := fun _ => multiplierTolerance_pos spin
  contraction := by
    intro epsilon he x y h
    have hc : leEv czero (ofQ' (characterBound spin)) :=
      leEv_ofQ'_of_approx_ge (fun _ => multiplierCap_nonnegative spin)
    exact leEv_trans (distSq_multiplier_bound hw0 hw1 L spin x y)
      (leEv_trans (leEv_mul_nonneg_left hc h)
        (leEv_le_ofQ'_of_approx_le (fun _ => multiplierTolerance_bound spin he)))

def multiplyCauchy (L : SourceLoop width) (spin : Nat) (X : (D).Cauchy) : (D).Cauchy :=
  (multiplierContinuous hw0 hw1 L spin).mapCauchy X

theorem multiplyCauchy_seq (L : SourceLoop width) (spin : Nat) (X : (D).Cauchy) (n : Nat) :
    (multiplyCauchy hw0 hw1 L spin X).seq n = multiply L spin (X.seq n) := rfl

theorem multiplyCauchy_modulus (L : SourceLoop width) (spin : Nat)
    (X : (D).Cauchy) (epsilon : Q') :
    (multiplyCauchy hw0 hw1 L spin X).modulus epsilon =
      X.modulus (multiplierTolerance spin epsilon) := rfl

/-- Actual multiplication on the already constructed literal-width completion. -/
def completedMultiply (L : SourceLoop width) (spin : Nat) : V → V :=
  (multiplierContinuous hw0 hw1 L spin).completionMap

local notation "M" => completedMultiply hw0 hw1

theorem completedMultiply_mk (L : SourceLoop width) (spin : Nat) (X : (D).Cauchy) :
    M L spin (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (multiplyCauchy hw0 hw1 L spin X) := rfl

theorem completedMultiply_embed (L : SourceLoop width) (spin : Nat)
    (x : IntrinsicExpression width) :
    M L spin (embed hw0 hw1 x) = embed hw0 hw1 (multiply L spin x) := rfl

theorem representativeDist_multiply_bound (L : SourceLoop width) (spin : Nat)
    (X Y : (D).Cauchy) :
    leEv (representativeDist hw0 hw1
      (multiplyCauchy hw0 hw1 L spin X) (multiplyCauchy hw0 hw1 L spin Y))
      (mul (ofQ' (characterBound spin)) (representativeDist hw0 hw1 X Y)) :=
  leEv_of_convergesTo_le
    (representativeDist_converges hw0 hw1
      (multiplyCauchy hw0 hw1 L spin X) (multiplyCauchy hw0 hw1 L spin Y))
    (convergesTo_const_mul (ofQ' (characterBound spin))
      (representativeDist_converges hw0 hw1 X Y))
    (fun n => distSq_multiplier_bound hw0 hw1 L spin (X.seq n) (Y.seq n))

/-- The same spin-only cap holds for every pair of completed states. -/
theorem completedDist_multiply_bound (L : SourceLoop width) (spin : Nat) (x y : V) :
    RCle (completedDist hw0 hw1 (M L spin x) (M L spin y))
      (RCmul (Quotient.mk crealSetoid (ofQ' (characterBound spin)))
        (completedDist hw0 hw1 x y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeDist_multiply_bound hw0 hw1 L spin

theorem representativeInner_multiplier_balance (L : SourceLoop width) (spin : Nat)
    (X Y : (D).Cauchy) :
    Equiv (representativeInner PD (multiplyCauchy hw0 hw1 L spin X) Y)
      (representativeInner PD X (multiplyCauchy hw0 hw1 L spin Y)) :=
  Equiv_of_limit_of_equal
    (fun n => intrinsicForm_multiplier_balance hw0 hw1 L spin (X.seq n) (Y.seq n))
    (pairSequence_converges PD (multiplyCauchy hw0 hw1 L spin X) Y)
    (pairSequence_converges PD X (multiplyCauchy hw0 hw1 L spin Y))

/-- Symmetry in the SAME all-nome completed reflected inner product. -/
theorem completedInner_multiplier_balance (L : SourceLoop width) (spin : Nat)
    (x y : V) : B (M L spin x) y = B x (M L spin y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound
    (representativeInner_multiplier_balance hw0 hw1 L spin X Y)

theorem completedMultiply_zero (L : SourceLoop width) (spin : Nat) :
    M L spin (completedZero hw0 hw1 width) = completedZero hw0 hw1 width := by
  apply completed_eq_of_pairings hw0 hw1
  intro test
  rw [completedInner_multiplier_balance, completedInner_zero_left, completedInner_zero_left]

theorem completedMultiply_add (L : SourceLoop width) (spin : Nat) (x y : V) :
    M L spin (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (M L spin x) (M L spin y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro test
  rw [completedInner_multiplier_balance, completedInner_add_left, completedInner_add_left,
    completedInner_multiplier_balance, completedInner_multiplier_balance]

theorem completedMultiply_smul (L : SourceLoop width) (spin : Nat) (c : Q') (x : V) :
    M L spin (completedSmul hw0 hw1 c x) = completedSmul hw0 hw1 c (M L spin x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro test
  rw [completedInner_multiplier_balance, completedInner_smul_left,
    completedInner_smul_left, completedInner_multiplier_balance]

/-- Real linearity retains the supplied scalar's explicit rational Cauchy modulus. -/
theorem completedMultiply_realSmul (L : SourceLoop width) (spin : Nat)
    (s : CReal) (cs : QCauchy s.approx) (x : V) :
    M L spin (completedRealSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs (M L spin x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro test
  rw [completedInner_multiplier_balance, completedInner_realSmul_left,
    completedInner_realSmul_left, completedInner_multiplier_balance]

/-- Original reflected squared-norm bound for every completed state.
The scalar cap is independent of w, width and the state. -/
theorem completedInner_multiplier_bound (L : SourceLoop width) (spin : Nat) (x : V) :
    RCle (B (M L spin x) (M L spin x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (characterBound spin))) (B x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact leEv_of_convergesTo_le
    (pairSequence_converges PD (multiplyCauchy hw0 hw1 L spin X)
      (multiplyCauchy hw0 hw1 L spin X))
    (convergesTo_const_mul (ofQ' (characterBound spin)) (pairSequence_converges PD X X))
    (fun n => intrinsicForm_multiplier_bound hw0 hw1 L spin (X.seq n))

#print axioms multiplierContinuous
#print axioms multiplyCauchy
#print axioms multiplyCauchy_seq
#print axioms multiplyCauchy_modulus
#print axioms completedMultiply
#print axioms completedMultiply_mk
#print axioms completedMultiply_embed
#print axioms representativeDist_multiply_bound
#print axioms completedDist_multiply_bound
#print axioms representativeInner_multiplier_balance
#print axioms completedInner_multiplier_balance
#print axioms completedMultiply_zero
#print axioms completedMultiply_add
#print axioms completedMultiply_smul
#print axioms completedMultiply_realSmul
#print axioms completedInner_multiplier_bound

end YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
