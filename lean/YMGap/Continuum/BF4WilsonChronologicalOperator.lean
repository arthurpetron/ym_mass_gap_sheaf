/-
# Bounded chronological operators on the SAME Wilson completion

Replace the vacuum leaf of an existing finite program by its input vector.
Reversing composition gives an explicit adjoint for the original completed
pairing. Structural induction computes a squared-norm cap from the signed
coefficients and spins; time advances cost no additional factor.

The existing signed-window compiler is the consumer: its output on the
vacuum is unchanged, and every compiled window receives the computed cap.
This is an operator calculus at the existing fixed nome and lattice spacing,
not a multiplication of arbitrary OS states, an operator independent of a
program presentation, or a continuum observable representation. No canonical
OS identification, changing-spacing estimate, or Clay field is discharged.
-/

import YMGap.Continuum.BF4WilsonWindowRealization
import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.BF4WilsonChronologicalOperator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonWindowRealization
open YMGap.Continuum.BF4WilsonWindowOperatorPins (embedWindow)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression Within)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance (completedDist)
open YMGap.Continuum.CRealSeminormPairingCompletion (pairSequence_converges)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound sumBound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Squared-norm cap; independent of support base and discrete time lengths.
It depends on the actual finite expression, coefficients, and spins. -/
def squaredCap {base : Nat} : Program base → Q'
  | .vacuum => 1
  | .zero => 0
  | .add p q => sumBound (squaredCap p) (squaredCap q)
  | .smul c p => (c*c)*squaredCap p
  | .time _ p => squaredCap p
  | .multiply _ spin p => characterBound spin * squaredCap p

theorem squaredCap_nonnegative {base : Nat} (p : Program base) :
    (0 : Q') ≤ squaredCap p := by
  induction p with
  | vacuum => exact Q'.zero_le_one
  | zero => exact Q'.le_refl' 0
  | add p q hp hq =>
      exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hp hp) (Q'.zero_le_add _ _ hq hq)
  | smul c p hp => exact Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg c) hp
  | time n p hp => exact hp
  | multiply L spin p hp => exact Q'.mul_nonneg _ _ (multiplierCap_nonnegative spin) hp

private theorem budget_pos {base : Nat} (p : Program base) :
    (0 : Q') < squaredCap p + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg 1 (squaredCap p) (squaredCap_nonnegative p))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Explicit squared-distance tolerance, valid also for the zero program. -/
def inputTolerance {base : Nat} (p : Program base) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (squaredCap p + 1) (budget_pos p)

theorem inputTolerance_pos {base : Nat} (p : Program base) {epsilon : Q'}
    (he : (0 : Q') < epsilon) : (0 : Q') < inputTolerance p epsilon :=
  Q'.divPos_pos _ _ _ he

theorem inputTolerance_bound {base : Nat} (p : Program base) {epsilon : Q'}
    (he : (0 : Q') < epsilon) : squaredCap p * inputTolerance p epsilon ≤ epsilon :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_self_of_nonneg (squaredCap p) 1 Q'.zero_le_one)
      (Q'.le_of_lt (inputTolerance_pos p he)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)))

private theorem add_scales (a b : Q') (x : RC) :
    RCadd (RCscale a x) (RCscale b x) = RCscale (a+b) x := by
  refine Quotient.inductionOn x ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.add_mul_eqv a b (X.approx n))))

private theorem scale_zero (x : RC) : RCscale 0 x = RCzero := by
  refine Quotient.inductionOn x ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (X.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "S" => completedSmul hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "M" => completedMultiply hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

/-- A program presentation determines an actual map on the existing carrier.
The vacuum constructor becomes the identity, not a constant map. -/
def act {base : Nat} : Program base → V → V
  | .vacuum, x => x
  | .zero, _ => Z
  | .add p q, x => A (act p x) (act q x)
  | .smul c p, x => S c (act p x)
  | .time n p, x => T n (act p x)
  | .multiply L spin p, x => M L spin (act p x)

/-- Reverse the order of the same symmetric time and character operators. -/
def adjointAct {base : Nat} : Program base → V → V
  | .vacuum, x => x
  | .zero, _ => Z
  | .add p q, x => A (adjointAct p x) (adjointAct q x)
  | .smul c p, x => S c (adjointAct p x)
  | .time n p, x => adjointAct p (T n x)
  | .multiply L spin p, x => adjointAct p (M L spin x)

/-- The existing vacuum-generated meaning is preserved exactly. -/
theorem act_unit {base : Nat} (p : Program base) :
    act hw0 hw1 hsmall hd hs p U = evaluate hw0 hw1 hsmall hd hs p := by
  induction p <;> simp only [act, evaluate, *]

theorem adjoint_balance {base : Nat} (p : Program base) (x y : V) :
    B (act hw0 hw1 hsmall hd hs p x) y =
      B x (adjointAct hw0 hw1 hsmall hd hs p y) := by
  induction p generalizing x y with
  | vacuum => rfl
  | zero => simp only [act, adjointAct, completedInner_zero_left, completedInner_zero_right]
  | add p q hp hq => simp only [act, adjointAct, completedInner_add_left,
      completedInner_add_right, hp, hq]
  | smul c p hp => simp only [act, adjointAct, completedInner_smul_left,
      completedInner_smul_right, hp]
  | time n p hp => simp only [act, adjointAct, completedInner_time_balance, hp]
  | multiply L spin p hp => simp only [act, adjointAct, completedInner_multiplier_balance, hp]

theorem act_add {base : Nat} (p : Program base) (x y : V) :
    act hw0 hw1 hsmall hd hs p (A x y) =
      A (act hw0 hw1 hsmall hd hs p x) (act hw0 hw1 hsmall hd hs p y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [adjoint_balance, completedInner_add_left]

theorem act_smul {base : Nat} (p : Program base) (c : Q') (x : V) :
    act hw0 hw1 hsmall hd hs p (S c x) = S c (act hw0 hw1 hsmall hd hs p x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [adjoint_balance, completedInner_smul_left]

theorem act_sub {base : Nat} (p : Program base) (x y : V) :
    act hw0 hw1 hsmall hd hs p (completedSub hw0 hw1 hsmall hd hs x y) =
      completedSub hw0 hw1 hsmall hd hs
        (act hw0 hw1 hsmall hd hs p x) (act hw0 hw1 hsmall hd hs p y) := by
  simp only [completedSub, completedNeg, act_add, act_smul]

private theorem norm_sum_bound (x y : V) :
    RCle (B (A x y) (A x y))
      (RCadd (RCadd (B x x) (B x x)) (RCadd (B y y) (B y y))) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  let PD := pairingData hw0 hw1 hsmall hd hs
  have hx := pairSequence_converges PD X X
  have hy := pairSequence_converges PD Y Y
  exact leEv_of_convergesTo_le
    (pairSequence_converges PD (addCauchy hw0 hw1 hsmall hd hs X Y)
      (addCauchy hw0 hw1 hsmall hd hs X Y))
    (TrigAddCReal.convergesTo_add (TrigAddCReal.convergesTo_add hx hx)
      (TrigAddCReal.convergesTo_add hy hy))
    (fun n => pairing_sum_bound hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n))

private theorem norm_smul (c : Q') (x : V) :
    B (S c x) (S c x) = RCscale (c*c) (B x x) := by
  rw [completedInner_smul_left, completedInner_smul_right]
  exact RCscale_RCscale c c (B x x)

/-- Every completed input, not only the cyclic vacuum, obeys the computed cap. -/
theorem act_norm_bound {base : Nat} (p : Program base) (x : V) :
    RCle (B (act hw0 hw1 hsmall hd hs p x) (act hw0 hw1 hsmall hd hs p x))
      (RCscale (squaredCap p) (B x x)) := by
  induction p with
  | vacuum => simpa only [act, squaredCap, RCscale_one] using RCle_refl (B x x)
  | zero => simp only [act, squaredCap, completedInner_zero_left, scale_zero]; exact RCle_refl _
  | add p q hp hq =>
      have h := RCle_trans (norm_sum_bound hw0 hw1 hsmall hd hs _ _)
        (RCadd_le_add (RCadd_le_add hp hp) (RCadd_le_add hq hq))
      rw [add_scales, add_scales, add_scales] at h
      exact h
  | smul c p hp =>
      simp only [act, squaredCap, norm_smul]
      simpa only [RCscale_RCscale] using
        RCscale_mono (SumOfSquares.q_mul_self_nonneg c) hp
  | time n p hp => exact RCle_trans (completedInner_time_contraction hw0 hw1 hsmall hd hs n _) hp
  | multiply L spin p hp =>
      have h := RCle_trans (completedInner_multiplier_bound hw0 hw1 hsmall hd hs L spin _)
        (RCscale_mono (multiplierCap_nonnegative spin) hp)
      simpa only [act, squaredCap, ← RCscale_RCscale] using h

/-- The same cap controls differences, with no representative selection. -/
theorem act_distance_bound {base : Nat} (p : Program base) (x y : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (act hw0 hw1 hsmall hd hs p x) (act hw0 hw1 hsmall hd hs p y))
      (RCscale (squaredCap p) (completedDist hw0 hw1 hsmall hd hs x y)) := by
  unfold completedDist
  rw [← act_sub]
  exact act_norm_bound hw0 hw1 hsmall hd hs p _

/-- A quantitative continuity statement with its tolerance returned as data. -/
theorem act_close {base : Nat} (p : Program base) (epsilon : Q')
    (he : (0 : Q') < epsilon) (x y : V)
    (hxy : RCle (completedDist hw0 hw1 hsmall hd hs x y)
      (Quotient.mk crealSetoid (ofQ' (inputTolerance p epsilon)))) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (act hw0 hw1 hsmall hd hs p x) (act hw0 hw1 hsmall hd hs p y))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  RCle_trans (act_distance_bound hw0 hw1 hsmall hd hs p x y)
    (RCle_trans (RCscale_mono (squaredCap_nonnegative p) hxy)
      (leEv_le_ofQ'_of_approx_le (fun _ => inputTolerance_bound p he)))

/-- The existing finite approximation is stable under any supplied program.
The sampled input stage is selected by X.modulus at the computed tolerance;
no quotient representative or common support bound is chosen. -/
theorem act_approximationProgram_bound {base : Nat} (p : Program base)
    (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (act hw0 hw1 hsmall hd hs p
        (evaluate hw0 hw1 hsmall hd hs
          (approximationProgram hw0 hw1 hsmall hd hs X (inputTolerance p epsilon))))
      (act hw0 hw1 hsmall hd hs p
        (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  act_close hw0 hw1 hsmall hd hs p epsilon he _ _
    (approximationProgram_bound hw0 hw1 hsmall hd hs X (inputTolerance p epsilon)
      (inputTolerance_pos p he))

/-- Exact positive square on the ORIGINAL completed form, for arbitrary signed programs. -/
theorem adjoint_square {base : Nat} (p : Program base) (x : V) :
    B x (adjointAct hw0 hw1 hsmall hd hs p (act hw0 hw1 hsmall hd hs p x)) =
      B (act hw0 hw1 hsmall hd hs p x) (act hw0 hw1 hsmall hd hs p x) :=
  (adjoint_balance hw0 hw1 hsmall hd hs p x _).symm

theorem adjoint_square_nonnegative {base : Nat} (p : Program base) (x : V) :
    RCnonneg (B x (adjointAct hw0 hw1 hsmall hd hs p (act hw0 hw1 hsmall hd hs p x))) := by
  rw [adjoint_square]
  exact completedInner_nonnegative hw0 hw1 hsmall hd hs _

/-- Immediate consumer: every original bounded signed window gets a rational
norm cap without a new observable pin or an assumed operator representation. -/
theorem compiledWindow_norm_bound {base : Nat} (hb : 0 < base) (H : Nat)
    (e : WindowExpression base) (he : Within H e) :
    RCle (B (embedWindow hw0 hw1 hsmall hd hs hb H e he)
      (embedWindow hw0 hw1 hsmall hd hs hb H e he))
      (Quotient.mk crealSetoid (ofQ' (squaredCap (compileWindow H e)))) := by
  have h := act_norm_bound hw0 hw1 hsmall hd hs (compileWindow H e) U
  rw [act_unit, compileWindow_pin hw0 hw1 hsmall hd hs hb H e he,
    completedUnit_norm_one] at h
  have hcap : RCscale (squaredCap (compileWindow H e)) (Quotient.mk crealSetoid cone) =
      Quotient.mk crealSetoid (ofQ' (squaredCap (compileWindow H e))) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.mul_one_eqv (squaredCap (compileWindow H e))))
  rw [hcap] at h
  exact h

#print axioms squaredCap
#print axioms squaredCap_nonnegative
#print axioms inputTolerance
#print axioms inputTolerance_pos
#print axioms inputTolerance_bound
#print axioms act
#print axioms adjointAct
#print axioms act_unit
#print axioms adjoint_balance
#print axioms act_add
#print axioms act_smul
#print axioms act_sub
#print axioms act_norm_bound
#print axioms act_distance_bound
#print axioms act_close
#print axioms act_approximationProgram_bound
#print axioms adjoint_square
#print axioms adjoint_square_nonnegative
#print axioms compiledWindow_norm_bound

end YMGap.Continuum.BF4WilsonChronologicalOperator
