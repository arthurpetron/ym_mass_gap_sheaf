/-
# Positive bounded regularized series on the SAME Wilson completion

The already constructed series limit is symmetric and has squared-norm
bound one. Pairing continuity passes the finite estimates to its actual
represented limit. Symmetry and positive definiteness then give linearity,
including constructive-real scalars with their supplied moduli. No choice
of representatives or spectral theorem enters.

This is the map sum_{k>=1} (I-T)^k T/k, not an identified scalar logarithm,
an unbounded Hamiltonian, or a continuous physical-time generator. Its
annihilation of the actual boundary kernel is unchanged. No useful signed
scaling estimate or continuum mass bound follows from this norm cap.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogSeries
import YMGap.Continuum.BF4WilsonAllNomeLogPartialAlgebra
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomeLogOperator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeLogPartial
open YMGap.Continuum.BF4WilsonAllNomeLogPartialAlgebra
open YMGap.Continuum.BF4WilsonAllNomeLogSeries
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "F" => regularizedLog hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Rq" => fun q : Q' => Quotient.mk crealSetoid (ofQ' q)

private theorem rc_two_halves (a : RC) (epsilon : Q') :
    RCadd (RCadd a (Rq (HalfPow.half*epsilon))) (Rq (HalfPow.half*epsilon)) =
      RCadd a (Rq epsilon) := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))))

private theorem pairing_limits_le (R S U W : RepresentedCauchy hw0 hw1 (width := width))
    (h : ∀ n, B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n) =
      B (rowPoint hw0 hw1 U n) (rowPoint hw0 hw1 W n)) :
    RCle (B (limit hw0 hw1 R) (limit hw0 hw1 S))
      (B (limit hw0 hw1 U) (limit hw0 hw1 W)) := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let d := HalfPow.half * epsilon
  have hd : (0 : Q') < d := ExpNeg.half_mul_pos epsilon he
  let n := max (pairingModulus hw0 hw1 R S d) (pairingModulus hw0 hw1 U W d)
  have hRS := (row_pairing_bound hw0 hw1 R S d hd n (Nat.le_max_left _ _)).2
  have hUW := (row_pairing_bound hw0 hw1 U W d hd n (Nat.le_max_right _ _)).1
  rw [h n] at hRS
  have hh := RCle_trans hRS (RCadd_le_add hUW (RCle_refl (Rq d)))
  rwa [rc_two_halves] at hh

/-- Pointwise equality of represented pairings survives the SAME computed limits. -/
theorem pairing_limits_eq (R S U W : RepresentedCauchy hw0 hw1 (width := width))
    (h : ∀ n, B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n) =
      B (rowPoint hw0 hw1 U n) (rowPoint hw0 hw1 W n)) :
    B (limit hw0 hw1 R) (limit hw0 hw1 S) =
      B (limit hw0 hw1 U) (limit hw0 hw1 W) :=
  RCle_antisymm (pairing_limits_le hw0 hw1 R S U W h)
    (pairing_limits_le hw0 hw1 U W R S (fun n => (h n).symm))

/-- Symmetry of the actual constructed limit, not a newly assumed operator. -/
theorem regularizedLog_symmetric (x y : V) : B (F x) y = B x (F y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1 (logRows hw0 hw1 X) (constantRows hw0 hw1 Y)
    (constantRows hw0 hw1 X) (logRows hw0 hw1 Y) (fun n => by
      rw [logRows_point, constantRows_point, constantRows_point, logRows_point]
      exact logPartial_symmetric hw0 hw1 n (Class X) (Class Y))
  rw [limit_constantRows, limit_constantRows] at h
  exact h

private theorem scale_one (a : RC) : RCscale 1 a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.one_mul_eqv (A.approx n)))

/-- The original squared norm bounds the LIMIT, uniformly in nome and width. -/
theorem regularizedLog_norm_bound (x : V) : RCle (B (F x) (F x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  change RCle (B (limit hw0 hw1 (logRows hw0 hw1 X))
    (limit hw0 hw1 (logRows hw0 hw1 X))) _
  apply rowLimit_norm_bound hw0 hw1
  intro n
  rw [logRows_point]
  have h := logTail_norm_bound hw0 hw1 (Class X) 0 n
  rw [RCSignedPairBudget.scale_congr
    (by decide : Q'.eqv (Q'.invSucc 0 * Q'.invSucc 0) 1), scale_one] at h
  exact h

/-- Positivity of the regularized form follows from positive mixed moments. -/
theorem regularizedLog_nonnegative (x : V) : RCnonneg (B x (F x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let R := constantRows hw0 hw1 X
  let S := logRows hw0 hw1 X
  let n := pairingModulus hw0 hw1 R S epsilon
  have h := (row_pairing_bound hw0 hw1 R S epsilon he n (Nat.le_refl n)).1
  change RCle (B (rowPoint hw0 hw1 (constantRows hw0 hw1 X) n)
    (rowPoint hw0 hw1 (logRows hw0 hw1 X) n))
      (RCadd (B (limit hw0 hw1 (constantRows hw0 hw1 X))
        (limit hw0 hw1 (logRows hw0 hw1 X))) (Rq epsilon)) at h
  rw [constantRows_point, logRows_point, limit_constantRows] at h
  have hp := logPartial_nonnegative hw0 hw1 n (Class X)
  rw [completedInner_symm hw0 hw1 (logPartial hw0 hw1 n (Class X)) (Class X)] at hp
  exact RCle_trans hp h

/-- Symmetry already forces additivity through the actual definite pairing. -/
theorem regularizedLog_add (x y : V) :
    F (completedAdd hw0 hw1 x y) = completedAdd hw0 hw1 (F x) (F y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [regularizedLog_symmetric, completedInner_add_left, completedInner_add_left,
    regularizedLog_symmetric, regularizedLog_symmetric]

theorem regularizedLog_smul (c : Q') (x : V) :
    F (completedSmul hw0 hw1 c x) = completedSmul hw0 hw1 c (F x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [regularizedLog_symmetric, completedInner_smul_left, completedInner_smul_left,
    regularizedLog_symmetric]

/-- Full supplied-modulus constructive-real homogeneity on the existing carrier. -/
theorem regularizedLog_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    F (completedRealSmul hw0 hw1 s cs x) = completedRealSmul hw0 hw1 s cs (F x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [regularizedLog_symmetric, completedInner_realSmul_left,
    completedInner_realSmul_left, regularizedLog_symmetric]

theorem regularizedLog_sub (x y : V) :
    F (completedSub hw0 hw1 x y) = completedSub hw0 hw1 (F x) (F y) := by
  unfold completedSub completedNeg
  rw [regularizedLog_add, regularizedLog_smul]

/-- Nonexpansiveness gives the identity tolerance on actual squared distances. -/
theorem regularizedLog_dist_bound (x y : V) :
    RCle (completedDist hw0 hw1 (F x) (F y)) (completedDist hw0 hw1 x y) := by
  unfold completedDist
  rw [← regularizedLog_sub]
  exact regularizedLog_norm_bound hw0 hw1 (completedSub hw0 hw1 x y)

/-- Every output is orthogonal to the original normalized unit. -/
theorem regularizedLog_orthogonal (x : V) :
    B (unitState hw0 hw1 width) (F x) = RCzero := by
  rw [← regularizedLog_symmetric, regularizedLog_unit_zero, completedInner_zero_left]

/-- The SAME operator as a map into the pre-existing vacuum complement. -/
def regularizedLogVacuum (x : V) : VacuumComplement hw0 hw1 (width := width) :=
  ⟨F x, regularizedLog_orthogonal hw0 hw1 x⟩

#print axioms pairing_limits_eq
#print axioms regularizedLog_symmetric
#print axioms regularizedLog_norm_bound
#print axioms regularizedLog_nonnegative
#print axioms regularizedLog_add
#print axioms regularizedLog_smul
#print axioms regularizedLog_realSmul
#print axioms regularizedLog_sub
#print axioms regularizedLog_dist_bound
#print axioms regularizedLog_orthogonal
#print axioms regularizedLogVacuum

end YMGap.Continuum.BF4WilsonAllNomeLogOperator
