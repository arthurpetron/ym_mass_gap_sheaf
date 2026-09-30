/-
Core laws of the actual original-carrier dyadic derivative. The derivative
acts on an input through its original T(1)-image. Its positive symmetric
form is a graph-core fact, not an identification with the regularized
logarithm or a full-carrier Hamiltonian.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeGap
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeCore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (mesh_original)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect time_defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeGap
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root root_sub root_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility (root_square)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeGeometry (completedInner_posdef)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.RCSignedPairBudget (neg_mono)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "U" => unitState hw0 hw1 width
local notation "d" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- Original whole-time translations commute with the derivative's supplied
quotient rows and therefore with their represented limit. -/
theorem derivativeAction_commutes_time (n : Nat) (x : V) :
    A (T n x) = T n (A x) := by
  refine Quotient.inductionOn x ?_
  intro X
  let Y := (timeNonexpansive hw0 hw1 n).mapCauchy X
  change A (Class Y) = T n (A (Class X))
  rw [derivativeAction_pin,derivativeAction_pin]
  unfold representedLimit
  rw [← limit_timeRows]
  apply limit_independent hw0 hw1
  intro k
  rw [quotientRows_pin,timeRows_rowPoint,quotientRows_pin]
  unfold differenceQuotient
  rw [completedTime_smul]
  have hd := time_defect hw0 hw1 0 n k (T 1 (Class X))
  rw [mesh_original hw0 hw1 n,mesh_original hw0 hw1 n] at hd
  rw [hd]
  have ht : T n (T 1 (Class X)) = T 1 (T n (Class X)) := by
    calc
      T n (T 1 (Class X)) = T (n+1) (Class X) :=
        (completedTime_add hw0 hw1 n 1 (Class X)).symm
      _ = T (1+n) (Class X) := by rw [Nat.add_comm]
      _ = T 1 (T n (Class X)) := completedTime_add hw0 hw1 1 n (Class X)
  rw [ht]
  exact rfl

theorem derivativeAction_zero : A Z = Z := by
  have h := derivativeAction_smul hw0 hw1 0 Z
  simpa only [completedSmul_zero] using h

theorem derivativeAction_kernel_zero (x : V) (hx : T 1 x = Z) : A x = Z := by
  have h := derivativeAction_time_congr hw0 hw1 x Z
    (by rw [hx,completedTime_zero_element])
  exact h.trans (derivativeAction_zero hw0 hw1)

theorem derivativeAction_sub (x y : V) :
    A (completedSub hw0 hw1 x y) = completedSub hw0 hw1 (A x) (A y) := by
  unfold completedSub completedNeg
  rw [derivativeAction_add,derivativeAction_smul]

theorem derivativeAction_dist_bound (x y : V) :
    RCle (d (A x) (A y)) (d x y) := by
  unfold completedDist
  rw [← derivativeAction_sub]
  exact derivativeAction_norm_bound hw0 hw1 (completedSub hw0 hw1 x y)

private theorem rc_neg_zero : RCneg RCzero = RCzero :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => (by decide : Q'.eqv (-(0 : Q')) 0)))

private theorem rc_neg_neg (a : RC) : RCneg (RCneg a) = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.neg_neg_eqv (X.approx n)))

private theorem nonneg_and_neg_nonneg_zero {a : RC}
    (ha : RCnonneg a) (hna : RCnonneg (RCneg a)) : a = RCzero := by
  have h := neg_mono hna
  rw [rc_neg_neg,rc_neg_zero] at h
  exact RCle_antisymm h ha

private theorem sub_add_cancel (x y : V) :
    completedAdd hw0 hw1 (completedSub hw0 hw1 x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc,completedNeg_add,completedAdd_zero]

/-- A positive original root cannot have a negative eigenvector. Hence a
vector fixed by its square is fixed by the root itself. -/
private theorem positive_root_fixed_of_square (k : Nat) (u : V)
    (hsquare : root hw0 hw1 k (root hw0 hw1 k u) = u) :
    root hw0 hw1 k u = u := by
  let z := completedSub hw0 hw1 u (root hw0 hw1 k u)
  have hRz : root hw0 hw1 k z =
      completedSub hw0 hw1 (root hw0 hw1 k u) u := by
    dsimp only [z]
    rw [root_sub,hsquare]
  have hpos := root_nonnegative hw0 hw1 k z
  rw [hRz,completedInner_sub_right] at hpos
  have hdiag : B z z = RCsub (B z u) (B z (root hw0 hw1 k u)) := by
    dsimp only [z]
    rw [completedInner_sub_right]
  have hneg : RCnonneg (RCneg (B z z)) := by
    rw [hdiag,← reverse_sub]
    exact hpos
  have hzNorm := nonneg_and_neg_nonneg_zero
    (completedInner_nonnegative hw0 hw1 z) hneg
  have hz : z = Z := (completedInner_posdef hw0 hw1 width z).mp hzNorm
  have h := congrArg (fun v => completedAdd hw0 hw1 v (root hw0 hw1 k u)) hz
  dsimp only [z] at h
  rw [sub_add_cancel,completedZero_add] at h
  exact h.symm

private theorem root_unit_fixed (k : Nat) : root hw0 hw1 k U = U := by
  induction k with
  | zero =>
      rw [BF4WilsonAllNomeNestedRootBasics.root_zero_depth,
        completedUnit_fixed]
  | succ k ih =>
      apply positive_root_fixed_of_square hw0 hw1 (k+1) U
      rw [root_square,ih]

private theorem quotient_unit_zero (k : Nat) :
    differenceQuotient hw0 hw1 k U = Z := by
  unfold differenceQuotient defect
  rw [completedUnit_fixed,root_unit_fixed,completedSub_self]
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [completedInner_smul_left,completedInner_zero_left,RCscale_RCzero]

theorem derivativeAction_unit_zero : A U = Z := by
  let X : (seminorm hw0 hw1 (width := width)).Cauchy :=
    (seminorm hw0 hw1 (width := width)).constant
      (BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit width)
  have hclass : Class X = U := rfl
  rw [←hclass,derivativeAction_pin]
  let Y : (seminorm hw0 hw1 (width := width)).Cauchy :=
    (seminorm hw0 hw1 (width := width)).constant
      (BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.zero width)
  have h := limit_independent hw0 hw1 (quotientRows hw0 hw1 X)
    (constantRows hw0 hw1 Y) (by
      intro n
      rw [quotientRows_pin,constantRows_point,hclass,quotient_unit_zero]
      rfl)
  rw [limit_constantRows] at h
  exact h

theorem core_nonnegative (x : V) : RCnonneg (B (T 1 x) (A x)) :=
  RCle_trans (BF4WilsonAllNomeTimeDefectMoments.defect_nonnegative hw0 hw1 (T 1 x))
    (derivative_form_ge_defect hw0 hw1 x)

theorem core_symmetric (x y : V) :
    B (A x) (T 1 y) = B (T 1 x) (A y) := by
  calc
    B (A x) (T 1 y) = B x (A (T 1 y)) := derivativeAction_symmetric hw0 hw1 x (T 1 y)
    _ = B x (T 1 (A y)) := congrArg (B x) (derivativeAction_commutes_time hw0 hw1 1 y)
    _ = B (T 1 x) (A y) := (completedInner_time_balance hw0 hw1 1 x (A y)).symm

#print axioms derivativeAction_commutes_time
#print axioms derivativeAction_zero
#print axioms derivativeAction_kernel_zero
#print axioms derivativeAction_sub
#print axioms derivativeAction_dist_bound
#print axioms derivativeAction_unit_zero
#print axioms core_nonnegative
#print axioms core_symmetric

end YMGap.Continuum.BF4WilsonAllNomeDerivativeCore
