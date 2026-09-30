/-
Finite polynomial algebra for the actual completed Wilson time defect.
All identities are on the same all-nome completion; no spectral calculus is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial

namespace YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "DP" => defectPower hw0 hw1
local notation "PA" => actionFrom hw0 hw1

private theorem add_interchange (a b c d : V) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  rw [completedAdd_assoc, ← completedAdd_assoc hw0 hw1 b c d,
    completedAdd_comm hw0 hw1 b c, completedAdd_assoc hw0 hw1 c b d,
    ← completedAdd_assoc]

private theorem smul_zero (c : Q') : S c Z = Z := by
  calc
    S c Z = S c (S 0 Z) := congrArg (S c) (completedSmul_zero hw0 hw1 Z).symm
    _ = S (c*0) Z := completedSmul_mul hw0 hw1 c 0 Z
    _ = S 0 Z := completedSmul_congr hw0 hw1 (Q'.mul_zero_eqv c) Z
    _ = Z := completedSmul_zero hw0 hw1 Z

theorem defect_additive (x y : V) :
    defect hw0 hw1 (A x y) = A (defect hw0 hw1 x) (defect hw0 hw1 y) := by
  unfold defect completedSub completedNeg
  rw [completedTime_additive, completedSmul_add]
  exact add_interchange hw0 hw1 x y
    (S (-1) (T 1 x)) (S (-1) (T 1 y))

theorem defect_smul (c : Q') (x : V) :
    defect hw0 hw1 (S c x) = S c (defect hw0 hw1 x) := by
  unfold defect completedSub completedNeg
  rw [completedTime_smul, completedSmul_add,
    completedSmul_mul, completedSmul_mul]
  exact congrArg (A (S c x))
    (completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv (-1) c) (T 1 x))

theorem defect_zero : defect hw0 hw1 Z = Z := by
  unfold defect completedSub completedNeg
  rw [completedTime_zero_element, smul_zero, completedAdd_zero]

theorem defectPower_additive (n : Nat) (x y : V) :
    DP n (A x y) = A (DP n x) (DP n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change defect hw0 hw1 (DP n (A x y)) = _
      rw [ih, defect_additive]
      rfl

theorem defectPower_smul (n : Nat) (c : Q') (x : V) :
    DP n (S c x) = S c (DP n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change defect hw0 hw1 (DP n (S c x)) = _
      rw [ih, defect_smul]
      rfl

theorem defectPower_zero (n : Nat) : DP n Z = Z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change defect hw0 hw1 (DP n Z) = Z
      rw [ih, defect_zero]

/-- Applying a defect power shifts every coefficient's defect index. -/
theorem defectPower_actionFrom (p : Poly) (i j : Nat) (x : V) :
    DP i (PA p j x) = PA p (i+j) x := by
  induction p generalizing j with
  | nil =>
      change DP i Z = Z
      exact defectPower_zero hw0 hw1 i
  | cons a p ih =>
      change DP i (A (S a (DP j x)) (PA p (j+1) x)) =
        A (S a (DP (i+j) x)) (PA p (i+j+1) x)
      rw [defectPower_additive, defectPower_smul,
        ← defectPower_add, ih]
      exact congrArg (A (S a (DP (i+j) x)))
        (congrArg (fun k => PA p k x) (show i+(j+1) = i+j+1 by omega))

theorem actionFrom_defectPower (p : Poly) (i j : Nat) (x : V) :
    PA p i (DP j x) = PA p (i+j) x := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
      change A (S a (DP i (DP j x))) (PA p (i+1) (DP j x)) =
        A (S a (DP (i+j) x)) (PA p (i+j+1) x)
      rw [← defectPower_add, ih]
      exact congrArg (A (S a (DP (i+j) x)))
        (congrArg (fun k => PA p k x) (show i+1+j = i+j+1 by omega))

theorem actionFrom_additive (p : Poly) (i : Nat) (x y : V) :
    PA p i (A x y) = A (PA p i x) (PA p i y) := by
  induction p generalizing i with
  | nil => exact (completedZero_add hw0 hw1 Z).symm
  | cons a p ih =>
      change A (S a (DP i (A x y))) (PA p (i+1) (A x y)) = _
      rw [defectPower_additive, completedSmul_add, ih, add_interchange]
      rfl

theorem actionFrom_smul (p : Poly) (i : Nat) (c : Q') (x : V) :
    PA p i (S c x) = S c (PA p i x) := by
  induction p generalizing i with
  | nil => exact (smul_zero hw0 hw1 c).symm
  | cons a p ih =>
      change A (S a (DP i (S c x))) (PA p (i+1) (S c x)) =
        S c (A (S a (DP i x)) (PA p (i+1) x))
      rw [defectPower_smul, ih, completedSmul_add,
        completedSmul_mul, completedSmul_mul]
      exact congrArg (fun z => A z (S c (PA p (i+1) x)))
        (completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv a c) (DP i x))

theorem actionFrom_zero (p : Poly) (i : Nat) : PA p i Z = Z := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
      change A (S a (DP i Z)) (PA p (i+1) Z) = Z
      rw [defectPower_zero, smul_zero, ih, completedZero_add]

theorem actionFrom_pmul (p q : Poly) (i : Nat) (x : V) :
    PA (pmul p q) i x = PA p i (action hw0 hw1 q x) := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
      change PA (padd (pscale a q) (0 :: pmul p q)) i x = _
      rw [actionFrom_padd, actionFrom_pscale]
      change A (S a (PA q i x))
        (A (S 0 (DP i x)) (PA (pmul p q) (i+1) x)) = _
      rw [completedSmul_zero, completedZero_add, ih]
      change A (S a (PA q i x)) (PA p (i+1) (action hw0 hw1 q x)) =
        A (S a (DP i (action hw0 hw1 q x)))
          (PA p (i+1) (action hw0 hw1 q x))
      exact congrArg (fun z => A (S a z) (PA p (i+1) (action hw0 hw1 q x)))
        (by
          simpa only [action, Nat.add_zero] using
            (defectPower_actionFrom hw0 hw1 q i 0 x).symm)

theorem action_pmul (p q : Poly) (x : V) :
    action hw0 hw1 (pmul p q) x =
      action hw0 hw1 p (action hw0 hw1 q x) :=
  actionFrom_pmul hw0 hw1 p q 0 x

theorem action_add (p q : Poly) (x : V) :
    action hw0 hw1 (padd p q) x =
      A (action hw0 hw1 p x) (action hw0 hw1 q x) :=
  actionFrom_padd hw0 hw1 p q 0 x

theorem action_smul (c : Q') (p : Poly) (x : V) :
    action hw0 hw1 (pscale c p) x = S c (action hw0 hw1 p x) :=
  actionFrom_pscale hw0 hw1 c p 0 x

theorem action_sub (p q : Poly) (x : V) :
    action hw0 hw1 (psub p q) x =
      completedSub hw0 hw1 (action hw0 hw1 p x) (action hw0 hw1 q x) :=
  action_psub hw0 hw1 p q x

theorem actionFrom_symmetric (p : Poly) (i : Nat) (x y : V) :
    B (PA p i x) y = B x (PA p i y) := by
  induction p generalizing i with
  | nil =>
      change B Z y = B x Z
      rw [completedInner_zero_left, completedInner_zero_right]
  | cons a p ih =>
      change B (A (S a (DP i x)) (PA p (i+1) x)) y =
        B x (A (S a (DP i y)) (PA p (i+1) y))
      rw [completedInner_add_left, completedInner_add_right,
        completedInner_smul_left, completedInner_smul_right,
        defectPower_symmetric, ih]

theorem action_symmetric (p : Poly) (x y : V) :
    B (action hw0 hw1 p x) y = B x (action hw0 hw1 p y) :=
  actionFrom_symmetric hw0 hw1 p 0 x y

theorem actionFrom_commutes_time (p : Poly) (i n : Nat) (x : V) :
    T n (PA p i x) = PA p i (T n x) := by
  induction p generalizing i with
  | nil => exact completedTime_zero_element hw0 hw1 n
  | cons a p ih =>
      change T n (A (S a (DP i x)) (PA p (i+1) x)) = _
      rw [completedTime_additive, completedTime_smul,
        time_defectPower, ih]
      rfl

theorem action_commutes_time (p : Poly) (n : Nat) (x : V) :
    T n (action hw0 hw1 p x) = action hw0 hw1 p (T n x) :=
  actionFrom_commutes_time hw0 hw1 p 0 n x

#print axioms defectPower_actionFrom
#print axioms actionFrom_pmul
#print axioms action_pmul
#print axioms action_add
#print axioms action_smul
#print axioms action_sub
#print axioms action_symmetric
#print axioms action_commutes_time

end YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
