/-
# Linear time combinations on the literal all-nome Wilson completion

The rational operations constructed on the existing completion are bilinear
for its actual pairing and commute with its actual completed time semigroup.
Finite signed time filters therefore retain every cross term of the SAME
completed correlator.  This is fixed-nome, fixed-width algebra and adds no
scaling or continuum input.
-/

import YMGap.Continuum.BF4WilsonAllNomeLinear
import YMGap.Continuum.BF4WilsonAllNomeCompletedTime
import YMGap.Continuum.BF4WilsonAllNomeCompletedGap

namespace YMGap.Continuum.BF4WilsonAllNomeBilinearTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (smul zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeForm
  (intrinsicForm_time_balance)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm
  (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
  (completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate)
open YMGap.Continuum.BF4WilsonAllNomeLinear

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "U" => unitState hw0 hw1 width
local notation "F" => intrinsicForm hw0 hw1
local notation "R" => CRealSeminormPairingCompletion.representativeInner PD

theorem representativeInner_add_left (X Y Z' : (D).Cauchy) :
    Equiv (R ((addition hw0 hw1).mapCauchy X Y) Z')
      (add (R X Z') (R Y Z')) :=
  Equiv_of_limit_of_equal
    (fun n => intrinsicForm_sum_left hw0 hw1 (X.seq n) (Y.seq n) (Z'.seq n))
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      ((addition hw0 hw1).mapCauchy X Y) Z')
    (TrigAddCReal.convergesTo_add
      (CRealSeminormPairingCompletion.pairSequence_converges PD X Z')
      (CRealSeminormPairingCompletion.pairSequence_converges PD Y Z'))

theorem representativeInner_smul_left (c : Q') (X Y : (D).Cauchy) :
    Equiv (R ((scalarContinuous hw0 hw1 c).mapCauchy X) Y)
      (mul (ofQ' c) (R X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => intrinsicForm_smul_left hw0 hw1 c (X.seq n) (Y.seq n))
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      ((scalarContinuous hw0 hw1 c).mapCauchy X) Y)
    (convergesTo_const_mul (ofQ' c)
      (CRealSeminormPairingCompletion.pairSequence_converges PD X Y))

theorem completedInner_add_left (x y z : V) :
    B (A x y) z = RCadd (B x z) (B y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact fun X Y Z' => Quotient.sound
    (representativeInner_add_left hw0 hw1 X Y Z')

theorem completedInner_add_right (x y z : V) :
    B x (A y z) = RCadd (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 x, completedInner_add_left,
    completedInner_symm hw0 hw1 y x, completedInner_symm hw0 hw1 z x]

theorem completedInner_smul_left (c : Q') (x y : V) :
    B (S c x) y = RCscale c (B x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound
    (representativeInner_smul_left hw0 hw1 c X Y)

theorem completedInner_smul_right (c : Q') (x y : V) :
    B x (S c y) = RCscale c (B x y) := by
  rw [completedInner_symm hw0 hw1 x, completedInner_smul_left,
    completedInner_symm hw0 hw1 y x]

theorem completedInner_zero_left (x : V) : B Z x = RCzero := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  apply Equiv_of_limit_of_equal
    (fun n => intrinsicForm_zero_left hw0 hw1 (X.seq n))
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      ((D).constant (zero width)) X)
    (convergesTo_const czero)

theorem completedInner_zero_right (x : V) : B x Z = RCzero := by
  rw [completedInner_symm, completedInner_zero_left]

private theorem time_sum_pairing (n : Nat)
    (x y z : IntrinsicExpression width) :
    Equiv (F (advance n (sum x y)) z)
      (F (sum (advance n x) (advance n y)) z) := by
  refine (intrinsicForm_time_balance hw0 hw1 n (sum x y) z).trans ?_
  refine (intrinsicForm_sum_left hw0 hw1 x y (advance n z)).trans ?_
  refine (Equiv_add (intrinsicForm_time_balance hw0 hw1 n x z).symm
    (intrinsicForm_time_balance hw0 hw1 n y z).symm).trans ?_
  exact (intrinsicForm_sum_left hw0 hw1 (advance n x) (advance n y) z).symm

private theorem time_smul_pairing (n : Nat) (c : Q')
    (x z : IntrinsicExpression width) :
    Equiv (F (advance n (smul c x)) z) (F (smul c (advance n x)) z) := by
  refine (intrinsicForm_time_balance hw0 hw1 n (smul c x) z).trans ?_
  refine (intrinsicForm_smul_left hw0 hw1 c x (advance n z)).trans ?_
  refine (Pivot2.mul_congr_right
    (intrinsicForm_time_balance hw0 hw1 n x z).symm).trans ?_
  exact (intrinsicForm_smul_left hw0 hw1 c (advance n x) z).symm

/-- Addition of vectors, distinct from addition of time indices. -/
theorem completedTime_additive (n : Nat) (x y : V) :
    T n (A x y) = A (T n x) (T n y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply completion_eq_of_pointwise hw0 hw1
  intro k z
  exact time_sum_pairing hw0 hw1 n (X.seq k) (Y.seq k) z

theorem completedTime_smul (n : Nat) (c : Q') (x : V) :
    T n (S c x) = S c (T n x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro k z
  exact time_smul_pairing hw0 hw1 n c (X.seq k) z

theorem completedTime_zero_element (n : Nat) : T n Z = Z := by
  unfold completedZero
  rw [completedTime_embed]
  apply completion_eq_of_pointwise hw0 hw1
  intro _ z
  exact (intrinsicForm_time_balance hw0 hw1 n (zero width) z).trans
    ((intrinsicForm_zero_left hw0 hw1 (advance n z)).trans
      (intrinsicForm_zero_left hw0 hw1 z).symm)

theorem completedTime_sub (n : Nat) (x y : V) :
    T n (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (T n x) (T n y) := by
  unfold completedSub completedNeg
  rw [completedTime_additive, completedTime_smul]

/-- A finite signed sum of actual time-translated states. -/
def orbitSum (x : V) : List (Q' × Nat) → V
  | [] => Z
  | (c,n)::cs => A (S c (T n x)) (orbitSum x cs)

def responseSum : List (Q' × Nat) → (Nat → RC) → RC
  | [], _ => RCzero
  | (c,n)::cs, f => RCadd (RCscale c (f n)) (responseSum cs f)

theorem orbitSum_inner_left (x y : V) (cs : List (Q' × Nat)) :
    B (orbitSum hw0 hw1 x cs) y =
      responseSum cs (fun n => B (T n x) y) := by
  induction cs with
  | nil => exact completedInner_zero_left hw0 hw1 y
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      simp only [orbitSum, responseSum, completedInner_add_left,
        completedInner_smul_left, ih]

theorem orbitSum_inner_right (x y : V) (cs : List (Q' × Nat)) :
    B x (orbitSum hw0 hw1 y cs) =
      responseSum cs (fun n => B x (T n y)) := by
  induction cs with
  | nil => exact completedInner_zero_right hw0 hw1 x
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      simp only [orbitSum, responseSum, completedInner_add_right,
        completedInner_smul_right, ih]

/-- Every signed cross term remains in the actual completed correlator. -/
theorem orbitSum_pairing (x y : V) (cs ds : List (Q' × Nat)) :
    B (orbitSum hw0 hw1 x cs) (orbitSum hw0 hw1 y ds) =
      responseSum cs (fun m => responseSum ds
        (fun n => B x (T (m+n) y))) := by
  rw [orbitSum_inner_left]
  apply congrArg (responseSum cs)
  funext m
  rw [orbitSum_inner_right]
  exact congrArg (responseSum ds)
    (funext (fun n => completedInner_time_sum hw0 hw1 m n x y))

theorem orbitSum_time (x : V) (cs : List (Q' × Nat)) (m : Nat) :
    T m (orbitSum hw0 hw1 x cs) = orbitSum hw0 hw1 (T m x) cs := by
  induction cs with
  | nil => exact completedTime_zero_element hw0 hw1 m
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      simp only [orbitSum, completedTime_additive, completedTime_smul, ih]
      rw [← completedTime_add, ← completedTime_add, Nat.add_comm m n]

theorem orbitSum_orthogonal (x : V) (hx : B U x = RCzero)
    (cs : List (Q' × Nat)) : B U (orbitSum hw0 hw1 x cs) = RCzero := by
  induction cs with
  | nil => exact completedInner_zero_right hw0 hw1 U
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      rw [orbitSum, completedInner_add_right, completedInner_smul_right,
        completedTime_preserves_vacuumComplement hw0 hw1 n x hx,
        RCscale_RCzero, ih]
      rfl

/-- Finite time filtering stays in the existing strict sector.  No
nonvanishing assertion for the filtered vector is made. -/
theorem orbitSum_twoStep_form_gap (x : V) (hx : B U x = RCzero)
    (cs : List (Q' × Nat)) :
    let y := orbitSum hw0 hw1 x cs
    RCle (B y (T 2 y))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (B y y)) :=
  completed_twoStep_form_gap hw0 hw1 width (orbitSum hw0 hw1 x cs)
    ((completedInner_symm hw0 hw1 (orbitSum hw0 hw1 x cs) U).trans
      (orbitSum_orthogonal hw0 hw1 x hx cs))

#print axioms representativeInner_add_left
#print axioms representativeInner_smul_left
#print axioms completedInner_add_left
#print axioms completedInner_add_right
#print axioms completedInner_smul_left
#print axioms completedInner_smul_right
#print axioms completedInner_zero_left
#print axioms completedInner_zero_right
#print axioms completedTime_additive
#print axioms completedTime_smul
#print axioms completedTime_zero_element
#print axioms completedTime_sub
#print axioms orbitSum
#print axioms responseSum
#print axioms orbitSum_inner_left
#print axioms orbitSum_inner_right
#print axioms orbitSum_pairing
#print axioms orbitSum_time
#print axioms orbitSum_orthogonal
#print axioms orbitSum_twoStep_form_gap

end YMGap.Continuum.BF4WilsonAllNomeBilinearTime
