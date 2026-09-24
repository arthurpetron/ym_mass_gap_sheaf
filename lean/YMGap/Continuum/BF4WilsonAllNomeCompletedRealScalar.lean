/-
# Real scaling on the literal all-nome Wilson completion

The action takes a `CReal` together with explicit `QCauchy` data and descends
the varying rational-scaled stream from the SAME Wilson Cauchy carrier.
Pairing homogeneity proves independence of scalar data and representatives.
This is fixed-width completed linear algebra, not a scaling-limit assertion.
-/

import YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy
import YMGap.Continuum.BF4WilsonAllNomeDistance

namespace YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws (intrinsicForm_smul_left)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy
open YMGap.Continuum.CRealSeminormPairingCompletion

def rationalCauchy (q : Q') : QCauchy (ofQ' q).approx where
  M _ := 0
  bound := fun _ he _ _ _ _ =>
    ⟨Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he),
      Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he)⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "V" => Completion hw0 hw1 width

/-- Equality follows by testing the completed difference against itself. -/
theorem completed_eq_of_pairings (x y : V) (h : ∀ z, B x z = B y z) : x = y := by
  let d := completedSub hw0 hw1 x y
  have hd : B d d = RCzero := calc
    B d d = RCadd (B x d) (B (completedNeg hw0 hw1 y) d) :=
      completedInner_add_left hw0 hw1 x (completedNeg hw0 hw1 y) d
    _ = RCadd (B y d) (B (completedNeg hw0 hw1 y) d) :=
      congrArg (fun a => RCadd a (B (completedNeg hw0 hw1 y) d)) (h d)
    _ = B (completedAdd hw0 hw1 y (completedNeg hw0 hw1 y)) d :=
      (completedInner_add_left hw0 hw1 y (completedNeg hw0 hw1 y) d).symm
    _ = RCzero := by rw [completedAdd_comm, completedNeg_add, completedInner_zero_left]
  exact (completedDist_zero_iff hw0 hw1 x y).mp hd

theorem representativeInner_realScalar_left (s : CReal) (cs : QCauchy s.approx)
    (X Y : (D).Cauchy) :
    Equiv (representativeInner PD (realScalarCauchy hw0 hw1 s cs X) Y)
      (CReal.mul s (representativeInner PD X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => intrinsicForm_smul_left hw0 hw1 (s.approx n) (X.seq n) (Y.seq n))
    (pairSequence_converges PD (realScalarCauchy hw0 hw1 s cs X) Y)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self s) (pairSequence_converges PD X Y))

theorem realScalarCauchy_pairing (s : CReal) (cs : QCauchy s.approx)
    (X : (D).Cauchy) (y : V) :
    B (Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 s cs X)) y =
      RCmul (Quotient.mk crealSetoid s)
        (B (Quotient.mk (D).completionSetoid X) y) := by
  refine Quotient.inductionOn y ?_
  exact fun Y => Quotient.sound (representativeInner_realScalar_left hw0 hw1 s cs X Y)

theorem realScalarCauchy_congr (s t : CReal) (cs : QCauchy s.approx)
    (ct : QCauchy t.approx) (hs : Equiv s t) (X Y : (D).Cauchy)
    (hX : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 s cs X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 t ct Y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [realScalarCauchy_pairing, realScalarCauchy_pairing, hX,
    show Quotient.mk crealSetoid s = Quotient.mk crealSetoid t from Quotient.sound hs]

def completedRealSmul (s : CReal) (cs : QCauchy s.approx) : V → V :=
  Quotient.lift
    (fun X => Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 s cs X))
    (fun X Y h => realScalarCauchy_congr hw0 hw1 s s cs cs (Equiv.refl s)
      X Y (Quotient.sound h))

theorem completedRealSmul_mk (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    completedRealSmul hw0 hw1 s cs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 s cs X) := rfl

theorem completedInner_realSmul_left (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B (completedRealSmul hw0 hw1 s cs x) y = RCmul (Quotient.mk crealSetoid s) (B x y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_pairing hw0 hw1 s cs X y

theorem completedInner_realSmul_right (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B x (completedRealSmul hw0 hw1 s cs y) = RCmul (Quotient.mk crealSetoid s) (B x y) := by
  rw [completedInner_symm hw0 hw1 x, completedInner_realSmul_left,
    completedInner_symm hw0 hw1 y x]

theorem completedRealSmul_congr (s t : CReal) (cs : QCauchy s.approx)
    (ct : QCauchy t.approx) (hs : Equiv s t) (x : V) :
    completedRealSmul hw0 hw1 s cs x = completedRealSmul hw0 hw1 t ct x := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_congr hw0 hw1 s t cs ct hs X X rfl

theorem completedRealSmul_ofQ' (q : Q') (cq : QCauchy (ofQ' q).approx) (x : V) :
    completedRealSmul hw0 hw1 (ofQ' q) cq x = completedSmul hw0 hw1 q x := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [completedInner_realSmul_left, completedInner_smul_left]
  refine Quotient.inductionOn (B x y) ?_
  intro z
  rfl

theorem completedRealSmul_one (c : QCauchy cone.approx) (x : V) :
    completedRealSmul hw0 hw1 cone c x = x :=
  (completedRealSmul_ofQ' hw0 hw1 1 c x).trans (completedSmul_one hw0 hw1 x)

theorem completedRealSmul_zero (c : QCauchy czero.approx) (x : V) :
    completedRealSmul hw0 hw1 czero c x = completedZero hw0 hw1 width :=
  (completedRealSmul_ofQ' hw0 hw1 0 c x).trans (completedSmul_zero hw0 hw1 x)

/-- The descended real action commutes with the actual completed time map. -/
theorem completedTime_realSmul (n : Nat) (s : CReal) (cs : QCauchy s.approx) (x : V) :
    BF4WilsonAllNomeCompletedTime.completedTime hw0 hw1 n
        (completedRealSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs
        (BF4WilsonAllNomeCompletedTime.completedTime hw0 hw1 n x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [BF4WilsonAllNomeCompletedTime.completedInner_time_balance,
    completedInner_realSmul_left, completedInner_realSmul_left,
    BF4WilsonAllNomeCompletedTime.completedInner_time_balance]

end YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.rationalCauchy
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completed_eq_of_pairings
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.representativeInner_realScalar_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.realScalarCauchy_pairing
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.realScalarCauchy_congr
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedRealSmul
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedRealSmul_mk
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedInner_realSmul_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedInner_realSmul_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedRealSmul_congr
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedRealSmul_ofQ'
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedRealSmul_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedRealSmul_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar.completedTime_realSmul
