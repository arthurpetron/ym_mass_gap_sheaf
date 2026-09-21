/-
# Constructive real scaling on the SAME all-nome joint carrier

The scalar and its rational Cauchy modulus are supplied as data. The actual
joint dense scalar stream descends by separation of the original pairing.
Equivalent scalar streams, even with different moduli, act identically.
Physical time commutes with this operation on the same carrier.

This supplies the vacuum projection consumer. No representative or modulus
is selected from a bare quotient real, no arbitrary quotient-level
completeness is asserted, and no continuum or physical-mass input is added.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

theorem representativeInner_realScalar_left (s : CReal) (cs : QCauchy s.approx)
    (X Y : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 width (realScalarCauchy hw0 hw1 width s cs X) Y)
      (mul s (representativeInner hw0 hw1 width X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => jointPairing_smul_left hw0 hw1 width (s.approx n) (X.seq n) (Y.seq n))
    (pairSequence_converges hw0 hw1 width (realScalarCauchy hw0 hw1 width s cs X) Y)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self s) (pairSequence_converges hw0 hw1 width X Y))

theorem realScalarCauchy_pairing (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (y : V) :
    B (Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width s cs X)) y =
      RCmul (Quotient.mk crealSetoid s) (B (Quotient.mk (D).completionSetoid X) y) := by
  refine Quotient.inductionOn y ?_
  exact fun Y => Quotient.sound (representativeInner_realScalar_left hw0 hw1 width s cs X Y)

/-- Both vector representatives and the scalar stream/modulus are immaterial. -/
theorem realScalarCauchy_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hst : Equiv s t) (X Y : (D).Cauchy)
    (hX : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width s cs X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width t ct Y) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro z
  rw [realScalarCauchy_pairing, realScalarCauchy_pairing, hX,
    show Quotient.mk crealSetoid s = Quotient.mk crealSetoid t from Quotient.sound hst]

def completedRealSmul (s : CReal) (cs : QCauchy s.approx) : V → V :=
  Quotient.lift
    (fun X => Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width s cs X))
    (fun X Y h => realScalarCauchy_congr hw0 hw1 width
      s s cs cs (Equiv.refl s) X Y (Quotient.sound h))

theorem completedRealSmul_mk (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    completedRealSmul hw0 hw1 width s cs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 width s cs X) := rfl

theorem completedInner_realSmul_left (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B (completedRealSmul hw0 hw1 width s cs x) y =
      RCmul (Quotient.mk crealSetoid s) (B x y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_pairing hw0 hw1 width s cs X y

theorem completedInner_realSmul_right (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B x (completedRealSmul hw0 hw1 width s cs y) =
      RCmul (Quotient.mk crealSetoid s) (B x y) := by
  rw [completedInner_symm hw0 hw1 width x, completedInner_realSmul_left,
    completedInner_symm hw0 hw1 width y x]

theorem completedRealSmul_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hst : Equiv s t) (x : V) :
    completedRealSmul hw0 hw1 width s cs x = completedRealSmul hw0 hw1 width t ct x := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_congr hw0 hw1 width s t cs ct hst X X rfl

theorem completedRealSmul_ofQ' (q : Q') (cq : QCauchy (ofQ' q).approx) (x : V) :
    completedRealSmul hw0 hw1 width (ofQ' q) cq x = completedSmul hw0 hw1 width q x := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [completedInner_realSmul_left, completedInner_smul_left]
  exact Quotient.inductionOn (B x y) (fun _ => rfl)

theorem completedRealSmul_add (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    completedRealSmul hw0 hw1 width s cs (completedAdd hw0 hw1 width x y) =
      completedAdd hw0 hw1 width (completedRealSmul hw0 hw1 width s cs x)
        (completedRealSmul hw0 hw1 width s cs y) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro test
  simp only [completedInner_add_left, completedInner_realSmul_left]
  refine Quotient.inductionOn₂ (B x test) (B y test) ?_
  exact fun X Y => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_add_eqv (s.approx n) (X.approx n) (Y.approx n)))

/-- Actual physical time commutes with the modulus-bearing real operation. -/
theorem completedTime_realSmul (n : Nat) (s : CReal) (cs : QCauchy s.approx) (x : V) :
    T n (completedRealSmul hw0 hw1 width s cs x) =
      completedRealSmul hw0 hw1 width s cs (T n x) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [completedInner_time_balance, completedInner_realSmul_left,
    completedInner_realSmul_left, completedInner_time_balance]

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.representativeInner_realScalar_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.realScalarCauchy_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.realScalarCauchy_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedRealSmul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedRealSmul_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedInner_realSmul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedInner_realSmul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedRealSmul_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedRealSmul_ofQ'
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedRealSmul_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar.completedTime_realSmul
