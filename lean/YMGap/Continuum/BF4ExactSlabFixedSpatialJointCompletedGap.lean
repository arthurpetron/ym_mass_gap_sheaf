/-
# Strict two-step form bound on the actual joint Cauchy completion

The cutoff-removed centered moments of each supplied physical Cauchy
stream converge by the three actual completed-pairing limits and scalar
product continuity. Their already prefactor-free dense bound therefore
passes to every representative, without a uniform presentation cap.
Quotient induction gives the result on the SAME JointCompletion and its
constructed physical time map, without choosing representatives.

The completed centered scalar below is only subtraction of scalar unit
coefficients. No completed linear or vector-centering operation is needed:
for any vector orthogonal to the actual unit, this scalar is the ordinary
completed time pairing. The rate is the existing nome/width-dependent q^2,
including its zero case. No metric completeness, Hamiltonian, continuous
time, spatial-uniform estimate or continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm (jointSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width

/-- Scalar centering of the actual representative pairing, using the
literal joint-time map and the constant stream of the original unit. -/
def representativeCenteredMoment (n : Nat) (X Y : (D).Cauchy) : CReal :=
  sub (representativeInner hw0 hw1 width X
      ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy Y))
    (mul (representativeInner hw0 hw1 width X ((D).constant (unit width)))
      (representativeInner hw0 hw1 width ((D).constant (unit width)) Y))

/-- All approximation moduli are data from the three actual pairing
representatives; the product ceiling is computed by the scalar algebra. -/
def representativeCenteredMomentCauchy (n : Nat) (X Y : (D).Cauchy) :
    QCauchy (representativeCenteredMoment hw0 hw1 width n X Y).approx :=
  let A := representativeInner hw0 hw1 width X
    ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy Y)
  let L := representativeInner hw0 hw1 width X ((D).constant (unit width))
  let R := representativeInner hw0 hw1 width ((D).constant (unit width)) Y
  let cA := representativeInnerCauchy hw0 hw1 width X
    ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy Y)
  let cL := representativeInnerCauchy hw0 hw1 width X ((D).constant (unit width))
  let cR := representativeInnerCauchy hw0 hw1 width ((D).constant (unit width)) Y
  scalarAddCauchy A (neg (mul L R)) cA
    (scalarNegCauchy (mul L R) (scalarMulCauchy L R cL cR))

/-- The physical lag n is fixed while the supplied Cauchy index k varies.
No bound on the coefficient presentations is assumed uniformly in k. -/
theorem representativeCenteredMoment_converges (n : Nat) (X Y : (D).Cauchy) :
    ConvergesTo
      (fun k => jointCenteredMoment hw0 hw1 width n (X.seq k) (Y.seq k))
      (representativeCenteredMoment hw0 hw1 width n X Y) := by
  have htime := pairSequence_converges hw0 hw1 width X
    ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy Y)
  have hleft := pairSequence_converges hw0 hw1 width X ((D).constant (unit width))
  have hright := pairSequence_converges hw0 hw1 width ((D).constant (unit width)) Y
  exact TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))

/-- Scalar subtraction on existing completed objects, not a new vector
centering operation or a separate completed carrier. -/
def completedCenteredScalar (n : Nat) (x y : JointCompletion hw0 hw1 width) : RC :=
  RCsub (B x (T n y)) (RCmul (B x U) (B U y))

theorem representativeCenteredMoment_pin (n : Nat) (X Y : (D).Cauchy) :
    completedCenteredScalar hw0 hw1 width n
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeCenteredMoment hw0 hw1 width n X Y) := rfl

/-- The SAME prefactor-free q^2 estimate passes through the actual scalar
limits of every supplied joint Cauchy representative. -/
theorem representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 width 2 X X)
      (mul (ofQ' (twoStepRate hw0 hw1 width))
        (representativeCenteredMoment hw0 hw1 width 0 X X)) :=
  leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 width 2 X X)
    (convergesTo_const_mul (ofQ' (twoStepRate hw0 hw1 width))
      (representativeCenteredMoment_converges hw0 hw1 width 0 X X))
    (fun k => joint_twoStep_form_gap hw0 hw1 width (X.seq k))

theorem completedCenteredScalar_twoStep_gap (x : JointCompletion hw0 hw1 width) :
    RCle (completedCenteredScalar hw0 hw1 width 2 x x)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (completedCenteredScalar hw0 hw1 width 0 x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 width 2 X X,
    representativeCenteredMoment_pin hw0 hw1 width 0 X X]
  exact representative_twoStep_form_gap hw0 hw1 width X

/-- The even-time restriction is retained; this does not assert that the
one-step physical-time operator is positive. -/
theorem completedCenteredScalar_even_nonnegative (n : Nat)
    (x : JointCompletion hw0 hw1 width) :
    RCnonneg (completedCenteredScalar hw0 hw1 width (2*n) x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 width (2*n) X X]
  exact leEv_of_convergesTo_le (convergesTo_const czero)
    (representativeCenteredMoment_converges hw0 hw1 width (2*n) X X)
    (fun k => jointEvenMoment_nonnegative hw0 hw1 width (X.seq k) n)

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

/-- Orthogonality removes the scalar correction without constructing or
assuming a completed vector-centering operation. -/
theorem completedCenteredScalar_of_orthogonal (n : Nat)
    (x : JointCompletion hw0 hw1 width) (hx : B x U = RCzero) :
    completedCenteredScalar hw0 hw1 width n x x = B x (T n x) := by
  unfold completedCenteredScalar
  rw [hx, rc_zero_mul, rc_sub_zero]

/-- Universal strict form bound on the actual completed unit complement.
Its only vector premise is orthogonality in this SAME completed pairing. -/
theorem completed_twoStep_form_gap (x : JointCompletion hw0 hw1 width)
    (hx : B x U = RCzero) :
    RCle (B x (T 2 x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width))) (B x x)) := by
  have h := completedCenteredScalar_twoStep_gap hw0 hw1 width x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 width 2 x hx,
    completedCenteredScalar_of_orthogonal hw0 hw1 width 0 x hx,
    jointCompletedTime_zero] at h
  exact h

theorem completed_even_nonnegative (n : Nat) (x : JointCompletion hw0 hw1 width)
    (hx : B x U = RCzero) : RCnonneg (B x (T (2*n) x)) := by
  have h := completedCenteredScalar_even_nonnegative hw0 hw1 width n x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 width (2*n) x hx] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.representativeCenteredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.representativeCenteredMomentCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.representativeCenteredMoment_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.completedCenteredScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.representativeCenteredMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.representative_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.completedCenteredScalar_twoStep_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.completedCenteredScalar_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.completedCenteredScalar_of_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.completed_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap.completed_even_nonnegative
