/-
# Completed two-step gap form for the literal-width all-nome Wilson carrier

The prefactor-free dense centered estimate passes through the three actual
pairing limits of each supplied Cauchy representative.  Quotient induction
then gives the same estimate for every completed vector orthogonal to the
embedded constant state.

The rate remains nome- and width-dependent.  This is neither a width-uniform
gap nor a continuum/Hamiltonian conclusion.
-/

import YMGap.Continuum.BF4WilsonAllNomeDenseGap
import YMGap.Continuum.BF4WilsonAllNomeCompletedTime
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4WilsonAllNomeCompletedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
open YMGap.Continuum.BF4WilsonAllNomeDenseGap (centered_twoStep_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat)

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "A" n => timeNonexpansive hw0 hw1 (width := width) n
local notation "R" => CRealSeminormPairingCompletion.representativeInner PD

/-- Scalar centering of the actual representative pairing. -/
def representativeCenteredMoment (n : Nat) (X Y : (D).Cauchy) : CReal :=
  sub (R X ((A n).mapCauchy Y))
    (mul (R X ((D).constant (unit width)))
      (R ((D).constant (unit width)) Y))

/-- Its approximation modulus is assembled from the three supplied pairing
moduli and constructive scalar-product arithmetic. -/
def representativeCenteredMomentCauchy (n : Nat) (X Y : (D).Cauchy) :
    QCauchy (representativeCenteredMoment hw0 hw1 width n X Y).approx :=
  let A0 := R X ((A n).mapCauchy Y)
  let L := R X ((D).constant (unit width))
  let R0 := R ((D).constant (unit width)) Y
  let cA := CRealSeminormPairingCompletion.representativeInnerCauchy PD
    X ((A n).mapCauchy Y)
  let cL := CRealSeminormPairingCompletion.representativeInnerCauchy PD
    X ((D).constant (unit width))
  let cR := CRealSeminormPairingCompletion.representativeInnerCauchy PD
    ((D).constant (unit width)) Y
  scalarAddCauchy A0 (neg (mul L R0)) cA
    (scalarNegCauchy (mul L R0) (scalarMulCauchy L R0 cL cR))

/-- Physical lag is fixed while the Cauchy-stream index varies. -/
theorem representativeCenteredMoment_converges (n : Nat) (X Y : (D).Cauchy) :
    ConvergesTo (fun k => centeredTimeMoment hw0 hw1 n (X.seq k) (Y.seq k))
      (representativeCenteredMoment hw0 hw1 width n X Y) := by
  have htime := CRealSeminormPairingCompletion.pairSequence_converges PD
    X ((A n).mapCauchy Y)
  have hleft := CRealSeminormPairingCompletion.pairSequence_converges PD
    X ((D).constant (unit width))
  have hright := CRealSeminormPairingCompletion.pairSequence_converges PD
    ((D).constant (unit width)) Y
  exact TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))

/-- Scalar subtraction on existing completed vectors, not a new centered
carrier. -/
def completedCenteredScalar (n : Nat) (x y : V) : RC :=
  RCsub (B x (T n y)) (RCmul (B x U) (B U y))

theorem representativeCenteredMoment_pin (n : Nat) (X Y : (D).Cauchy) :
    completedCenteredScalar hw0 hw1 width n
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeCenteredMoment hw0 hw1 width n X Y) := rfl

/-- The dense estimate passes to every actual Cauchy representative without
a uniform presentation cap. -/
theorem representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 width 2 X X)
      (mul (ofQ' (twoStepRate hw0 hw1 width))
        (representativeCenteredMoment hw0 hw1 width 0 X X)) :=
  leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 width 2 X X)
    (convergesTo_const_mul (ofQ' (twoStepRate hw0 hw1 width))
      (representativeCenteredMoment_converges hw0 hw1 width 0 X X))
    (fun k => centered_twoStep_bound hw0 hw1 (X.seq k))

theorem completedCenteredScalar_twoStep_gap (x : V) :
    RCle (completedCenteredScalar hw0 hw1 width 2 x x)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (completedCenteredScalar hw0 hw1 width 0 x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 width 2 X X,
    representativeCenteredMoment_pin hw0 hw1 width 0 X X]
  exact representative_twoStep_form_gap hw0 hw1 width X

theorem completedCenteredScalar_even_nonnegative (n : Nat) (x : V) :
    RCnonneg (completedCenteredScalar hw0 hw1 width (2*n) x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 width (2*n) X X]
  exact leEv_of_convergesTo_le (convergesTo_const czero)
    (representativeCenteredMoment_converges hw0 hw1 width (2*n) X X)
    (fun k => evenMoment_nonnegative hw0 hw1 (X.seq k) n)

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A0 => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A0.approx n)))

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A0
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A0.approx n)))))

/-- Orthogonality removes the scalar correction without selecting a centered
vector representative. -/
theorem completedCenteredScalar_of_orthogonal (n : Nat) (x : V)
    (hx : B x U = RCzero) :
    completedCenteredScalar hw0 hw1 width n x x = B x (T n x) := by
  unfold completedCenteredScalar
  rw [hx, rc_zero_mul, rc_sub_zero]

/-- Strict two-step form estimate on every vector orthogonal to the unit in
this same all-nome completion. -/
theorem completed_twoStep_form_gap (x : V) (hx : B x U = RCzero) :
    RCle (B x (T 2 x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (B x x)) := by
  have h := completedCenteredScalar_twoStep_gap hw0 hw1 width x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 width 2 x hx,
    completedCenteredScalar_of_orthogonal hw0 hw1 width 0 x hx,
    completedTime_zero] at h
  exact h

theorem completed_even_nonnegative (n : Nat) (x : V)
    (hx : B x U = RCzero) : RCnonneg (B x (T (2*n) x)) := by
  have h := completedCenteredScalar_even_nonnegative hw0 hw1 width n x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 width (2*n) x hx] at h
  exact h

/-- Direct consumer on the existing vacuum-complement subtype.  Its stored
orthogonality has the unit on the left; symmetry of this SAME completed
pairing supplies exactly the orientation used by the scalar-centering proof. -/
theorem vacuumComplement_twoStep_form_gap
    (x : VacuumComplement hw0 hw1 (width := width)) :
    RCle (B x.val (T 2 x.val))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (B x.val x.val)) :=
  completed_twoStep_form_gap hw0 hw1 width x.val
    ((completedInner_symm hw0 hw1 x.val U).trans x.property)

theorem completedInner_even_diagonal (n : Nat) (x : V) :
    B x (T (2*n) x) = B (T n x) (T n x) := by
  simpa only [Nat.two_mul] using
    (completedInner_time_sum (width := width) hw0 hw1 n n x x).symm

/-! The fixed-parameter same-carrier estimate can be translated to every
time slice.  The rate is still the supplied nome/width rate; this theorem
does not introduce a new transfer or a scaling limit. -/
theorem completed_twoStep_translated (n : Nat) (x : V)
  (hx : B x U = RCzero) :
    RCle (B (T n x) (T (n+2) x))
      (RCscale (twoStepRate hw0 hw1 width)
        (B (T n x) (T n x))) := by
  have hx' : B U x = RCzero :=
    (completedInner_symm hw0 hw1 U x).trans hx
  have horth' := completedTime_preserves_vacuumComplement
    (width := width) hw0 hw1 n x hx'
  have horth : B (T n x) U = RCzero :=
    (completedInner_symm hw0 hw1 (T n x) U).trans horth'
  have h := completed_twoStep_form_gap hw0 hw1 width (T n x) horth
  rw [show n+2 = 2+n by omega,
    completedTime_add (width := width) hw0 hw1 2 n x]
  exact h

/-! The translated two-step estimate is the one-step norm contraction at the
intervening time slice, using the exact completed pairing identity. -/
theorem completed_oneStep_norm_gap (n : Nat) (x : V)
    (hx : B x U = RCzero) :
    RCle (B (T (n+1) x) (T (n+1) x))
      (RCscale (twoStepRate hw0 hw1 width)
        (B (T n x) (T n x))) := by
  have h := completed_twoStep_translated hw0 hw1 width n x hx
  rw [completedInner_time_sum (width := width) hw0 hw1 n (n+2) x x,
    show n + (n+2) = 2*(n+1) by omega,
    completedInner_even_diagonal hw0 hw1 width (n+1) x] at h
  exact h

/-! Iteration of the same completed-carrier contraction.  The power is the
fixed nome/width rate, so this remains a discrete finite-parameter statement.
-/
theorem completed_iterated_norm_gap (n : Nat) (x : V)
    (hx : B x U = RCzero) :
    RCle (B (T n x) (T n x))
      (RCscale ((twoStepRate hw0 hw1 width)^n) (B x x)) := by
  induction n with
  | zero =>
      rw [completedTime_zero, Q'.pow_zero, RCscale_one]
      exact RCle_refl _
  | succ k ih =>
      have hstep := completed_oneStep_norm_gap hw0 hw1 width k x hx
      refine RCle_trans hstep ?_
      have hrateNonnegative : (0 : Q') ≤ twoStepRate hw0 hw1 width :=
        twoStepRate_nonnegative hw0 hw1 width
      have hscaled := RCscale_mono hrateNonnegative ih
      refine RCle_trans hscaled ?_
      rw [RCscale_RCscale, Q'.pow_succ]
      exact RCle_refl _

/-! The iterated norm estimate is the same-object even-lag correlator bound;
no representative or new observable is introduced. -/
theorem completed_even_lag_corr_decay (n : Nat) (x : V)
    (hx : B x U = RCzero) :
    RCle (B x (T (2*n) x))
      (RCscale ((twoStepRate hw0 hw1 width)^n) (B x x)) := by
  rw [completedInner_even_diagonal hw0 hw1 width n x]
  exact completed_iterated_norm_gap hw0 hw1 width n x hx

theorem completed_even_lag_corr_nonnegative (n : Nat) (x : V) :
    RCnonneg (B x (T (2*n) x)) := by
  rw [completedInner_even_diagonal hw0 hw1 width n x]
  exact completedInner_nonnegative hw0 hw1 (T n x)

#print axioms representativeCenteredMoment
#print axioms representativeCenteredMomentCauchy
#print axioms representativeCenteredMoment_converges
#print axioms completedCenteredScalar
#print axioms representativeCenteredMoment_pin
#print axioms representative_twoStep_form_gap
#print axioms completedCenteredScalar_twoStep_gap
#print axioms completedCenteredScalar_even_nonnegative
#print axioms completedCenteredScalar_of_orthogonal
#print axioms completed_twoStep_form_gap
#print axioms completed_even_nonnegative
#print axioms vacuumComplement_twoStep_form_gap
#print axioms completed_twoStep_translated
#print axioms completed_oneStep_norm_gap
#print axioms completed_iterated_norm_gap
#print axioms completed_even_lag_corr_decay
#print axioms completed_even_lag_corr_nonnegative

end YMGap.Continuum.BF4WilsonAllNomeCompletedGap
