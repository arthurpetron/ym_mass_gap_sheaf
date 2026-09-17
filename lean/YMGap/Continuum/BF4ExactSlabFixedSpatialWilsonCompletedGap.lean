/-
# Strict two-step form bound on the SAME Wilson Cauchy completion

Three actual completed-pairing limits define the centered moment of each
supplied Cauchy stream. The already prefactor-free dense Wilson estimate
passes through these scalar limits without a uniform bound on the streams'
expression caps or radii. Quotient induction covers every vector orthogonal
to the actual embedded unit in this EXISTING Wilson Completion.

The displayed rate is rho(w)^2, independent of the positive source base,
under the original small-nome guards. The map is the actual two-step
discrete physical time, not a link-update dynamics. This does not construct
full Hilbert completeness, a continuum Hamiltonian, changing-spacing
control, a calibrated physical mass or the every-group Clay theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap (evenMoment_first_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Only the scalar rate facts are reused; no old-carrier bound enters. -/
theorem twoStepRate_strict {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    (0 : Q') < twoStepRate w hd ∧ twoStepRate w hd < (1 : Q') :=
  ⟨twoStepRate_positive hw0 hd, twoStepRate_lt_one hw0 hd hs⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0<base)

local notation "D" => seminorm hw0 hw1 hsmall hd hs hb
local notation "PD" => pairingData hw0 hw1 hsmall hd hs hb
local notation "V" => Completion hw0 hw1 hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 hsmall hd hs hb
local notation "T" => completedTime hw0 hw1 hsmall hd hs hb
local notation "U" => embed hw0 hw1 hsmall hd hs hb (unit base)

/-- Scalar centering of actual representative pairings, retaining the
existing physical-time map and the constant original-unit stream. -/
def representativeCenteredMoment (n : Nat) (X Y : (D).Cauchy) : CReal :=
  sub (representativeInner hw0 hw1 hsmall hd hs hb X
      ((timeNonexpansive hw0 hw1 hsmall hd hs hb n).mapCauchy Y))
    (mul (representativeInner hw0 hw1 hsmall hd hs hb X ((D).constant (unit base)))
      (representativeInner hw0 hw1 hsmall hd hs hb ((D).constant (unit base)) Y))

/-- Computed scalar Cauchy data use all three actual pairing representatives. -/
def representativeCenteredMomentCauchy (n : Nat) (X Y : (D).Cauchy) :
    QCauchy (representativeCenteredMoment hw0 hw1 hsmall hd hs hb n X Y).approx :=
  let A := representativeInner hw0 hw1 hsmall hd hs hb X
    ((timeNonexpansive hw0 hw1 hsmall hd hs hb n).mapCauchy Y)
  let L := representativeInner hw0 hw1 hsmall hd hs hb X ((D).constant (unit base))
  let R := representativeInner hw0 hw1 hsmall hd hs hb ((D).constant (unit base)) Y
  let cA := representativeInnerCauchy hw0 hw1 hsmall hd hs hb X
    ((timeNonexpansive hw0 hw1 hsmall hd hs hb n).mapCauchy Y)
  let cL := representativeInnerCauchy hw0 hw1 hsmall hd hs hb X ((D).constant (unit base))
  let cR := representativeInnerCauchy hw0 hw1 hsmall hd hs hb ((D).constant (unit base)) Y
  scalarAddCauchy A (neg (mul L R)) cA
    (scalarNegCauchy (mul L R) (scalarMulCauchy L R cL cR))

/-- The physical lag is fixed while the supplied Cauchy index varies.
No stream-uniform bound on the original expression presentations is assumed. -/
theorem representativeCenteredMoment_converges (n : Nat) (X Y : (D).Cauchy) :
    ConvergesTo
      (fun k => centeredTimeMoment hw0 hw1 hsmall hd hs hb n (X.seq k) (Y.seq k))
      (representativeCenteredMoment hw0 hw1 hsmall hd hs hb n X Y) := by
  have htime := CRealSeminormPairingCompletion.pairSequence_converges PD X
    ((timeNonexpansive hw0 hw1 hsmall hd hs hb n).mapCauchy Y)
  have hleft := CRealSeminormPairingCompletion.pairSequence_converges PD X ((D).constant (unit base))
  have hright := CRealSeminormPairingCompletion.pairSequence_converges PD ((D).constant (unit base)) Y
  exact TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))

/-- Scalar subtraction on the existing completed objects, not a new carrier
or an assumed completed vector-centering operation. -/
def completedCenteredScalar (n : Nat) (x y : V) : RC :=
  RCsub (B x (T n y)) (RCmul (B x U) (B U y))

theorem representativeCenteredMoment_pin (n : Nat) (X Y : (D).Cauchy) :
    completedCenteredScalar hw0 hw1 hsmall hd hs hb n
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeCenteredMoment hw0 hw1 hsmall hd hs hb n X Y) := rfl

/-- The SAME prefactor-free estimate passes through actual scalar limits
for every supplied Wilson Cauchy stream. -/
theorem representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 hsmall hd hs hb 2 X X)
      (mul (ofQ' (twoStepRate w hd))
        (representativeCenteredMoment hw0 hw1 hsmall hd hs hb 0 X X)) :=
  leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs hb 2 X X)
    (convergesTo_const_mul (ofQ' (twoStepRate w hd))
      (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs hb 0 X X))
    (fun k => evenMoment_first_le hw0 hw1 hsmall hd hs hb (X.seq k))

theorem completedCenteredScalar_twoStep_gap (x : V) :
    RCle (completedCenteredScalar hw0 hw1 hsmall hd hs hb 2 x x)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd)))
        (completedCenteredScalar hw0 hw1 hsmall hd hs hb 0 x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 hsmall hd hs hb 2 X X,
    representativeCenteredMoment_pin hw0 hw1 hsmall hd hs hb 0 X X]
  exact representative_twoStep_form_gap hw0 hw1 hsmall hd hs hb X

/-- Positivity remains an even-time statement. -/
theorem completedCenteredScalar_even_nonnegative (n : Nat) (x : V) :
    RCnonneg (completedCenteredScalar hw0 hw1 hsmall hd hs hb (2*n) x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 hsmall hd hs hb (2*n) X X]
  exact leEv_of_convergesTo_le (convergesTo_const czero)
    (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs hb (2*n) X X)
    (fun k => evenMoment_nonnegative hw0 hw1 hsmall hd hs hb (X.seq k) n)

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

/-- Orthogonality removes the correction on the SAME completed pairing. -/
theorem completedCenteredScalar_of_orthogonal (n : Nat) (x : V) (hx : B x U = RCzero) :
    completedCenteredScalar hw0 hw1 hsmall hd hs hb n x x = B x (T n x) := by
  unfold completedCenteredScalar
  rw [hx, rc_zero_mul, rc_sub_zero]

/-- Universal strict form bound on the actual completed unit complement.
The rate depends on nome, not on the vector, its radius or the positive base. -/
theorem completed_twoStep_form_gap (x : V) (hx : B x U = RCzero) :
    RCle (B x (T 2 x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd))) (B x x)) := by
  have h := completedCenteredScalar_twoStep_gap hw0 hw1 hsmall hd hs hb x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs hb 2 x hx,
    completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs hb 0 x hx,
    completedTime_zero] at h
  exact h

theorem completed_even_nonnegative (n : Nat) (x : V) (hx : B x U = RCzero) :
    RCnonneg (B x (T (2*n) x)) := by
  have h := completedCenteredScalar_even_nonnegative hw0 hw1 hsmall hd hs hb n x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs hb (2*n) x hx] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.twoStepRate_strict
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.representativeCenteredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.representativeCenteredMomentCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.representativeCenteredMoment_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.completedCenteredScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.representativeCenteredMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.representative_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.completedCenteredScalar_twoStep_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.completedCenteredScalar_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.completedCenteredScalar_of_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.completed_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap.completed_even_nonnegative
