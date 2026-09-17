/-
# Universal strict two-step bound on the actual Wilson spatial-union completion

Three computed representative pairing limits give the centered scalar of
every supplied union Cauchy stream. The dense prefactor-free estimate is
valid at each term's own positive base with one common nome-only rate.
It therefore passes through these scalar limits even for growing supports.
No orthogonal approximants or uniform bound on support bases are required.

Quotient induction covers every vector orthogonal to the actual unit of
the SAME UnionCompletion. The two-step map is actual discrete physical time;
even positivity does not assert one-step positivity. No metric completeness,
positive definiteness, stationary law or continuum Hamiltonian is claimed.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionPairingData
import YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm

namespace YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion (unitStage)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (pairingData completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner representativeInnerCauchy pairSequence_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)

open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

/-- Scalar centering of the actual representative pairing, using the
literal union-time map and the constant stream of the original unit. -/
def representativeCenteredMoment (n : Nat) (X Y : (D).Cauchy) : CReal :=
  sub (representativeInner (pairingData hw0 hw1 hsmall hd hs) X
      ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy Y))
    (mul (representativeInner (pairingData hw0 hw1 hsmall hd hs) X ((D).constant unitStage))
      (representativeInner (pairingData hw0 hw1 hsmall hd hs) ((D).constant unitStage) Y))

/-- All approximation moduli are data from the three actual pairing
representatives; the product ceiling is computed by the scalar algebra. -/
def representativeCenteredMomentCauchy (n : Nat) (X Y : (D).Cauchy) :
    QCauchy (representativeCenteredMoment hw0 hw1 hsmall hd hs n X Y).approx :=
  let A := representativeInner (pairingData hw0 hw1 hsmall hd hs) X
    ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy Y)
  let L := representativeInner (pairingData hw0 hw1 hsmall hd hs) X ((D).constant unitStage)
  let R := representativeInner (pairingData hw0 hw1 hsmall hd hs) ((D).constant unitStage) Y
  let cA := representativeInnerCauchy (pairingData hw0 hw1 hsmall hd hs) X
    ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy Y)
  let cL := representativeInnerCauchy (pairingData hw0 hw1 hsmall hd hs) X ((D).constant unitStage)
  let cR := representativeInnerCauchy (pairingData hw0 hw1 hsmall hd hs) ((D).constant unitStage) Y
  scalarAddCauchy A (neg (mul L R)) cA
    (scalarNegCauchy (mul L R) (scalarMulCauchy L R cL cR))

/-- The physical lag n is fixed while the supplied Cauchy index k varies.
Neither support bases nor coefficient presentations are assumed uniformly bounded in k. -/
theorem representativeCenteredMoment_converges (n : Nat) (X Y : (D).Cauchy) :
    ConvergesTo
      (fun k => centeredMoment hw0 hw1 hsmall hd hs n (X.seq k) (Y.seq k))
      (representativeCenteredMoment hw0 hw1 hsmall hd hs n X Y) := by
  have htime := pairSequence_converges (pairingData hw0 hw1 hsmall hd hs) X
    ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy Y)
  have hleft := pairSequence_converges (pairingData hw0 hw1 hsmall hd hs) X ((D).constant unitStage)
  have hright := pairSequence_converges (pairingData hw0 hw1 hsmall hd hs) ((D).constant unitStage) Y
  exact TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))

/-- Scalar subtraction on existing completed objects, not a new vector
centering operation or a separate completed carrier. -/
def completedCenteredScalar (n : Nat) (x y : UnionCompletion hw0 hw1 hsmall hd hs) : RC :=
  RCsub (B x (T n y)) (RCmul (B x U) (B U y))

theorem representativeCenteredMoment_pin (n : Nat) (X Y : (D).Cauchy) :
    completedCenteredScalar hw0 hw1 hsmall hd hs n
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeCenteredMoment hw0 hw1 hsmall hd hs n X Y) := rfl

/-- The SAME prefactor-free q^2 estimate passes through the actual scalar
limits of every supplied union Cauchy representative. -/
theorem representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 hsmall hd hs 2 X X)
      (mul (ofQ' (twoStepRate w hd))
        (representativeCenteredMoment hw0 hw1 hsmall hd hs 0 X X)) :=
  leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs 2 X X)
    (convergesTo_const_mul (ofQ' (twoStepRate w hd))
      (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs 0 X X))
    (fun k => centered_twoStep_bound hw0 hw1 hsmall hd hs (X.seq k))

theorem completedCenteredScalar_twoStep_gap (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    RCle (completedCenteredScalar hw0 hw1 hsmall hd hs 2 x x)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd)))
        (completedCenteredScalar hw0 hw1 hsmall hd hs 0 x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 hsmall hd hs 2 X X,
    representativeCenteredMoment_pin hw0 hw1 hsmall hd hs 0 X X]
  exact representative_twoStep_form_gap hw0 hw1 hsmall hd hs X

/-- The even-time restriction is retained; this does not assert that the
one-step physical-time operator is positive. -/
theorem completedCenteredScalar_even_nonnegative (n : Nat)
    (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    RCnonneg (completedCenteredScalar hw0 hw1 hsmall hd hs (2*n) x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 hsmall hd hs (2*n) X X]
  exact leEv_of_convergesTo_le (convergesTo_const czero)
    (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs (2*n) X X)
    (fun k => centered_even_nonnegative hw0 hw1 hsmall hd hs n (X.seq k))

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
    (x : UnionCompletion hw0 hw1 hsmall hd hs) (hx : B x U = RCzero) :
    completedCenteredScalar hw0 hw1 hsmall hd hs n x x = B x (T n x) := by
  unfold completedCenteredScalar
  rw [hx, rc_zero_mul, rc_sub_zero]

/-- Universal strict form bound on the actual completed unit complement.
Its only vector premise is orthogonality in this SAME completed pairing. -/
theorem completed_twoStep_form_gap (x : UnionCompletion hw0 hw1 hsmall hd hs)
    (hx : B x U = RCzero) :
    RCle (B x (T 2 x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd))) (B x x)) := by
  have h := completedCenteredScalar_twoStep_gap hw0 hw1 hsmall hd hs x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs 2 x hx,
    completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs 0 x hx,
    completedTime_zero] at h
  exact h

theorem completed_even_nonnegative (n : Nat) (x : UnionCompletion hw0 hw1 hsmall hd hs)
    (hx : B x U = RCzero) : RCnonneg (B x (T (2*n) x)) := by
  have h := completedCenteredScalar_even_nonnegative hw0 hw1 hsmall hd hs n x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs (2*n) x hx] at h
  exact h

end YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.representativeCenteredMoment
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.representativeCenteredMomentCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.representativeCenteredMoment_converges
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.completedCenteredScalar
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.representativeCenteredMoment_pin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.representative_twoStep_form_gap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.completedCenteredScalar_twoStep_gap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.completedCenteredScalar_even_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.completedCenteredScalar_of_orthogonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.completed_twoStep_form_gap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap.completed_even_nonnegative
