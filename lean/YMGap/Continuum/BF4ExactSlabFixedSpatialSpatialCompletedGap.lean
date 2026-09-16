/-
# Strict two-step form bound on the actual spatial Cauchy carrier

Every supplied spatial Cauchy stream has three actual completed-pairing
limits defining its centered moment. The already prefactor-free dense
bound passes through these same scalar limits without a uniform bound on
presentation coefficients. Quotient induction then covers EVERY vector
orthogonal to the actual unit of this SAME SpatialCompletion.

The rate is rho(w)^2, independent of the positive base size, under the
displayed small-nome guards. The two-step map is actual discrete physical
time, not heat-bath dynamics. This is not metric completeness, a continuum
Hamiltonian, unrestricted coupling control or a physical mass calibration.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm (spatialSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate spatialEvenMoment_first_le)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)

open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 base hsmall hd hs hb
local notation "T" => spatialCompletedTime hw0 hw1 base hsmall hd hs hb
local notation "U" => spatialCompletedUnit hw0 hw1 base hsmall hd hs hb

/-- Scalar centering of the actual representative pairing, using the
literal spatial-time map and the constant stream of the original unit. -/
def representativeCenteredMoment (n : Nat) (X Y : (D).Cauchy) : CReal :=
  sub (representativeInner hw0 hw1 base hsmall hd hs hb X
      ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy Y))
    (mul (representativeInner hw0 hw1 base hsmall hd hs hb X ((D).constant (unit base)))
      (representativeInner hw0 hw1 base hsmall hd hs hb ((D).constant (unit base)) Y))

/-- All approximation moduli are data from the three actual pairing
representatives; the product ceiling is computed by the scalar algebra. -/
def representativeCenteredMomentCauchy (n : Nat) (X Y : (D).Cauchy) :
    QCauchy (representativeCenteredMoment hw0 hw1 base hsmall hd hs hb n X Y).approx :=
  let A := representativeInner hw0 hw1 base hsmall hd hs hb X
    ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy Y)
  let L := representativeInner hw0 hw1 base hsmall hd hs hb X ((D).constant (unit base))
  let R := representativeInner hw0 hw1 base hsmall hd hs hb ((D).constant (unit base)) Y
  let cA := representativeInnerCauchy hw0 hw1 base hsmall hd hs hb X
    ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy Y)
  let cL := representativeInnerCauchy hw0 hw1 base hsmall hd hs hb X ((D).constant (unit base))
  let cR := representativeInnerCauchy hw0 hw1 base hsmall hd hs hb ((D).constant (unit base)) Y
  scalarAddCauchy A (neg (mul L R)) cA
    (scalarNegCauchy (mul L R) (scalarMulCauchy L R cL cR))

/-- The physical lag n is fixed while the supplied Cauchy index k varies.
No bound on the coefficient presentations is assumed uniformly in k. -/
theorem representativeCenteredMoment_converges (n : Nat) (X Y : (D).Cauchy) :
    ConvergesTo
      (fun k => spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n (X.seq k) (Y.seq k))
      (representativeCenteredMoment hw0 hw1 base hsmall hd hs hb n X Y) := by
  have htime := pairSequence_converges hw0 hw1 base hsmall hd hs hb X
    ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy Y)
  have hleft := pairSequence_converges hw0 hw1 base hsmall hd hs hb X ((D).constant (unit base))
  have hright := pairSequence_converges hw0 hw1 base hsmall hd hs hb ((D).constant (unit base)) Y
  exact TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))

/-- Scalar subtraction on existing completed objects, not a new vector
centering operation or a separate completed carrier. -/
def completedCenteredScalar (n : Nat) (x y : SpatialCompletion hw0 hw1 base hsmall hd hs hb) : RC :=
  RCsub (B x (T n y)) (RCmul (B x U) (B U y))

theorem representativeCenteredMoment_pin (n : Nat) (X Y : (D).Cauchy) :
    completedCenteredScalar hw0 hw1 base hsmall hd hs hb n
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeCenteredMoment hw0 hw1 base hsmall hd hs hb n X Y) := rfl

/-- The SAME prefactor-free q^2 estimate passes through the actual scalar
limits of every supplied spatial Cauchy representative. -/
theorem representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 base hsmall hd hs hb 2 X X)
      (mul (ofQ' (twoStepRate w hd))
        (representativeCenteredMoment hw0 hw1 base hsmall hd hs hb 0 X X)) :=
  leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 base hsmall hd hs hb 2 X X)
    (convergesTo_const_mul (ofQ' (twoStepRate w hd))
      (representativeCenteredMoment_converges hw0 hw1 base hsmall hd hs hb 0 X X))
    (fun k => spatialEvenMoment_first_le hw0 hw1 base hsmall hd hs hb (X.seq k))

theorem completedCenteredScalar_twoStep_gap (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    RCle (completedCenteredScalar hw0 hw1 base hsmall hd hs hb 2 x x)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd)))
        (completedCenteredScalar hw0 hw1 base hsmall hd hs hb 0 x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 base hsmall hd hs hb 2 X X,
    representativeCenteredMoment_pin hw0 hw1 base hsmall hd hs hb 0 X X]
  exact representative_twoStep_form_gap hw0 hw1 base hsmall hd hs hb X

/-- The even-time restriction is retained; this does not assert that the
one-step physical-time operator is positive. -/
theorem completedCenteredScalar_even_nonnegative (n : Nat)
    (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    RCnonneg (completedCenteredScalar hw0 hw1 base hsmall hd hs hb (2*n) x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 base hsmall hd hs hb (2*n) X X]
  exact leEv_of_convergesTo_le (convergesTo_const czero)
    (representativeCenteredMoment_converges hw0 hw1 base hsmall hd hs hb (2*n) X X)
    (fun k => spatialEvenMoment_nonnegative hw0 hw1 base hsmall hd hs hb (X.seq k) n)

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
    (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) (hx : B x U = RCzero) :
    completedCenteredScalar hw0 hw1 base hsmall hd hs hb n x x = B x (T n x) := by
  unfold completedCenteredScalar
  rw [hx, rc_zero_mul, rc_sub_zero]

/-- Universal strict form bound on the actual completed unit complement.
Its only vector premise is orthogonality in this SAME completed pairing. -/
theorem completed_twoStep_form_gap (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb)
    (hx : B x U = RCzero) :
    RCle (B x (T 2 x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd))) (B x x)) := by
  have h := completedCenteredScalar_twoStep_gap hw0 hw1 base hsmall hd hs hb x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 base hsmall hd hs hb 2 x hx,
    completedCenteredScalar_of_orthogonal hw0 hw1 base hsmall hd hs hb 0 x hx,
    spatialCompletedTime_zero] at h
  exact h

theorem completed_even_nonnegative (n : Nat) (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb)
    (hx : B x U = RCzero) : RCnonneg (B x (T (2*n) x)) := by
  have h := completedCenteredScalar_even_nonnegative hw0 hw1 base hsmall hd hs hb n x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 base hsmall hd hs hb (2*n) x hx] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.representativeCenteredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.representativeCenteredMomentCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.representativeCenteredMoment_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.completedCenteredScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.representativeCenteredMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.representative_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.completedCenteredScalar_twoStep_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.completedCenteredScalar_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.completedCenteredScalar_of_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.completed_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap.completed_even_nonnegative
