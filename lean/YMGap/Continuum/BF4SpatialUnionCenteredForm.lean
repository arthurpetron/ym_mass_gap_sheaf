/-
# Centered moments on the union of the actual spatial presentation carriers

The scalar uses the same maximum-base union pairing, original unit and
literal physical time. Its Cauchy data are computed from the three actual
pairing representatives. A common-base pin identifies it with the existing
spatialCenteredMoment, in particular at a stage's own positive base.

The prefactor-free two-step bound and even-time positivity therefore hold
unconditionally for every stage, with the same nome-only rate. No uniform
support bound for a stream, orthogonality of approximants, completed form,
or additional observable coverage is assumed or asserted here.
-/

import YMGap.Continuum.BF4SpatialUnion
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap

namespace YMGap.Continuum.BF4SpatialUnionCenteredForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (inclusion_refl)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws (spatialPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate spatialEvenMoment_first_le)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs

/-- Center the actual union pairing with its original normalized unit. -/
def centeredMoment (n : Nat) (x y : Stage) : CReal :=
  sub (P x (time n y)) (mul (P x unitStage) (P unitStage y))

/-- Every modulus comes from the supplied maximum-base pairing data. -/
def centeredMomentCauchy (n : Nat) (x y : Stage) :
    QCauchy (centeredMoment hw0 hw1 hsmall hd hs n x y).approx :=
  let A := P x (time n y)
  let C := P x unitStage
  let E := P unitStage y
  let cA := pairingCauchy hw0 hw1 hsmall hd hs x (time n y)
  let cC := pairingCauchy hw0 hw1 hsmall hd hs x unitStage
  let cE := pairingCauchy hw0 hw1 hsmall hd hs unitStage y
  scalarAddCauchy A (neg (mul C E)) cA
    (scalarNegCauchy (mul C E) (scalarMulCauchy C E cC cE))

attribute [local irreducible] pairing spatialPairing

/-- Any actual common positive base gives the SAME centered scalar, with
the unit and both time labels transported by their proved literal pins. -/
theorem centeredMoment_at_base (n : Nat) (x y : Stage) (larger : Nat)
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    Equiv (centeredMoment hw0 hw1 hsmall hd hs n x y)
      (spatialCenteredMoment hw0 hw1 larger hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive hx) n (atBase x hx) (atBase y hy)) := by
  have hu : 1 ≤ larger := Nat.lt_of_lt_of_le x.positive hx
  have ht := pairing_at_base hw0 hw1 hsmall hd hs x (time n y) larger hx hy
  have hl := pairing_at_base hw0 hw1 hsmall hd hs x unitStage larger hx hu
  have hr := pairing_at_base hw0 hw1 hsmall hd hs unitStage y larger hu hy
  simp only [atBase_time, atBase_unit] at ht hl hr
  have hm : Equiv (mul (P x unitStage) (P unitStage y))
      (mul
        (spatialPairing hw0 hw1 larger hsmall hd hs
          (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (unit larger))
        (spatialPairing hw0 hw1 larger hsmall hd hs
          (Nat.lt_of_lt_of_le x.positive hx) (unit larger) (atBase y hy))) :=
    (CReal.mul_congr_left hl).trans (TrigSignedAdd.mul_congr_right hr)
  exact Equiv_add ht (neg_congr hm)

/-- No larger support bound is required for a stage's diagonal moments. -/
theorem centeredMoment_diagonal_pin (n : Nat) (x : Stage) :
    Equiv (centeredMoment hw0 hw1 hsmall hd hs n x x)
      (spatialCenteredMoment hw0 hw1 x.base hsmall hd hs x.positive n x.value x.value) := by
  simpa only [atBase_self] using
    centeredMoment_at_base hw0 hw1 hsmall hd hs n x x x.base (Nat.le_refl _) (Nat.le_refl _)

/-- Fixed-base pairs retain their original physical presentations. -/
theorem centeredMoment_ofSpan (n base : Nat) (hb : 0<base) (x y : PhysicalSpan base) :
    Equiv (centeredMoment hw0 hw1 hsmall hd hs n (ofSpan base hb x) (ofSpan base hb y))
      (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y) := by
  simpa only [atBase, ofSpan, inclusion_refl] using
    centeredMoment_at_base hw0 hw1 hsmall hd hs n (ofSpan base hb x) (ofSpan base hb y)
      base (Nat.le_refl _) (Nat.le_refl _)

/-- The common nome-dependent q^2 bound holds before imposing orthogonality.
It is therefore usable termwise even when a Cauchy stream has growing bases. -/
theorem centered_twoStep_bound (x : Stage) :
    leEv (centeredMoment hw0 hw1 hsmall hd hs 2 x x)
      (mul (ofQ' (twoStepRate w hd)) (centeredMoment hw0 hw1 hsmall hd hs 0 x x)) :=
  leEv_trans (leEv_of_equiv (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs 2 x))
    (leEv_trans
      (spatialEvenMoment_first_le hw0 hw1 x.base hsmall hd hs x.positive x.value)
      (leEv_of_equiv (TrigSignedAdd.mul_congr_right
        (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs 0 x).symm)))

/-- Site-reflected positivity remains explicitly restricted to even times. -/
theorem centered_even_nonnegative (n : Nat) (x : Stage) :
    leEv czero (centeredMoment hw0 hw1 hsmall hd hs (2*n) x x) :=
  leEv_trans
    (spatialEvenMoment_nonnegative hw0 hw1 x.base hsmall hd hs x.positive x.value n)
    (leEv_of_equiv (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs (2*n) x).symm)

#print axioms centeredMoment
#print axioms centeredMomentCauchy
#print axioms centeredMoment_at_base
#print axioms centeredMoment_diagonal_pin
#print axioms centeredMoment_ofSpan
#print axioms centered_twoStep_bound
#print axioms centered_even_nonnegative

end YMGap.Continuum.BF4SpatialUnionCenteredForm
