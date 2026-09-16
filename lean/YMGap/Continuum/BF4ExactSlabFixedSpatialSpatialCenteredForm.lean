/-
# Centered scalar moments of the actual spatial limiting reflected form

The scalar is the spatial pairing at the literal physical lag, minus the
product of its same two unit coefficients. Its Cauchy data are computed
from those three actual spatial scalars. The recentered joint centered
moments converge to it, so their unconditional even positivity, contraction
and dyadic Cauchy--Schwarz inequality survive the spatial limit.

The original connected-scalar diagonal below uses one common chart and
one selected action/partition for the joint moment and both marginals.
No decay envelope, strict rate, completed centering map, cross-base carrier
identification or continuum statement is assumed or asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime unit physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
  (paddedWidth recenter recenter_time)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance (recenter_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit
  (recenteredScalar spatial_diagonal_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
  (spatialPairing_time_balance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator (connectedScalar)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "B" => spatialPairing hw0 hw1 base hsmall hd hs hb

/-- Computed centering of the same spatial pairing at the actual physical lag. -/
def spatialCenteredMoment (n : Nat) (x y : PhysicalSpan base) : CReal :=
  sub (B x (physicalTime n y)) (mul (B x (unit base)) (B (unit base) y))

/-- Every scalar modulus comes from the actual constructed spatial pairing. -/
def spatialCenteredMomentCauchy (n : Nat) (x y : PhysicalSpan base) :
    QCauchy (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y).approx :=
  let A := B x (physicalTime n y)
  let C := B x (unit base)
  let E := B (unit base) y
  let cA := spatialPairingCauchy hw0 hw1 base hsmall hd hs hb x (physicalTime n y)
  let cC := spatialPairingCauchy hw0 hw1 base hsmall hd hs hb x (unit base)
  let cE := spatialPairingCauchy hw0 hw1 base hsmall hd hs hb (unit base) y
  scalarAddCauchy A (neg (mul C E)) cA
    (scalarNegCauchy (mul C E) (scalarMulCauchy C E cC cE))

/-- Recentring commutes with physical time and preserves the actual unit. -/
theorem jointCenteredMoment_spatial_converges (n : Nat) (x y : PhysicalSpan base) :
    ConvergesTo (fun r => jointCenteredMoment hw0 hw1 (paddedWidth base r) n
      (recenter r x) (recenter r y))
      (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y) := by
  have htime := spatialPairing_converges hw0 hw1 base hsmall hd hs hb x (physicalTime n y)
  have hleft := spatialPairing_converges hw0 hw1 base hsmall hd hs hb x (unit base)
  have hright := spatialPairing_converges hw0 hw1 base hsmall hd hs hb (unit base) y
  have h := TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))
  simpa only [jointCenteredMoment, spatialCenteredMoment, recenter_time, recenter_unit] using h

/-- The moment index counts pairs of physical time steps. -/
def spatialEvenMoment (x : PhysicalSpan base) (k : Nat) : CReal :=
  spatialCenteredMoment hw0 hw1 base hsmall hd hs hb (2*k) x x

theorem spatialEvenMoment_nonnegative (x : PhysicalSpan base) (k : Nat) :
    leEv czero (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x k) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb (2*k) x x)
    (fun r => jointEvenMoment_nonnegative hw0 hw1 (paddedWidth base r) (recenter r x) k)

theorem spatialEvenMoment_le_zero (x : PhysicalSpan base) (k : Nat) :
    leEv (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x k)
      (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x 0) :=
  leEv_of_convergesTo_le
    (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb (2*k) x x)
    (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb 0 x x)
    (fun r => jointEvenMoment_le_zero hw0 hw1 (paddedWidth base r) (recenter r x) k)

/-- Sharp dyadic moment CS on the same limiting form, with no decay premise. -/
theorem spatialEvenMoment_dyadic (x : PhysicalSpan base) (k : Nat) :
    leEv
      (mul (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x k)
        (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x k))
      (mul (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x (k+k))
        (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x 0)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb (2*k) x x)
      (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb (2*k) x x))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb (2*(k+k)) x x)
      (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb 0 x x))
    (fun r => jointEvenMoment_dyadic hw0 hw1 (paddedWidth base r) (recenter r x) k)

attribute [local irreducible] spatialPairing

private theorem chart_diagonal_converges (H : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    ConvergesTo (fun r => ofQ' (recenteredScalar hw0 hw1 base H x y r r r)) (B x y) :=
  CReal.convergesTo_limit_congr
    (spatial_diagonal_converges hw0 hw1 base H x y hx hy hsmall hd hs hb)
    (spatialPairing_chart hw0 hw1 base hsmall hd hs hb x y H hx hy).symm

/-- All three finite moments have the SAME chart, selected action and Z.
The physical lag is fixed while margin, heat stage and time buffer recede. -/
theorem originalConnected_diagonal_converges (n H : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ H) (hy : radius (physicalTime n y).val ≤ H) :
    ConvergesTo (fun r => ofQ'
      (connectedScalar hw0 hw1 (paddedWidth base r) r H
        (recenter r x) (physicalTime n (recenter r y)) r))
      (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y) := by
  have hu : radius (unit base).val ≤ H := Nat.zero_le H
  have htime := chart_diagonal_converges hw0 hw1 base hsmall hd hs hb H x (physicalTime n y) hx hy
  have hleft := chart_diagonal_converges hw0 hw1 base hsmall hd hs hb H x (unit base) hx hu
  have hright := chart_diagonal_converges hw0 hw1 base hsmall hd hs hb H (unit base)
    (physicalTime n y) hu hy
  have hunit : Equiv (B (unit base) (physicalTime n y)) (B (unit base) y) := by
    have h := spatialPairing_time_balance hw0 hw1 base hsmall hd hs hb n (unit base) y
    rw [physicalTime_unit] at h
    exact h.symm
  have hright' := CReal.convergesTo_limit_congr hright hunit
  have h := TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright'))
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro r
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  simp only [connectedScalar, recenteredScalar, recenter_time, recenter_unit]
  exact Q'.eqv_refl _

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.spatialCenteredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.spatialCenteredMomentCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.jointCenteredMoment_spatial_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.spatialEvenMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.spatialEvenMoment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.spatialEvenMoment_le_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.spatialEvenMoment_dyadic
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm.originalConnected_diagonal_converges
