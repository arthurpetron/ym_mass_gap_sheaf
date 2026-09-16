/-
# Actual physical time on the original unit-orthogonal carrier

The SAME completed time balance and fixed normalized unit preserve both
unit coefficients. Pairing separation shows that time fixes the constructed
unit projection, which is also unchanged by first applying time. The actual
centering map therefore commutes with physical time and restricts the
existing semigroup to its unit-orthogonal subtype without choosing data.

The centered mixed-time form is exactly the original completed pairing
minus the product of its two unit coefficients. Site reflection supplies
even-time positivity; the diagonal and even-time bounds have constant one.
The real-scalar commutation law retains the scalar's supplied QCauchy data.

Nome, spatial width and retained heat stage are fixed throughout. No
nonzero excitation, uniqueness or isolation of the fixed unit, one-step
positivity, strict gap, metric completeness or continuum claim is made.
Original finite-covariance placement is a separate consumer, not assumed here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "u" => completedUnit hw0 hw1 width stage
local notation "B" => completedInner hw0 hw1 width stage
local notation "P" => unitProjection hw0 hw1 width stage
local notation "C" => center hw0 hw1 width stage
local notation "T" => completedTime hw0 hw1 width stage

/-- Time preserves the first-slot unit coefficient by actual balance and
the already proved fixed-unit identity. -/
theorem unitCoefficient_time_left (n : Nat) (x : Completion hw0 hw1 width stage) :
    B (T n x) u = B x u := by
  rw [completedInner_time_balance, completedUnit_fixed]

theorem unitCoefficient_time_right (n : Nat) (x : Completion hw0 hw1 width stage) :
    B u (T n x) = B u x := by
  rw [← completedInner_time_balance hw0 hw1 width stage n u x, completedUnit_fixed]

/-- Actual physical time commutes with real scaling whenever the scalar's
approximation modulus is supplied; no modulus is selected from a quotient. -/
theorem completedTime_realSmul (n : Nat) (s : CReal) (cs : QCauchy s.approx)
    (x : Completion hw0 hw1 width stage) :
    T n (completedRealSmul hw0 hw1 width stage s cs x) =
      completedRealSmul hw0 hw1 width stage s cs (T n x) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [completedInner_time_balance, completedInner_realSmul_left,
    completedInner_realSmul_left, completedInner_time_balance]

/-- Projection onto the actual unit is unchanged by first applying time. -/
theorem unitProjection_time (n : Nat) (x : Completion hw0 hw1 width stage) :
    P (T n x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [unitProjection_pairing, unitProjection_pairing, unitCoefficient_time_left]

/-- The whole constructed unit-projection image is fixed by physical time. -/
theorem time_unitProjection (n : Nat) (x : Completion hw0 hw1 width stage) :
    T n (P x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [completedInner_time_balance, unitProjection_pairing, unitProjection_pairing,
    unitCoefficient_time_right]

theorem completedTime_center (n : Nat) (x : Completion hw0 hw1 width stage) :
    T n (C x) = C (T n x) := by
  unfold center
  rw [completedTime_sub, time_unitProjection, unitProjection_time]

/-- Restrict the SAME physical-time map to the actual unit complement.
The guard is proved from coefficient preservation, not a new premise. -/
def unitComplementTime (n : Nat) (x : UnitComplement hw0 hw1 width stage) :
    UnitComplement hw0 hw1 width stage :=
  ⟨T n x.val, (unitCoefficient_time_left hw0 hw1 width stage n x.val).trans x.property⟩

theorem unitComplementTime_val (n : Nat) (x : UnitComplement hw0 hw1 width stage) :
    (unitComplementTime hw0 hw1 width stage n x).val = T n x.val := rfl

theorem unitComplementTime_zero (x : UnitComplement hw0 hw1 width stage) :
    unitComplementTime hw0 hw1 width stage 0 x = x :=
  Subtype.ext (completedTime_zero hw0 hw1 width stage x.val)

theorem unitComplementTime_add (m n : Nat) (x : UnitComplement hw0 hw1 width stage) :
    unitComplementTime hw0 hw1 width stage (m+n) x =
      unitComplementTime hw0 hw1 width stage m
        (unitComplementTime hw0 hw1 width stage n x) :=
  Subtype.ext (completedTime_add hw0 hw1 width stage m n x.val)

/-- The restricted map agrees with centering the same physically advanced
element; this does not introduce a second centered evolution. -/
theorem unitComplementTime_centeredState (n : Nat) (x : Completion hw0 hw1 width stage) :
    unitComplementTime hw0 hw1 width stage n (centeredState hw0 hw1 width stage x) =
      centeredState hw0 hw1 width stage (T n x) :=
  Subtype.ext (completedTime_center hw0 hw1 width stage n x)

/-- The centered time pairing subtracts the SAME two unit coefficients.
No original finite-volume covariance identity is used as a hypothesis. -/
theorem centered_time_pairing (n : Nat) (x y : Completion hw0 hw1 width stage) :
    B (C x) (T n (C y)) = RCsub (B x (T n y)) (RCmul (B x u) (B u y)) := by
  rw [completedTime_center, centered_inner, unitCoefficient_time_right]

/-- Positivity is asserted only for even physical time, as supplied by
the original site-reflected diagonal identity. -/
theorem centered_even_nonnegative (n : Nat) (x : Completion hw0 hw1 width stage) :
    RCnonneg (B (C x) (T (2*n) (C x))) :=
  completedInner_even_nonnegative hw0 hw1 width stage n (C x)

/-- Non-strict even-time comparison with the actual centered diagonal. -/
theorem centered_even_le_identity (n : Nat) (x : Completion hw0 hw1 width stage) :
    RCle (B (C x) (T (2*n) (C x))) (B (C x) (C x)) :=
  completedInner_even_le_identity hw0 hw1 width stage n (C x)

/-- Every physical advance is contractive on centered elements, with
constant one. No strict vacuum-complement rate is asserted. -/
theorem centered_time_norm_le (n : Nat) (x : Completion hw0 hw1 width stage) :
    RCle (B (T n (C x)) (T n (C x))) (B (C x) (C x)) :=
  completedInner_time_contraction hw0 hw1 width stage n (C x)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitCoefficient_time_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitCoefficient_time_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.completedTime_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitProjection_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.time_unitProjection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.completedTime_center
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitComplementTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitComplementTime_val
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitComplementTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitComplementTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.unitComplementTime_centeredState
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.centered_time_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.centered_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.centered_even_le_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime.centered_time_norm_le
