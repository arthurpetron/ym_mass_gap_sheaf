/-
# Strict centered form bound on the actual completed physical carrier

For each supplied physical Cauchy stream, the existing mixed-pairing
limits and continuity of scalar multiplication give the limit of its
centered physical-time moments. The dense bound has already removed its
presentation-dependent prefactor, so passing to these limits requires
no uniform coefficient bound on the stream. Quotient induction then
proves the same two-step bound on every completed centered vector.

The one-step squared-norm consequence uses the actual even-time diagonal
identity. It does not assert positivity of the one-step map. Nome and
width remain fixed, the rate is the actual comparison rate squared, and
no completed representative is selected. No continuum-uniform estimate,
nonzero excitation or physical Hamiltonian gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (seminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection (unitCauchy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion
  (center UnitComplement center_fixed_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime
  (centered_time_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm
  (completedInner_even_diagonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments
  (centeredMoment evenMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate evenMoment_first_le)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage
local notation "B" => completedInner hw0 hw1 width stage
local notation "C" => center hw0 hw1 width stage
local notation "T" => completedTime hw0 hw1 width stage

/-- The centered mixed scalar limit computed from the supplied streams,
using precisely the existing physical-time map and unit stream. -/
def representativeCenteredMoment (n : Nat) (X Y : (D).Cauchy) : CReal :=
  sub (representativeInner hw0 hw1 width stage X
      ((timeNonexpansive hw0 hw1 width stage n).mapCauchy Y))
    (mul (representativeInner hw0 hw1 width stage X
        (unitCauchy hw0 hw1 width stage))
      (representativeInner hw0 hw1 width stage
        (unitCauchy hw0 hw1 width stage) Y))

/-- Arbitrary supplied Cauchy moduli are handled by the existing actual
pairing limits; no presentation cap is assumed uniformly in k. -/
theorem representativeCenteredMoment_converges (n : Nat) (X Y : (D).Cauchy) :
    ConvergesTo
      (fun k => centeredMoment hw0 hw1 width stage n (X.seq k) (Y.seq k))
      (representativeCenteredMoment hw0 hw1 width stage n X Y) := by
  have htime := pairSequence_converges hw0 hw1 width stage X
    ((timeNonexpansive hw0 hw1 width stage n).mapCauchy Y)
  have hleft := pairSequence_converges hw0 hw1 width stage X
    (unitCauchy hw0 hw1 width stage)
  have hright := pairSequence_converges hw0 hw1 width stage
    (unitCauchy hw0 hw1 width stage) Y
  exact TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))

/-- Exact pin to the centered pairing on the SAME completed carrier. -/
theorem representativeCenteredMoment_pin (n : Nat) (X Y : (D).Cauchy) :
    B (C (Quotient.mk (D).completionSetoid X))
        (T n (C (Quotient.mk (D).completionSetoid Y))) =
      Quotient.mk crealSetoid
        (representativeCenteredMoment hw0 hw1 width stage n X Y) := by
  rw [centered_time_pairing]
  rfl

/-- Pass the already prefactor-free dense estimate through the actual
centered scalar limits of a given representative. -/
theorem representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 width stage 2 X X)
      (mul (ofQ' (twoStepRate hw0 hw1 width))
        (representativeCenteredMoment hw0 hw1 width stage 0 X X)) := by
  exact leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 width stage 2 X X)
    (convergesTo_const_mul (ofQ' (twoStepRate hw0 hw1 width))
      (representativeCenteredMoment_converges hw0 hw1 width stage 0 X X))
    (fun k => evenMoment_first_le hw0 hw1 width stage (X.seq k))

/-- The actual strict two-step form bound holds on all completed centered
vectors, without assuming density or selecting a representative. -/
theorem completed_twoStep_form_gap (v : Completion hw0 hw1 width stage) :
    RCle (B (C v) (T 2 (C v)))
      (RCscale (twoStepRate hw0 hw1 width) (B (C v) (C v))) := by
  refine Quotient.inductionOn v ?_
  intro X
  have htwo := representativeCenteredMoment_pin hw0 hw1 width stage 2 X X
  have hzero := representativeCenteredMoment_pin hw0 hw1 width stage 0 X X
  rw [completedTime_zero] at hzero
  rw [htwo, hzero]
  exact representative_twoStep_form_gap hw0 hw1 width stage X

/-- The same strict rate bounds the one-step squared norm. This uses the
even-time form identity, not a claim that one-step physical time is positive. -/
theorem completed_oneStep_norm_gap (v : Completion hw0 hw1 width stage) :
    RCle (B (T 1 (C v)) (T 1 (C v)))
      (RCscale (twoStepRate hw0 hw1 width) (B (C v) (C v))) := by
  have h := completed_twoStep_form_gap hw0 hw1 width stage v
  have hdiag := completedInner_even_diagonal hw0 hw1 width stage 1 (C v)
  change B (C v) (T 2 (C v)) = B (T 1 (C v)) (T 1 (C v)) at hdiag
  rw [hdiag] at h
  exact h

/-- Restriction to the already defined actual unit-orthogonal subtype. -/
theorem unitComplement_twoStep_form_gap (x : UnitComplement hw0 hw1 width stage) :
    RCle (B x.val (T 2 x.val))
      (RCscale (twoStepRate hw0 hw1 width) (B x.val x.val)) := by
  have h := completed_twoStep_form_gap hw0 hw1 width stage x.val
  have hc := (center_fixed_iff hw0 hw1 width stage x.val).mpr x.property
  rw [hc] at h
  exact h

theorem unitComplement_oneStep_norm_gap (x : UnitComplement hw0 hw1 width stage) :
    RCle (B (T 1 x.val) (T 1 x.val))
      (RCscale (twoStepRate hw0 hw1 width) (B x.val x.val)) := by
  have h := completed_oneStep_norm_gap hw0 hw1 width stage x.val
  have hc := (center_fixed_iff hw0 hw1 width stage x.val).mpr x.property
  rw [hc] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.representativeCenteredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.representativeCenteredMoment_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.representativeCenteredMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.representative_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.completed_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.completed_oneStep_norm_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.unitComplement_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCenteredGap.unitComplement_oneStep_norm_gap
