/-
# A nonzero original excitation in the actual joint unit complement

The original central plaquette character is centered by its explicit
rational-approximation stream. Its completed norm is exactly the original
joint variance, so the proved positive centralFraction is an actual norm
floor, not only a formal Gram determinant. The vector belongs to the SAME
unit complement on which the actual physical-time form bound holds.

Width must be positive. The floor and contraction rate depend on width
and nome; no spatially uniform or physical mass bound is inferred. The
origin plaquette is not a recentered bulk-exhaustion probe. This is neither
a continuum excitation nor a full Hilbert/OS reconstruction.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter (span)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (hwidth : 0 < width)

local notation "x" => span width hwidth
local notation "B" => completedInner hw0 hw1 width

/-- Explicitly constructed, unit-orthogonal vector in the original carrier. -/
def centralExcitation : UnitComplement hw0 hw1 width :=
  ⟨centeredVector hw0 hw1 width x, centeredVector_orthogonal hw0 hw1 width x⟩

/-- The norm representative retains the already computed scalar modulus. -/
def excitationNorm : CReal := jointCenteredMoment hw0 hw1 width 0 x x

def excitationNormCauchy : QCauchy (excitationNorm hw0 hw1 width hwidth).approx :=
  jointCenteredMomentCauchy hw0 hw1 width 0 x x

theorem centralExcitation_norm_pin :
    B (centralExcitation hw0 hw1 width hwidth).val
      (centralExcitation hw0 hw1 width hwidth).val =
      Quotient.mk crealSetoid (excitationNorm hw0 hw1 width hwidth) :=
  centeredVector_pairing hw0 hw1 width x x

theorem centralExcitation_orthogonal :
    B (centralExcitation hw0 hw1 width hwidth).val (jointCompletedUnit hw0 hw1 width) = RCzero :=
  (centralExcitation hw0 hw1 width hwidth).property

/-- An explicit positive norm floor for an ACTUAL vector, after both
heat-cutoff and time-boundary removal at fixed positive spatial width. -/
theorem centralExcitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (centralFraction hw0 hw1 width)))
      (B (centralExcitation hw0 hw1 width hwidth).val
        (centralExcitation hw0 hw1 width hwidth).val) := by
  rw [centralExcitation_norm_pin]
  exact central_joint_variance_floor hw0 hw1 width hwidth

theorem centralExcitation_ne_zero :
    (centralExcitation hw0 hw1 width hwidth).val ≠
      jointEmbedSpan hw0 hw1 width (zero width) := by
  intro hz
  have h := centralExcitation_norm_floor hw0 hw1 width hwidth
  rw [hz, jointCompletedZero_norm] at h
  have hle : centralFraction hw0 hw1 width ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (centralFraction_positive hw0 hw1 width) hle)

/-- The SAME vector and SAME time map realize the original central
connected correlation at every discrete physical lag. -/
theorem centralExcitation_correlator_pin (n : Nat) :
    B (centralExcitation hw0 hw1 width hwidth).val
      (jointCompletedTime hw0 hw1 width n (centralExcitation hw0 hw1 width hwidth).val) =
      Quotient.mk crealSetoid (jointCenteredMoment hw0 hw1 width n x x) :=
  centeredVector_time_pairing hw0 hw1 width n x x

theorem centralExcitation_twoStep_bound :
    RCle (B (centralExcitation hw0 hw1 width hwidth).val
      (jointCompletedTime hw0 hw1 width 2 (centralExcitation hw0 hw1 width hwidth).val))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (B (centralExcitation hw0 hw1 width hwidth).val
          (centralExcitation hw0 hw1 width hwidth).val)) :=
  completed_twoStep_form_gap hw0 hw1 width _ (centralExcitation_orthogonal hw0 hw1 width hwidth)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.centralExcitation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.excitationNorm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.excitationNormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.centralExcitation_norm_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.centralExcitation_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.centralExcitation_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.centralExcitation_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.centralExcitation_correlator_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralExcitation.centralExcitation_twoStep_bound
