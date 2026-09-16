/-
# An actual nonzero plaquette excitation in the spatial union completion

Map the existing base-one centered original plaquette vector into the
union completion. The proved mixed-pairing and time pins preserve its
orthogonality, positive local-star norm floor, and original connected
correlator. Its mean and centering are not replaced by a new law.

This is a concrete witness in the SAME union carrier on which the universal
small-nome two-step bound holds. No full observable-algebra coverage, metric
completeness, continuum particle, or physical mass calibration is asserted.
-/

import YMGap.Continuum.BF4SpatialUnionFixedBase
import YMGap.Continuum.BF4SpatialUnionCompletedGap
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation

namespace YMGap.Continuum.BF4SpatialUnionExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation (origin_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
  (spatialCompletedUnit spatialCompletedTime spatialEmbedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4SpatialUnion (Stage ofSpan zeroStage)
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4SpatialUnionCenteredForm
open YMGap.Continuum.BF4SpatialUnionFixedBase
open YMGap.Continuum.BF4SpatialUnionCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- A fixed original fundamental plaquette character, with its support data. -/
def centralStage : Stage :=
  ofSpan 1 (by decide) (faceSpan 1 originFace (origin_physical (by decide)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "old" =>
  Subtype.val (BF4ExactSlabFixedSpatialSpatialCentralExcitation.centralExcitation
    hw0 hw1 1 hsmall hd hs (by decide))
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

/-- The image of the already constructed actual centered base-one vector. -/
def excitation : UnionCompletion hw0 hw1 hsmall hd hs :=
  completionMap hw0 hw1 1 hsmall hd hs (by decide) old

theorem excitation_orthogonal :
    B (excitation hw0 hw1 hsmall hd hs) (completedUnit hw0 hw1 hsmall hd hs) = RCzero := by
  unfold excitation
  rw [← completionMap_unit hw0 hw1 1 hsmall hd hs (by decide), completedInner_map]
  exact BF4ExactSlabFixedSpatialSpatialCentralExcitation.centralExcitation_orthogonal
    hw0 hw1 1 hsmall hd hs (by decide)

/-- The actual union time acts on the image of the same centered plaquette.
The scalar is the union centered moment, pinned to the original base-one law. -/
theorem excitation_correlator_pin (n : Nat) :
    B (excitation hw0 hw1 hsmall hd hs) (T n (excitation hw0 hw1 hsmall hd hs)) =
      Quotient.mk crealSetoid (centeredMoment hw0 hw1 hsmall hd hs n centralStage centralStage) := by
  unfold excitation
  rw [← completionMap_time, completedInner_map]
  exact (BF4ExactSlabFixedSpatialSpatialCentralExcitation.centralExcitation_correlator_pin
    hw0 hw1 1 hsmall hd hs (by decide) n).trans
    (Quotient.sound (centeredMoment_ofSpan hw0 hw1 hsmall hd hs n 1 (by decide)
      (faceSpan 1 originFace (origin_physical (by decide)))
      (faceSpan 1 originFace (origin_physical (by decide)))).symm)

/-- The norm representative and modulus belong to the actual union moment. -/
def excitationNorm : CReal := centeredMoment hw0 hw1 hsmall hd hs 0 centralStage centralStage

def excitationNormCauchy : QCauchy (excitationNorm hw0 hw1 hsmall hd hs).approx :=
  centeredMomentCauchy hw0 hw1 hsmall hd hs 0 centralStage centralStage

theorem excitation_norm_pin :
    B (excitation hw0 hw1 hsmall hd hs) (excitation hw0 hw1 hsmall hd hs) =
      Quotient.mk crealSetoid (excitationNorm hw0 hw1 hsmall hd hs) := by
  simpa only [completedTime_zero] using excitation_correlator_pin hw0 hw1 hsmall hd hs 0

/-- Positive local-star floor; no global-volume penalty is introduced by the map. -/
theorem excitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w)))
      (B (excitation hw0 hw1 hsmall hd hs) (excitation hw0 hw1 hsmall hd hs)) := by
  unfold excitation
  rw [completedInner_map]
  exact BF4ExactSlabFixedSpatialSpatialCentralExcitation.centralExcitation_norm_floor
    hw0 hw1 1 hsmall hd hs (by decide)

theorem completedZero_norm :
    B (embedStage hw0 hw1 hsmall hd hs zeroStage)
      (embedStage hw0 hw1 hsmall hd hs zeroStage) = RCzero := by
  have h := completedInner_map hw0 hw1 1 hsmall hd hs (by decide)
    (spatialEmbedSpan hw0 hw1 1 hsmall hd hs (by decide) (zero 1))
    (spatialEmbedSpan hw0 hw1 1 hsmall hd hs (by decide) (zero 1))
  simp only [completionMap_zero] at h
  exact h.trans (BF4ExactSlabFixedSpatialSpatialCenteredPairing.spatialCompletedZero_norm
    hw0 hw1 1 hsmall hd hs (by decide))

theorem excitation_ne_zero :
    excitation hw0 hw1 hsmall hd hs ≠ embedStage hw0 hw1 hsmall hd hs zeroStage := by
  intro hz
  have h := excitation_norm_floor hw0 hw1 hsmall hd hs
  rw [hz, completedZero_norm] at h
  have hle : starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1) hle)

/-- A nonzero actual vector to which the universal union form bound applies. -/
theorem excitation_twoStep_bound :
    RCle (B (excitation hw0 hw1 hsmall hd hs) (T 2 (excitation hw0 hw1 hsmall hd hs)))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd)))
        (B (excitation hw0 hw1 hsmall hd hs) (excitation hw0 hw1 hsmall hd hs))) :=
  completed_twoStep_form_gap hw0 hw1 hsmall hd hs (excitation hw0 hw1 hsmall hd hs)
    (excitation_orthogonal hw0 hw1 hsmall hd hs)

#print axioms centralStage
#print axioms excitation
#print axioms excitation_orthogonal
#print axioms excitation_correlator_pin
#print axioms excitationNorm
#print axioms excitationNormCauchy
#print axioms excitation_norm_pin
#print axioms excitation_norm_floor
#print axioms completedZero_norm
#print axioms excitation_ne_zero
#print axioms excitation_twoStep_bound

end YMGap.Continuum.BF4SpatialUnionExcitation
