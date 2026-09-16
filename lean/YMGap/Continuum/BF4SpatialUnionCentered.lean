/-
# All-vector centering on the original spatial union completion

Subtract the computed unit projection on the SAME completed carrier.
The resulting idempotent is exactly orthogonal centering for the actual
mixed pairing. Its image is the already constructed strict unit complement;
its time correlations are the already constructed connected scalar moments.
No additional analytic premise, full observable-density, or continuum claim.
-/

import YMGap.Continuum.BF4SpatialUnionUnitProjection
import YMGap.Continuum.BF4SpatialUnionUnitComplement

namespace YMGap.Continuum.BF4SpatialUnionCentered

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionUnitProjection
open YMGap.Continuum.BF4SpatialUnionUnitComplement
open YMGap.Continuum.BF4SpatialUnionCompletedGap
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "P" => unitProjection hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

def center (x : V) : V := completedSub hw0 hw1 hsmall hd hs x (P x)

def centerCauchy (X : (D).Cauchy) : (D).Cauchy :=
  differenceCauchy hw0 hw1 hsmall hd hs X (unitProjectionCauchy hw0 hw1 hsmall hd hs X)

theorem center_mk (X : (D).Cauchy) :
    center hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (centerCauchy hw0 hw1 hsmall hd hs X) := rfl

theorem center_pairing (x y : V) :
    B (center hw0 hw1 hsmall hd hs x) y = RCsub (B x y) (RCmul (B x U) (B U y)) := by
  unfold center
  rw [completedInner_sub_left, unitProjection_pairing]

theorem center_selfAdjoint (x y : V) :
    B (center hw0 hw1 hsmall hd hs x) y = B x (center hw0 hw1 hsmall hd hs y) := by
  unfold center
  rw [completedInner_sub_left, completedInner_sub_right, unitProjection_selfAdjoint]

theorem center_orthogonal (x : V) : B (center hw0 hw1 hsmall hd hs x) U = RCzero := by
  unfold center
  rw [completedInner_sub_left, unitProjection_coefficient, rc_sub_self]

theorem center_fixed_iff (x : V) :
    center hw0 hw1 hsmall hd hs x = x ↔ B x U = RCzero := by
  constructor
  · intro h
    rw [← h]
    exact center_orthogonal hw0 hw1 hsmall hd hs x
  · intro h
    unfold center
    rw [(unitProjection_zero_iff hw0 hw1 hsmall hd hs x).mpr h, completedSub_zero]

theorem center_idempotent (x : V) :
    center hw0 hw1 hsmall hd hs (center hw0 hw1 hsmall hd hs x) = center hw0 hw1 hsmall hd hs x :=
  (center_fixed_iff hw0 hw1 hsmall hd hs _).mpr (center_orthogonal hw0 hw1 hsmall hd hs x)

theorem center_decomposition (x : V) :
    completedAdd hw0 hw1 hsmall hd hs (center hw0 hw1 hsmall hd hs x) (P x) = x :=
  completedSub_add_cancel hw0 hw1 hsmall hd hs x (P x)

theorem center_add (x y : V) :
    center hw0 hw1 hsmall hd hs (completedAdd hw0 hw1 hsmall hd hs x y) =
      completedAdd hw0 hw1 hsmall hd hs (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [center_selfAdjoint, completedInner_add_left, completedInner_add_left,
    center_selfAdjoint, center_selfAdjoint]

theorem center_smul (c : Q') (x : V) :
    center hw0 hw1 hsmall hd hs (completedSmul hw0 hw1 hsmall hd hs c x) =
      completedSmul hw0 hw1 hsmall hd hs c (center hw0 hw1 hsmall hd hs x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [center_selfAdjoint, completedInner_smul_left, completedInner_smul_left, center_selfAdjoint]

theorem center_sub (x y : V) :
    center hw0 hw1 hsmall hd hs (completedSub hw0 hw1 hsmall hd hs x y) =
      completedSub hw0 hw1 hsmall hd hs (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [center_selfAdjoint, completedInner_sub_left, completedInner_sub_left,
    center_selfAdjoint, center_selfAdjoint]

theorem centered_inner (x y : V) :
    B (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs y) =
      RCsub (B x y) (RCmul (B x U) (B U y)) := by
  rw [center_selfAdjoint, center_idempotent, ← center_selfAdjoint, center_pairing]

/-- Exact mixed Pythagoras on the existing carrier and existing form. -/
theorem orthogonal_decomposition_inner (x y : V) :
    RCadd (B (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs y))
      (B (P x) (P y)) = B x y := by
  rw [centered_inner, unitProjection_inner, rc_sub_add]

theorem center_norm_le (x : V) :
    RCle (B (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs x)) (B x x) := by
  have h := RCadd_le_add
    (RCle_refl (B (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs x)))
    (completedInner_nonnegative hw0 hw1 hsmall hd hs (P x))
  rw [rc_add_zero, orthogonal_decomposition_inner] at h
  exact h

theorem center_nonexpansive (x y : V) :
    RCle
      (B (completedSub hw0 hw1 hsmall hd hs (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs y))
        (completedSub hw0 hw1 hsmall hd hs (center hw0 hw1 hsmall hd hs x) (center hw0 hw1 hsmall hd hs y)))
      (B (completedSub hw0 hw1 hsmall hd hs x y) (completedSub hw0 hw1 hsmall hd hs x y)) := by
  rw [← center_sub]
  exact center_norm_le hw0 hw1 hsmall hd hs (completedSub hw0 hw1 hsmall hd hs x y)

/-- This targets the previously constructed sector, not a duplicate subtype. -/
def centeredState (x : V) : UnitComplement hw0 hw1 hsmall hd hs :=
  ⟨center hw0 hw1 hsmall hd hs x, center_orthogonal hw0 hw1 hsmall hd hs x⟩

theorem centeredState_fixes (x : UnitComplement hw0 hw1 hsmall hd hs) :
    centeredState hw0 hw1 hsmall hd hs x.val = x :=
  Subtype.ext ((center_fixed_iff hw0 hw1 hsmall hd hs x.val).mpr x.property)

theorem completedTime_center (n : Nat) (x : V) :
    T n (center hw0 hw1 hsmall hd hs x) = center hw0 hw1 hsmall hd hs (T n x) := by
  unfold center
  rw [completedTime_sub, time_unitProjection, unitProjection_time]

/-- Every connected scalar is realized by the SAME centered vectors and time. -/
theorem centered_time_pairing (n : Nat) (x y : V) :
    B (center hw0 hw1 hsmall hd hs x) (T n (center hw0 hw1 hsmall hd hs y)) =
      completedCenteredScalar hw0 hw1 hsmall hd hs n x y := by
  rw [completedTime_center, centered_inner]
  unfold completedCenteredScalar
  rw [← completedInner_time_balance hw0 hw1 hsmall hd hs n U y, completedUnit_fixed]

end YMGap.Continuum.BF4SpatialUnionCentered

#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.centerCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_mk
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_pairing
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_selfAdjoint
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_orthogonal
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_fixed_iff
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_idempotent
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_decomposition
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_add
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_smul
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_sub
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.centered_inner
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.orthogonal_decomposition_inner
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_norm_le
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.center_nonexpansive
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.centeredState
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.centeredState_fixes
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.completedTime_center
#print axioms YMGap.Continuum.BF4SpatialUnionCentered.centered_time_pairing
