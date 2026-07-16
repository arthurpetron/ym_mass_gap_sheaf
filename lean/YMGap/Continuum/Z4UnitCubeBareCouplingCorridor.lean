/-
# The exact unit-cube bare-coupling corridor

The activity-matching unit-cube map is the exact rational polynomial

    B(w) = 2 * w^4.

This module records its constructive coarse-direction dynamics.  The map is
monotone on nonnegative couplings, and two iterations send the entire checked
window `0 <= w <= 1/2` below the derived strong-coupling anchor `1/400`.
Consequently every character coefficient and every unnormalized physical
term, partition, event numerator, support activity, and pinned layer at the
twice-blocked coupling is controlled by the already proved anchor regime,
uniformly in representation cutoff and box volume.

The last section is a formal scope fence.  Monotonicity of numerator and
denominator does not imply monotonicity of their normalized quotient, and
`B` strictly decreases the anchor itself.  Hence this bare coarse corridor is
neither a normalized physical block-spin pushforward nor an inverse/fine
asymptotically-free trajectory.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
import YMGap.Continuum.Z4NormalizedOccurrenceMonotonicityFence

namespace YMGap.Continuum.Z4UnitCubeBareCouplingCorridor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CouplingParametricMonotonicity
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4NormalizedOccurrenceMonotonicityFence
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

/-! ## 1. Constructive iteration of the exact bare map -/

def unitCubeBlockCouplingIterate : Nat → Q' → Q'
  | 0, coupling => coupling
  | steps + 1, coupling =>
      unitCubeBlockCoupling
        (unitCubeBlockCouplingIterate steps coupling)

private theorem ringPow_mono_base
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) :
    ∀ exponent : Nat, lower ^ exponent ≤ upper ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hupper : (0 : Q') ≤ upper :=
        Q'.le_trans' _ _ _ hlower hle
      show lower * lower ^ exponent ≤ upper * upper ^ exponent
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right
          lower upper (lower ^ exponent) hle
          (Q'.pow_nonneg lower hlower exponent))
        (Q'.mul_le_mul_of_nonneg_left
          (lower ^ exponent) (upper ^ exponent) upper
          (ringPow_mono_base hlower hle exponent) hupper)

theorem unitCubeBlockCoupling_mono
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) :
    unitCubeBlockCoupling lower ≤ unitCubeBlockCoupling upper := by
  unfold unitCubeBlockCoupling
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (ringPow_mono_base hlower hle 4) (by decide)

theorem unitCubeBlockCouplingIterate_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling) :
    ∀ steps, (0 : Q') ≤
      unitCubeBlockCouplingIterate steps coupling
  | 0 => hcoupling
  | steps + 1 =>
      unitCubeBlockCoupling_nonnegative
        (unitCubeBlockCouplingIterate_nonnegative hcoupling steps)

theorem unitCubeBlockCouplingIterate_mono
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) :
    ∀ steps,
      unitCubeBlockCouplingIterate steps lower ≤
        unitCubeBlockCouplingIterate steps upper
  | 0 => hle
  | steps + 1 =>
      unitCubeBlockCoupling_mono
        (unitCubeBlockCouplingIterate_nonnegative hlower steps)
        (unitCubeBlockCouplingIterate_mono hlower hle steps)

/-! ## 2. Two coarse steps enter the checked anchor regime -/

/-- The whole strong-coupling character window enters the derived anchor
corridor after two exact activity-matching coarse steps. -/
theorem unitCubeBlockCouplingIterate_two_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide)) :
    unitCubeBlockCouplingIterate 2 coupling ≤ anchorCoupling := by
  have hmono := unitCubeBlockCouplingIterate_mono
    hcoupling hleHalf 2
  have hendpoint :
      unitCubeBlockCouplingIterate 2
          (Q'.mkPos 1 2 (by decide)) ≤ anchorCoupling := by
    unfold unitCubeBlockCouplingIterate unitCubeBlockCoupling anchorCoupling
    decide
  exact Q'.le_trans' _ _ _ hmono hendpoint

/-- Once two coarse steps have entered the checked anchor corridor, every
later bare coarse iterate remains there.  This is a forward coarse-direction
invariant corridor; it is not an inverse/fine ultraviolet trajectory. -/
theorem unitCubeBlockCouplingIterate_two_add_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide)) :
    ∀ extra : Nat,
      unitCubeBlockCouplingIterate (2 + extra) coupling ≤
        anchorCoupling
  | 0 => unitCubeBlockCouplingIterate_two_le_anchor hcoupling hleHalf
  | extra + 1 => by
      change unitCubeBlockCoupling
          (unitCubeBlockCouplingIterate (2 + extra) coupling) ≤
        anchorCoupling
      exact Q'.le_trans' _ _ _
        (unitCubeBlockCoupling_mono
          (unitCubeBlockCouplingIterate_nonnegative hcoupling (2 + extra))
          (unitCubeBlockCouplingIterate_two_add_le_anchor
            hcoupling hleHalf extra))
        anchor_unitCubeBlockCoupling_le

theorem coeffW_twoBlockSteps_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (spin : Nat) :
    coeffW (unitCubeBlockCouplingIterate 2 coupling) spin ≤
      coeffW anchorCoupling spin := by
  exact coeffW_mono_w
    (unitCubeBlockCouplingIterate_nonnegative hcoupling 2)
    (unitCubeBlockCouplingIterate_two_le_anchor hcoupling hleHalf)
    spin

theorem physicalPartition_twoBlockSteps_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (cutoff volume : Nat) :
    parametricKPhysicalPartition
        (unitCubeBlockCouplingIterate 2 coupling) cutoff volume ≤
      parametricKPhysicalPartition anchorCoupling cutoff volume := by
  exact parametricKPhysicalPartition_mono_coupling
    (unitCubeBlockCouplingIterate_nonnegative hcoupling 2)
    (unitCubeBlockCouplingIterate_two_le_anchor hcoupling hleHalf)
    cutoff volume

theorem eventNumerator_twoBlockSteps_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (cutoff volume : Nat) (event : EdgeLabelling → Bool) :
    parametricKEventNumerator
        (unitCubeBlockCouplingIterate 2 coupling)
        cutoff volume event ≤
      parametricKEventNumerator anchorCoupling
        cutoff volume event := by
  exact parametricKEventNumerator_mono_coupling
    (unitCubeBlockCouplingIterate_nonnegative hcoupling 2)
    (unitCubeBlockCouplingIterate_two_le_anchor hcoupling hleHalf)
    cutoff volume event

theorem physicalPartition_afterTwoBlockSteps_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (extra cutoff volume : Nat) :
    parametricKPhysicalPartition
        (unitCubeBlockCouplingIterate (2 + extra) coupling)
        cutoff volume ≤
      parametricKPhysicalPartition anchorCoupling cutoff volume := by
  exact parametricKPhysicalPartition_mono_coupling
    (unitCubeBlockCouplingIterate_nonnegative hcoupling (2 + extra))
    (unitCubeBlockCouplingIterate_two_add_le_anchor
      hcoupling hleHalf extra)
    cutoff volume

theorem eventNumerator_afterTwoBlockSteps_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (extra cutoff volume : Nat) (event : EdgeLabelling → Bool) :
    parametricKEventNumerator
        (unitCubeBlockCouplingIterate (2 + extra) coupling)
        cutoff volume event ≤
      parametricKEventNumerator anchorCoupling
        cutoff volume event := by
  exact parametricKEventNumerator_mono_coupling
    (unitCubeBlockCouplingIterate_nonnegative hcoupling (2 + extra))
    (unitCubeBlockCouplingIterate_two_add_le_anchor
      hcoupling hleHalf extra)
    cutoff volume event

theorem supportActivity_twoBlockSteps_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (cutoff volume : Nat) (support : List Nat) :
    couplingParametricKSupportActivity
        (unitCubeBlockCouplingIterate 2 coupling)
        cutoff volume support ≤
      parametricKSupportActivity cutoff volume support := by
  exact couplingParametricKSupportActivity_le_anchor
    (unitCubeBlockCouplingIterate_nonnegative hcoupling 2)
    (unitCubeBlockCouplingIterate_two_le_anchor hcoupling hleHalf)
    cutoff volume support

theorem supportActivity_afterTwoBlockSteps_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (extra cutoff volume : Nat) (support : List Nat) :
    couplingParametricKSupportActivity
        (unitCubeBlockCouplingIterate (2 + extra) coupling)
        cutoff volume support ≤
      parametricKSupportActivity cutoff volume support := by
  exact couplingParametricKSupportActivity_le_anchor
    (unitCubeBlockCouplingIterate_nonnegative hcoupling (2 + extra))
    (unitCubeBlockCouplingIterate_two_add_le_anchor
      hcoupling hleHalf extra)
    cutoff volume support

theorem pinnedLayer_twoBlockSteps_le_half
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (cutoff volume rootId : Nat) :
    couplingParametricKCanonicalPinnedLayerActivity
        (unitCubeBlockCouplingIterate 2 coupling)
        cutoff volume rootId ≤
      Q'.mkPos 1 2 (by decide) := by
  exact couplingParametricKCanonicalPinnedLayerActivity_le_half
    (unitCubeBlockCouplingIterate_nonnegative hcoupling 2)
    (unitCubeBlockCouplingIterate_two_le_anchor hcoupling hleHalf)
    cutoff volume rootId

/-- Every later bare coarse iterate inherits the complete anchor pinned-layer
bound, uniformly in cutoff, volume, and marked face. -/
theorem pinnedLayer_afterTwoBlockSteps_le_half
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide))
    (extra cutoff volume rootId : Nat) :
    couplingParametricKCanonicalPinnedLayerActivity
        (unitCubeBlockCouplingIterate (2 + extra) coupling)
        cutoff volume rootId ≤
      Q'.mkPos 1 2 (by decide) := by
  exact couplingParametricKCanonicalPinnedLayerActivity_le_half
    (unitCubeBlockCouplingIterate_nonnegative hcoupling (2 + extra))
    (unitCubeBlockCouplingIterate_two_add_le_anchor
      hcoupling hleHalf extra)
    cutoff volume rootId

/-! ## 3. Scope fences: no quotient monotonicity and no fine trajectory -/

/-- The generic exact-rational counterexample remains applicable: simultaneous
monotonicity of every state weight, the event numerator, and the partition
does not supply monotonicity of the normalized event probability. -/
theorem bare_unnormalized_corridor_does_not_supply_normalized_monotonicity :
    ¬ toyRootOccurrenceProbability lowerCoupling
        lowerCoupling_nonnegative ≤
      toyRootOccurrenceProbability upperCoupling (by decide) :=
  termwise_mono_does_not_normalize

/-- The exact bare block map points strictly toward stronger coupling at the
anchor.  In particular it cannot be reinterpreted as a nondecreasing
inverse/fine ultraviolet step without constructing and proving a different
map. -/
theorem anchor_not_le_unitCubeBlockCoupling :
    ¬ anchorCoupling ≤ unitCubeBlockCoupling anchorCoupling := by
  unfold unitCubeBlockCoupling anchorCoupling
  decide

#print axioms unitCubeBlockCoupling_mono
#print axioms unitCubeBlockCouplingIterate_nonnegative
#print axioms unitCubeBlockCouplingIterate_mono
#print axioms unitCubeBlockCouplingIterate_two_le_anchor
#print axioms unitCubeBlockCouplingIterate_two_add_le_anchor
#print axioms coeffW_twoBlockSteps_le_anchor
#print axioms physicalPartition_twoBlockSteps_le_anchor
#print axioms eventNumerator_twoBlockSteps_le_anchor
#print axioms physicalPartition_afterTwoBlockSteps_le_anchor
#print axioms eventNumerator_afterTwoBlockSteps_le_anchor
#print axioms supportActivity_twoBlockSteps_le_anchor
#print axioms supportActivity_afterTwoBlockSteps_le_anchor
#print axioms pinnedLayer_twoBlockSteps_le_half
#print axioms pinnedLayer_afterTwoBlockSteps_le_half
#print axioms bare_unnormalized_corridor_does_not_supply_normalized_monotonicity
#print axioms anchor_not_le_unitCubeBlockCoupling

end YMGap.Continuum.Z4UnitCubeBareCouplingCorridor
