/-
# A fixed old-row-floor envelope for symmetric cutoff-two cross traffic

The symmetric old-to-new reduction has a common denominator: the stationary
weight of its old endpoint.  This module transports the already proved
cutoff-two persistent row floor from the explicit embedded old index to every
member of the later old block.  Since division of a nonnegative rational is
antitone in its positive denominator, reverse cross traffic divided by the
actual old weight is bounded by the same traffic divided by one fixed positive
row floor.

This produces a scale-independent envelope for the symmetric relative cross
load.  A Type-level certificate that pays this larger envelope by the physical
conditional transition automatically supplies the ratio-free conditional
certificate, and hence the old-to-new field of the three-block compiler.

The envelope payment is not inhabited here.  No old-to-new or new--new
capacity estimate, thermodynamic/continuum construction, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The persistent cutoff-two floor applies to every later old state -/

/-- Every member of the later old block has stationary weight at least the
single positive cutoff-two pulled row floor. -/
theorem cutoffTwoPulledUniformPositiveRowFloor_le_oldWeight
    {later source : Nat}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (hsource : source ∈ cutoffTwoEdgeLoadOldStates later) :
    cutoffTwoPulledUniformPositiveRowFloor ≤
      cutoffTwoEdgeLoadWeight later source := by
  have hbaseLater : 2 ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hsourceImage : source ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0 :=
    (mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (half := 0) hbaseLater).1 hsource
  rcases List.mem_map.mp hsourceImage with
    ⟨baseIndex, hbaseIndex, hsourceMap⟩
  have hfloor :=
    cutoffTwoPulledUniformPositiveRowFloor_le_weight
      hlater hbaseIndex
  unfold cutoffTwoEdgeLoadWeight
  unfold centralPhysicalFinitePulledWeight at hfloor
  rw [hsourceMap] at hfloor
  exact hfloor

/-! ## 2. Positive-denominator antitonicity -/

/-- Dividing a nonnegative rational by a larger positive denominator can only
decrease it.  This helper retains all positivity witnesses explicitly. -/
theorem divPos_le_divPos_of_denominator_le
    {numerator small large : Q'}
    (hnumerator : (0 : Q') ≤ numerator)
    (hsmall : (0 : Q') < small)
    (hlarge : (0 : Q') < large)
    (hdenominator : small ≤ large) :
    Q'.divPos numerator large hlarge ≤
      Q'.divPos numerator small hsmall := by
  apply Q'.divPos_le_of_le_mul numerator large hlarge
  have hquotientNonnegative :
      (0 : Q') ≤ Q'.divPos numerator small hsmall := by
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _ hnumerator
      (Q'.le_of_lt (Q'.recipPos_pos small hsmall))
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    small large (Q'.divPos numerator small hsmall)
    hdenominator hquotientNonnegative
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.divPos_mul_eqv numerator small hsmall))
    hscaled

/-! ## 3. A fixed-denominator envelope for old-to-new traffic -/

/-- Reverse cross traffic divided by the fixed positive cutoff-two old-row
floor.  Unlike the literal relative load, its denominator is independent of
the later cutoff and the selected old state. -/
def cutoffTwoNovelReverseOldRowFloorEnvelope
    (later oldState newState : Nat) : Q' :=
  Q'.divPos
    (cutoffTwoNovelSimpleEdgeLoad later newState oldState)
    cutoffTwoPulledUniformPositiveRowFloor
    cutoffTwoPulledUniformPositiveRowFloor_pos

/-- Replacing the actual old weight by its fixed lower floor majorizes the
reverse relative load. -/
theorem cutoffTwoNovelRelativeTargetEdgeLoad_le_reverseOldRowFloorEnvelope
    {later oldState newState : Nat}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (hold : oldState ∈ cutoffTwoEdgeLoadOldStates later) :
    cutoffTwoNovelRelativeTargetEdgeLoad later newState oldState ≤
      cutoffTwoNovelReverseOldRowFloorEnvelope
        later oldState newState := by
  have holdFull : oldState ∈ cutoffTwoEdgeLoadFullStates later :=
    (List.mem_filter.mp hold).1
  have holdWeight :=
    YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w := cutoffTwoHalfCoupling) (hw := by decide) holdFull
  unfold cutoffTwoNovelRelativeTargetEdgeLoad
    cutoffTwoNovelReverseOldRowFloorEnvelope
  rw [dif_pos holdFull]
  exact divPos_le_divPos_of_denominator_le
    (cutoffTwoNovelSimpleEdgeLoad_nonnegative later newState oldState)
    cutoffTwoPulledUniformPositiveRowFloor_pos holdWeight
    (cutoffTwoPulledUniformPositiveRowFloor_le_oldWeight hlater hold)

/-- The full symmetric relative cross load with its reverse half enlarged to
use the fixed old-row-floor denominator. -/
def cutoffTwoNovelSymmetricOldNewRowFloorEnvelope
    (later oldState newState : Nat) : Q' :=
  HalfPow.half *
      cutoffTwoNovelRelativeSourceEdgeLoad later oldState newState +
    HalfPow.half *
      cutoffTwoNovelReverseOldRowFloorEnvelope
        later oldState newState

theorem cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_le_oldNewRowFloorEnvelope
    {later oldState newState : Nat}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (hold : oldState ∈ cutoffTwoEdgeLoadOldStates later) :
    cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
        later oldState newState ≤
      cutoffTwoNovelSymmetricOldNewRowFloorEnvelope
        later oldState newState := by
  unfold cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
    cutoffTwoNovelSymmetricOldNewRowFloorEnvelope
  exact Q'.add_le_add
    (Q'.le_refl' _)
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (cutoffTwoNovelRelativeTargetEdgeLoad_le_reverseOldRowFloorEnvelope
        hlater hold)
      HalfPow.half_nonneg)

/-! ## 4. Envelope payment supplies the cross-capacity field -/

/-- A non-vacuous Type-level witness that the physical conditional transition
pays the larger, fixed-denominator old-to-new traffic envelope. -/
structure CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt
    (later : Nat) : Type 1 where
  anchor_le : cutoffTwoPulledRowFloorAnchor ≤ later
  envelope_capacity : ∀ oldState,
    oldState ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ newState,
    newState ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricOldNewRowFloorEnvelope
            later oldState newState ≤
        cutoffTwoEdgeLoadConditionalKernel later oldState newState

namespace CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt

/-- Fixed-row-floor envelope payment contracts to the exact ratio-free cross
certificate required by the preceding module. -/
def toOldNewConditionalCapacityAt
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt later) :
    CutoffTwoNovelSymmetricOldNewConditionalCapacityAt later where
  relative_capacity := fun oldState hold newState hnew => by
    have henvelope :=
      cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_le_oldNewRowFloorEnvelope
        (newState := newState) capacity.anchor_le hold
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      cutoffTwoNovelSimpleFlowCoercivityFloor henvelope
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (capacity.envelope_capacity oldState hold newState hnew)

/-- The fixed-row-floor certificate therefore supplies the old-to-new physical
capacity field required by the symmetric compiler. -/
theorem old_new
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt later)
    (oldState : Nat)
    (hold : oldState ∈ cutoffTwoEdgeLoadOldStates later)
    (newState : Nat)
    (hnew : newState ∈ cutoffTwoEdgeLoadNewStates later) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.cutoffTwoNovelSymmetricEdgeLoad
          later oldState newState ≤
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio.cutoffTwoNovelAllocatedKernel
        later oldState newState :=
  capacity.toOldNewConditionalCapacityAt.old_new
    oldState hold newState hnew

end CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor.cutoffTwoPulledUniformPositiveRowFloor_le_oldWeight
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor.divPos_le_divPos_of_denominator_le
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor.cutoffTwoNovelRelativeTargetEdgeLoad_le_reverseOldRowFloorEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor.cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_le_oldNewRowFloorEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor.CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt.toOldNewConditionalCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor.CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt.old_new
