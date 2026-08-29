/-
# Equal-rank target columns for both outward repair pivots

The two component-preserving canonical-left carriers are now placed at exact
written ranks in the corresponding right-tree target enumerations.  Equal-rank
production realization therefore reconstructs precisely the selected spatial
and temporal auxiliaries, independent of the accepted local anchor.

This module identifies columns and their production representatives.  It does
not yet prove that the two local matrix entries from the accepted source row
are positive or assemble the complete slab product.

Constructive contract: explicit finite SU(2) carriers and rank computation
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotTarget

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing

def outwardYZCanonicalRepairVacuumLeftSource :
    ValenceFiveLeftCarrier 0 0 0 0 0 where
  y := 0
  firstLeft :=
    { k := 0
      k_le := by decide
      r := 0
      r_le := by decide
      degree_eq := by decide }
  suffix :=
    { order := 0
      order_le := by decide
      output_eq := by decide }

def outwardYZCanonicalRepairVacuumRightTarget :
    ValenceFiveRightCarrier 0 0 0 0 0 where
  m := 0
  inner :=
    { order := 0
      order_le := by decide
      output_eq := by decide }
  second :=
    { p := 0
      p_le := by decide
      r := 0
      r_le := by decide
      degree_eq := by decide }

/-! ## 1. Spatial column -/

def outwardYZCanonicalRepairSpatialLeftTarget :
    ValenceFiveRightCarrier 1 1 1 1 0 where
  m := 0
  inner :=
    { order := 1
      order_le := by decide
      output_eq := by decide }
  second :=
    { p := 0
      p_le := by decide
      r := 1
      r_le := by decide
      degree_eq := by decide }

def outwardYZCanonicalRepairSpatialTarget :
    (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairSpatialPivotRecouplingData).Target :=
  (outwardYZCanonicalRepairSpatialLeftTarget,
    outwardYZCanonicalRepairVacuumRightTarget)

theorem outwardYZCanonicalRepairSpatialTarget_mem :
    outwardYZCanonicalRepairSpatialTarget ∈
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZCanonicalRepairSpatialPivotRecouplingData).kernel.targets :=
  slabPhysicalPairRecouplingTarget_mem 5
    outwardYZCanonicalRepairSpatialPivotRecouplingData
    outwardYZCanonicalRepairSpatialTarget

theorem outwardYZCanonicalRepairSpatialTarget_rank_source
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      outwardYZCanonicalRepairSpatialPivotRecouplingData) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      outwardYZCanonicalRepairSpatialPivotRecouplingData anchor
      outwardYZCanonicalRepairSpatialTarget =
        (outwardYZCanonicalRepairSpatialLeftSource,
          outwardYZCanonicalRepairVacuumLeftSource) := by
  rfl

/-! ## 2. Temporal column -/

/-- The temporal target has written rank one: the inner `(1,0)` fusion is
forced and the second right channel uses contraction order one. -/
def outwardYZCanonicalRepairTemporalLeftTarget :
    ValenceFiveRightCarrier 1 1 0 1 1 where
  m := 1
  inner :=
    { order := 0
      order_le := by decide
      output_eq := by decide }
  second :=
    { p := 1
      p_le := by decide
      r := 0
      r_le := by decide
      degree_eq := by decide }

def outwardYZCanonicalRepairTemporalTarget :
    (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairTemporalPivotRecouplingData).Target :=
  (outwardYZCanonicalRepairTemporalLeftTarget,
    outwardYZCanonicalRepairVacuumRightTarget)

theorem outwardYZCanonicalRepairTemporalTarget_mem :
    outwardYZCanonicalRepairTemporalTarget ∈
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZCanonicalRepairTemporalPivotRecouplingData).kernel.targets :=
  slabPhysicalPairRecouplingTarget_mem 5
    outwardYZCanonicalRepairTemporalPivotRecouplingData
    outwardYZCanonicalRepairTemporalTarget

theorem outwardYZCanonicalRepairTemporalTarget_rank_source
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      outwardYZCanonicalRepairTemporalPivotRecouplingData) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      outwardYZCanonicalRepairTemporalPivotRecouplingData anchor
      outwardYZCanonicalRepairTemporalTarget =
        (outwardYZCanonicalRepairTemporalLeftSource,
          outwardYZCanonicalRepairVacuumLeftSource) := by
  rfl

/-! ## 3. Exact production auxiliaries -/

theorem outwardYZCanonicalRepairSpatialTargetProduction_leftAuxiliary
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      outwardYZCanonicalRepairSpatialPivotRecouplingData)
    (rightBounded : SlabFaceLabellingBounded 1 5
      outwardYZCanonicalRepairSwitchRightPhysical) :
    (slabPhysicalPairTargetProductionWitnessPair
      outwardYZCanonicalRepairSpatialPivotRecouplingData anchor
      outwardYZCanonicalRepairSwitchLeftPhysical_bounded rightBounded
      outwardYZCanonicalRepairSpatialTarget).leftAuxiliary =
        outwardYZCanonicalRepairSpatialLeftAuxiliary := by
  unfold slabPhysicalPairTargetProductionWitnessPair
    slabPhysicalPairProductionWitnessPairOfSource
  rw [outwardYZCanonicalRepairSpatialTarget_rank_source]
  rfl

theorem outwardYZCanonicalRepairTemporalTargetProduction_leftAuxiliary
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      outwardYZCanonicalRepairTemporalPivotRecouplingData)
    (rightBounded : SlabFaceLabellingBounded 1 5
      outwardYZCanonicalRepairSwitchRightPhysical) :
    (slabPhysicalPairTargetProductionWitnessPair
      outwardYZCanonicalRepairTemporalPivotRecouplingData anchor
      outwardYZCanonicalRepairSwitchLeftPhysical_bounded rightBounded
      outwardYZCanonicalRepairTemporalTarget).leftAuxiliary =
        outwardYZCanonicalRepairTemporalLeftAuxiliary := by
  unfold slabPhysicalPairTargetProductionWitnessPair
    slabPhysicalPairProductionWitnessPairOfSource
  rw [outwardYZCanonicalRepairTemporalTarget_rank_source]
  rfl

#print axioms outwardYZCanonicalRepairSpatialTarget_mem
#print axioms outwardYZCanonicalRepairSpatialTarget_rank_source
#print axioms outwardYZCanonicalRepairTemporalTarget_mem
#print axioms outwardYZCanonicalRepairTemporalTarget_rank_source
#print axioms outwardYZCanonicalRepairSpatialTargetProduction_leftAuxiliary
#print axioms outwardYZCanonicalRepairTemporalTargetProduction_leftAuxiliary

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotTarget
