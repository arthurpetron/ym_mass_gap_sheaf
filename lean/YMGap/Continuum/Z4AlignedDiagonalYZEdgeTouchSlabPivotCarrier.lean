/-
# The rank-one pivot target for the aligned diagonal cut

The valence-five fundamental/vacuum pivot has two left carriers and two right
targets.  Written enumeration order pairs the right target with `m = 2` to
the left carrier with auxiliary labels `(0,1)`.  That left carrier pairs
physical positions `0 <-> 1` and `2 <-> 3`.  Against the aligned component
order `[near,near,far,far,vacuum]`, both pairs stay within one side.

This module writes the rank-one target and proves its equal-rank production
carrier exactly.  No basis reinterpretation is involved.

Constructive contract: explicit finite SU(2) carriers only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, noncomputable declaration,
or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Literal face and component order -/

theorem alignedDiagonalPivot_incidentPlaquetteOrder :
    (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).map
        (slabPlaquetteAt 5) =
      [((0, 0, 1, 0), .p01),
       ((0, 1, 0, 0), .p02),
       ((0, 1, 1, 0), .p01),
       ((0, 1, 1, 0), .p02),
       ((0, 1, 1, 0), .p03)] := by
  decide

theorem alignedDiagonalPivot_componentOrder :
    (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).map
        alignedDiagonalComponentTag = [1, 1, 2, 2, 0] :=
  alignedDiagonalSwitchPivot_componentTagList

/-! ## 2. Select the rank-one right target -/

def alignedDiagonalPivotLeftTarget :
    ValenceFiveRightCarrier 1 1 1 1 0 where
  m := 2
  inner :=
    { order := 0
      order_le := by decide
      output_eq := by decide }
  second :=
    { p := 1
      p_le := by decide
      r := 1
      r_le := by decide
      degree_eq := by decide }

def alignedDiagonalPivotRightTarget :
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

def alignedDiagonalPivotTarget :
    (slabPhysicalPairRecouplingKernelPackageFive
      alignedDiagonalSwitchPivotRecouplingData).Target :=
  (alignedDiagonalPivotLeftTarget, alignedDiagonalPivotRightTarget)

theorem alignedDiagonalPivotTarget_channel_data :
    alignedDiagonalPivotLeftTarget.m = 2 ∧
    alignedDiagonalPivotLeftTarget.inner.order = 0 ∧
    alignedDiagonalPivotLeftTarget.second.p = 1 ∧
    alignedDiagonalPivotLeftTarget.second.r = 1 := by
  decide

theorem alignedDiagonalPivotTarget_mem :
    alignedDiagonalPivotTarget ∈
      (slabPhysicalPairRecouplingKernelPackageFive
        alignedDiagonalSwitchPivotRecouplingData).kernel.targets :=
  slabPhysicalPairRecouplingTarget_mem
    5 alignedDiagonalSwitchPivotRecouplingData
      alignedDiagonalPivotTarget

/-! ## 3. Exact equal-rank production carrier -/

def alignedDiagonalPivotLeftSource :
    ValenceFiveLeftCarrier 1 1 1 1 0 where
  y := 1
  firstLeft :=
    { k := 1
      k_le := by decide
      r := 0
      r_le := by decide
      degree_eq := by decide }
  suffix :=
    { order := 1
      order_le := by decide
      output_eq := by decide }

def alignedDiagonalPivotRightSource :
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

theorem alignedDiagonalPivotTarget_rank_source
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      alignedDiagonalSwitchPivotRecouplingData) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      alignedDiagonalSwitchPivotRecouplingData anchor
        alignedDiagonalPivotTarget =
      (alignedDiagonalPivotLeftSource,
        alignedDiagonalPivotRightSource) := by
  rfl

def alignedDiagonalPivotLeftAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary alignedDiagonalPivotLeftSource

def alignedDiagonalPivotRightAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary alignedDiagonalPivotRightSource

theorem alignedDiagonalPivotLeftAuxiliary_firstIntermediate :
    alignedDiagonalPivotLeftAuxiliary 6 = 0 := by
  rfl

theorem alignedDiagonalPivotLeftAuxiliary_secondIntermediate :
    alignedDiagonalPivotLeftAuxiliary 7 = 1 := by
  rfl

theorem alignedDiagonalPivotRightAuxiliary_zero (edge : Nat) :
    alignedDiagonalPivotRightAuxiliary edge = 0 := by
  by_cases h6 : edge = 6
  · subst edge
    rfl
  · by_cases h7 : edge = 7
    · subst edge
      rfl
    · simp [alignedDiagonalPivotRightAuxiliary,
        valenceFiveLeftAuxiliary, h6, h7]

structure AlignedDiagonalPivotCarrierCertificate : Type where
  target : (slabPhysicalPairRecouplingKernelPackageFive
    alignedDiagonalSwitchPivotRecouplingData).Target
  target_mem : target ∈
    (slabPhysicalPairRecouplingKernelPackageFive
      alignedDiagonalSwitchPivotRecouplingData).kernel.targets
  rank_source : forall anchor : SlabPhysicalPairRecouplingWitnessData 1
      alignedDiagonalSwitchPivotRecouplingData,
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      alignedDiagonalSwitchPivotRecouplingData anchor target =
      (alignedDiagonalPivotLeftSource,
        alignedDiagonalPivotRightSource)
  firstIntermediate : alignedDiagonalPivotLeftAuxiliary 6 = 0
  secondIntermediate : alignedDiagonalPivotLeftAuxiliary 7 = 1
  vacuumAuxiliary : forall edge,
    alignedDiagonalPivotRightAuxiliary edge = 0

def alignedDiagonalPivotCarrierCertificate :
    AlignedDiagonalPivotCarrierCertificate :=
  { target := alignedDiagonalPivotTarget
    target_mem := alignedDiagonalPivotTarget_mem
    rank_source := alignedDiagonalPivotTarget_rank_source
    firstIntermediate :=
      alignedDiagonalPivotLeftAuxiliary_firstIntermediate
    secondIntermediate :=
      alignedDiagonalPivotLeftAuxiliary_secondIntermediate
    vacuumAuxiliary := alignedDiagonalPivotRightAuxiliary_zero }

#print axioms alignedDiagonalPivot_incidentPlaquetteOrder
#print axioms alignedDiagonalPivotTarget_mem
#print axioms alignedDiagonalPivotTarget_rank_source
#print axioms alignedDiagonalPivotLeftAuxiliary_firstIntermediate
#print axioms alignedDiagonalPivotLeftAuxiliary_secondIntermediate
#print axioms alignedDiagonalPivotRightAuxiliary_zero
#print axioms alignedDiagonalPivotCarrierCertificate

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier
