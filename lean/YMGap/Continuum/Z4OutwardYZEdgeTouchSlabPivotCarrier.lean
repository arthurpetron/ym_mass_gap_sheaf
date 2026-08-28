/-
# A concrete pivot carrier for the outward Y/Z cut

At the unique four-incidence link of the outward Y/Z surface, corrected-slab
face order is `Z,Y,Y,Z,0`.  The selected right-tree column has written rank
zero.  Equal-rank realization sends it to the left-tree carrier with first
intermediate twice-spin `2` and second intermediate twice-spin `1`.

The literal terminal computation shows that this left-tree carrier pairs
positions `0 <-> 2` and `1 <-> 3`; in the actual face order both pairs cross
from one cube side to the other.  Thus this carrier is a concrete positive
connected channel, not the sought disconnected channel.  A disconnected
column must retain the right-tree pairing or use a coherence compiler that
realizes that pairing faithfully.

Constructive contract: explicit finite SU(2) carriers and literal slab-face
order only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier

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
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. Literal face order at the cut link -/

/-- The active positions have component order Z, Y, Y, Z.  The final
corrected-slab coordinate is a vacuum temporal face. -/
theorem outwardYZPivot_incidentPlaquetteOrder :
    (slabIncidentPlaqIds 5 outwardYZSwitchPivot).map
        (slabPlaquetteAt 5) =
      [((0, 0, 1, 0), .p01),
       ((0, 1, 0, 0), .p02),
       ((0, 1, 1, 0), .p01),
       ((0, 1, 1, 0), .p02),
       ((0, 1, 1, 0), .p03)] := by
  decide

/-! ## 2. Select the rank-zero target column -/

def outwardYZPivotLeftTarget : ValenceFiveRightCarrier 1 1 1 1 0 where
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

def outwardYZPivotRightTarget : ValenceFiveRightCarrier 0 0 0 0 0 where
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

def outwardYZPivotTarget :
    (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZSwitchPivotRecouplingData).Target :=
  (outwardYZPivotLeftTarget, outwardYZPivotRightTarget)

/-- The physical-terminal pairing represented by the selected target in its
native right-associated tree.  The inner vacuum channel pairs slots one and
two; the remaining singlet pairs slots zero and three. -/
def outwardYZPivotNativeRightEdgeIdPairs : List (Nat × Nat) :=
  [(1, 2), (2, 1), (0, 3), (3, 0)]

theorem outwardYZPivotLeftTarget_native_channel_data :
    outwardYZPivotLeftTarget.m = 0 ∧
    outwardYZPivotLeftTarget.inner.order = 1 ∧
    outwardYZPivotLeftTarget.second.p = 0 ∧
    outwardYZPivotLeftTarget.second.r = 1 := by
  decide

theorem outwardYZPivotTarget_mem :
    outwardYZPivotTarget ∈
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZSwitchPivotRecouplingData).kernel.targets :=
  slabPhysicalPairRecouplingTarget_mem
    5 outwardYZSwitchPivotRecouplingData outwardYZPivotTarget

/-! ## 3. Decode the selected column to its production carrier -/

def outwardYZPivotLeftSource : ValenceFiveLeftCarrier 1 1 1 1 0 where
  y := 1
  firstLeft :=
    { k := 0
      k_le := by decide
      r := 1
      r_le := by decide
      degree_eq := by decide }
  suffix :=
    { order := 1
      order_le := by decide
      output_eq := by decide }

def outwardYZPivotRightSource : ValenceFiveLeftCarrier 0 0 0 0 0 where
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

/-- The rank decoding is independent of the accepted auxiliary anchor. -/
theorem outwardYZPivotTarget_rank_source
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      outwardYZSwitchPivotRecouplingData) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      outwardYZSwitchPivotRecouplingData anchor outwardYZPivotTarget =
        (outwardYZPivotLeftSource, outwardYZPivotRightSource) := by
  rfl

def outwardYZPivotLeftAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary outwardYZPivotLeftSource

def outwardYZPivotRightAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary outwardYZPivotRightSource

theorem outwardYZPivotLeftAuxiliary_firstIntermediate :
    outwardYZPivotLeftAuxiliary 6 = 2 := by
  rfl

theorem outwardYZPivotLeftAuxiliary_secondIntermediate :
    outwardYZPivotLeftAuxiliary 7 = 1 := by
  rfl

theorem outwardYZPivotRightAuxiliary_zero (edge : Nat) :
    outwardYZPivotRightAuxiliary edge = 0 := by
  by_cases h6 : edge = 6
  · subst edge
    rfl
  · by_cases h7 : edge = 7
    · subst edge
      rfl
    · simp [outwardYZPivotRightAuxiliary, valenceFiveLeftAuxiliary,
        h6, h7]

/-! ## 4. One small certificate for global compilation -/

structure OutwardYZPivotCarrierCertificate : Type where
  target : (slabPhysicalPairRecouplingKernelPackageFive
    outwardYZSwitchPivotRecouplingData).Target
  target_mem : target ∈
    (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZSwitchPivotRecouplingData).kernel.targets
  rank_source : forall anchor : SlabPhysicalPairRecouplingWitnessData 1
      outwardYZSwitchPivotRecouplingData,
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      outwardYZSwitchPivotRecouplingData anchor target =
        (outwardYZPivotLeftSource, outwardYZPivotRightSource)
  firstIntermediate : outwardYZPivotLeftAuxiliary 6 = 2
  secondIntermediate : outwardYZPivotLeftAuxiliary 7 = 1
  vacuumAuxiliary : forall edge, outwardYZPivotRightAuxiliary edge = 0

def outwardYZPivotCarrierCertificate : OutwardYZPivotCarrierCertificate :=
  { target := outwardYZPivotTarget
    target_mem := outwardYZPivotTarget_mem
    rank_source := outwardYZPivotTarget_rank_source
    firstIntermediate := outwardYZPivotLeftAuxiliary_firstIntermediate
    secondIntermediate := outwardYZPivotLeftAuxiliary_secondIntermediate
    vacuumAuxiliary := outwardYZPivotRightAuxiliary_zero }

#print axioms outwardYZPivot_incidentPlaquetteOrder
#print axioms outwardYZPivotTarget_mem
#print axioms outwardYZPivotLeftTarget_native_channel_data
#print axioms outwardYZPivotTarget_rank_source
#print axioms outwardYZPivotLeftAuxiliary_firstIntermediate
#print axioms outwardYZPivotLeftAuxiliary_secondIntermediate
#print axioms outwardYZPivotRightAuxiliary_zero
#print axioms outwardYZPivotCarrierCertificate

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
