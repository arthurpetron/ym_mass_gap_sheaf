/-
# The within-component pivot carrier for the outward Y/Z cut

At the unique four-incidence link of the outward Y/Z surface, corrected-slab
face order is `Z,Y,Z,Y,0`.  The selected right-tree column has written rank
zero.  Equal-rank realization sends it to the left-tree carrier with first
intermediate twice-spin `2` and second intermediate twice-spin `1`.

Thus the carrier retains the two Z strands through the first fusion and then
retains one strand through the second fusion before closing against the last
Y strand.  This is the local representation-theoretic datum needed for the
within-component `Z-Z` and `Y-Y` pivot pairing.  The subsequent global module
still has to compile this local column together with the sparse nonpivot
columns and prove marked-face disconnection.

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

/-- The active positions alternate by component: Z, Y, Z, Y.  The final
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
#print axioms outwardYZPivotTarget_rank_source
#print axioms outwardYZPivotLeftAuxiliary_firstIntermediate
#print axioms outwardYZPivotLeftAuxiliary_secondIntermediate
#print axioms outwardYZPivotRightAuxiliary_zero
#print axioms outwardYZPivotCarrierCertificate

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
