/-
# The component-preserving pivot carrier for the reflected bent-cube cut

At the unique pivot, corrected-slab order is `[near, vacuum, near, far,
far]` and the external spin word is `[1,0,1,1,1]`.  Its two left-tree
carriers have auxiliary labels `(1,0)` and `(1,2)`.  The written rank-zero
right-tree column recodes to `(1,0)`, whose singlet channels pair the two near
terminals and the two far terminals separately.

This module selects that column and proves the equal-rank production carrier
literally.  Positivity and terminal-path realization are separate downstream
statements.

Constructive contract: explicit finite SU(2) carriers only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, noncomputable declaration,
or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. The literal physical pair and local order -/

abbrev reflectedBentSwitchLeftPhysical : SlabLabelling :=
  reflectedBentBinaryConnectedCarrier.leftPhysical

abbrev reflectedBentSwitchRightPhysical : SlabLabelling :=
  reflectedBentBinaryConnectedCarrier.rightPhysical

def reflectedBentSwitchPivotRecouplingData :
    SlabPhysicalPairRecouplingData 5 5 where
  leftPhysical := reflectedBentSwitchLeftPhysical
  rightPhysical := reflectedBentSwitchRightPhysical
  link := reflectedBentSwitchPivot
  degree_eq := reflectedBentSwitchPivot_degree_five

theorem reflectedBentPivot_incidentPlaquetteOrder :
    (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).map
        (slabPlaquetteAt 5) =
      [((0, 0, 0, 2), .p02),
       ((0, 0, 1, 1), .p03),
       ((0, 0, 1, 2), .p01),
       ((0, 0, 1, 2), .p02),
       ((0, 0, 1, 2), .p03)] := by
  decide

theorem reflectedBentPivot_componentOrder :
    (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).map
        reflectedBentComponentTag = [1, 0, 1, 2, 2] :=
  reflectedBentSwitchPivot_componentTagList

/-! ## 2. Select the rank-zero right target -/

def reflectedBentPivotLeftTarget :
    ValenceFiveRightCarrier 1 0 1 1 1 where
  m := 1
  inner :=
    { order := 0
      order_le := by decide
      output_eq := by decide }
  second :=
    { p := 0
      p_le := by decide
      r := 1
      r_le := by decide
      degree_eq := by decide }

def reflectedBentPivotRightTarget :
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

def reflectedBentPivotTarget :
    (slabPhysicalPairRecouplingKernelPackageFive
      reflectedBentSwitchPivotRecouplingData).Target :=
  (reflectedBentPivotLeftTarget, reflectedBentPivotRightTarget)

theorem reflectedBentPivotTarget_channel_data :
    reflectedBentPivotLeftTarget.m = 1 ∧
    reflectedBentPivotLeftTarget.inner.order = 0 ∧
    reflectedBentPivotLeftTarget.second.p = 0 ∧
    reflectedBentPivotLeftTarget.second.r = 1 := by
  decide

theorem reflectedBentPivotTarget_mem :
    reflectedBentPivotTarget ∈
      (slabPhysicalPairRecouplingKernelPackageFive
        reflectedBentSwitchPivotRecouplingData).kernel.targets :=
  slabPhysicalPairRecouplingTarget_mem
    5 reflectedBentSwitchPivotRecouplingData reflectedBentPivotTarget

/-! ## 3. Exact equal-rank production carrier -/

def reflectedBentPivotLeftSource :
    ValenceFiveLeftCarrier 1 0 1 1 1 where
  y := 0
  firstLeft :=
    { k := 0
      k_le := by decide
      r := 1
      r_le := by decide
      degree_eq := by decide }
  suffix :=
    { order := 0
      order_le := by decide
      output_eq := by decide }

def reflectedBentPivotRightSource :
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

theorem reflectedBentPivotTarget_rank_source
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      reflectedBentSwitchPivotRecouplingData) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      reflectedBentSwitchPivotRecouplingData anchor reflectedBentPivotTarget =
        (reflectedBentPivotLeftSource, reflectedBentPivotRightSource) := by
  rfl

def reflectedBentPivotLeftAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary reflectedBentPivotLeftSource

def reflectedBentPivotRightAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary reflectedBentPivotRightSource

theorem reflectedBentPivotLeftAuxiliary_firstIntermediate :
    reflectedBentPivotLeftAuxiliary 6 = 1 := by
  rfl

theorem reflectedBentPivotLeftAuxiliary_secondIntermediate :
    reflectedBentPivotLeftAuxiliary 7 = 0 := by
  rfl

theorem reflectedBentPivotRightAuxiliary_zero (edge : Nat) :
    reflectedBentPivotRightAuxiliary edge = 0 := by
  by_cases h6 : edge = 6
  · subst edge
    rfl
  · by_cases h7 : edge = 7
    · subst edge
      rfl
    · simp [reflectedBentPivotRightAuxiliary,
        valenceFiveLeftAuxiliary, h6, h7]

structure ReflectedBentPivotCarrierCertificate : Type where
  target : (slabPhysicalPairRecouplingKernelPackageFive
    reflectedBentSwitchPivotRecouplingData).Target
  target_mem : target ∈
    (slabPhysicalPairRecouplingKernelPackageFive
      reflectedBentSwitchPivotRecouplingData).kernel.targets
  rank_source : forall anchor : SlabPhysicalPairRecouplingWitnessData 1
      reflectedBentSwitchPivotRecouplingData,
    slabPhysicalPairTargetToProductionSourceAtEqualRank
      reflectedBentSwitchPivotRecouplingData anchor target =
      (reflectedBentPivotLeftSource, reflectedBentPivotRightSource)
  firstIntermediate : reflectedBentPivotLeftAuxiliary 6 = 1
  secondIntermediate : reflectedBentPivotLeftAuxiliary 7 = 0
  vacuumAuxiliary : forall edge,
    reflectedBentPivotRightAuxiliary edge = 0

def reflectedBentPivotCarrierCertificate :
    ReflectedBentPivotCarrierCertificate :=
  { target := reflectedBentPivotTarget
    target_mem := reflectedBentPivotTarget_mem
    rank_source := reflectedBentPivotTarget_rank_source
    firstIntermediate :=
      reflectedBentPivotLeftAuxiliary_firstIntermediate
    secondIntermediate :=
      reflectedBentPivotLeftAuxiliary_secondIntermediate
    vacuumAuxiliary := reflectedBentPivotRightAuxiliary_zero }

#print axioms reflectedBentSwitchPivotRecouplingData
#print axioms reflectedBentPivot_incidentPlaquetteOrder
#print axioms reflectedBentPivotTarget_mem
#print axioms reflectedBentPivotTarget_rank_source
#print axioms reflectedBentPivotLeftAuxiliary_firstIntermediate
#print axioms reflectedBentPivotLeftAuxiliary_secondIntermediate
#print axioms reflectedBentPivotRightAuxiliary_zero
#print axioms reflectedBentPivotCarrierCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
