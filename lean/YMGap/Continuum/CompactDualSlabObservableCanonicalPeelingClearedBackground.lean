/-
# The canonical peeled terminal is a cleared component background

For an actual support-connected observable source, canonical peeling is not
an arbitrary accepted terminal.  It clears the whole target-rooted support
component, which contains both marked observable faces, and leaves the source
literally unchanged outside that component.  Its auxiliary assignments are
likewise unchanged away from the links incident to the component.

This module packages those facts as the neutral-background input needed by a
future reflected-pattern insertion.  It introduces no insertion and claims no
good-source density by itself.

Constructive contract: specialization of proved canonical peeling locality
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality
import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning

namespace YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingClearedBackground

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The actual component and canonical output of a connected source -/

def slabObservablePairedConnectedSourceTargetComponent
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : List Nat :=
  slabTwoReplicaTargetSupportComponent D.extent
    source.1.1.1.1 source.1.2.1.1 targetFaceId

def slabObservablePairedConnectedSourceCanonicalPeeling
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    SlabAcceptedPairedCanonicalPeelingOutput D :=
  slabObservablePairTargetSupportCanonicalPeeling
    D rootFaceId targetFaceId htarget source.1
      (List.mem_filter.mp source.2).1

abbrev slabObservablePairedConnectedSourceCanonicalTerminal
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : SlabAcceptedTwoReplicaState D :=
  (slabObservablePairedConnectedSourceCanonicalPeeling
    htarget source).1

/-! ## 2. One exact cleared-background package -/

/-- The terminal background produced by an actual connected source is zero
on the complete marked component and unchanged everywhere outside its
physical and auxiliary incidence neighborhoods. -/
structure SlabObservablePairedConnectedClearedBackground
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : Prop where
  component_nodup :
    (slabObservablePairedConnectedSourceTargetComponent source).Nodup
  target_mem_component :
    targetFaceId ∈
      slabObservablePairedConnectedSourceTargetComponent source
  root_mem_component :
    rootFaceId ∈
      slabObservablePairedConnectedSourceTargetComponent source
  terminal_zero_on_component : ∀ faceId,
    faceId ∈ slabObservablePairedConnectedSourceTargetComponent source →
      (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).1.1.1 faceId = 0 ∧
      (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).2.1.1 faceId = 0
  terminal_physical_eq_outside : ∀ faceId,
    faceId ∉ slabObservablePairedConnectedSourceTargetComponent source →
      (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).1.1.1 faceId = source.1.1.1.1 faceId ∧
      (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).2.1.1 faceId = source.1.2.1.1 faceId
  terminal_assignment_eq_outside_activeLinks : ∀ link,
    link ∈ boundaryCompleteSlabLinks D.extent →
    link ∉ slabObservableTwoReplicaPairTargetSupportActiveLinks
      D source.1 targetFaceId →
      slabFusionWitnessAssignmentAt link
          (slabObservablePairedConnectedSourceCanonicalTerminal
            htarget source).1.1.2 =
        slabFusionWitnessAssignmentAt link source.1.1.1.2 ∧
      slabFusionWitnessAssignmentAt link
          (slabObservablePairedConnectedSourceCanonicalTerminal
            htarget source).2.1.2 =
        slabFusionWitnessAssignmentAt link source.1.2.1.2

/-! ## 3. Every actual connected source produces the package -/

/-- Complete canonical peeling constructively supplies the exact neutral
background package for every literal support-connected source. -/
def slabObservablePairedConnectedSourceClearedBackground
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    SlabObservablePairedConnectedClearedBackground htarget source where
  component_nodup := by
    unfold slabObservablePairedConnectedSourceTargetComponent
    exact rootComponent_nodup
      (slabSupportFaceAdjacentB D.extent)
      (slabTwoReplicaSupportFaceVertices D.extent
        source.1.1.1.1 source.1.2.1.1)
      targetFaceId
  target_mem_component := by
    unfold slabObservablePairedConnectedSourceTargetComponent
    exact slabObservableTwoReplicaPairTarget_mem_targetSupportComponent
      D rootFaceId targetFaceId htarget source.1
        (List.mem_filter.mp source.2).1
  root_mem_component := by
    unfold slabObservablePairedConnectedSourceTargetComponent
    exact of_decide_eq_true source.connected
  terminal_zero_on_component := by
    intro faceId hface
    have hzero := slabAcceptedPairCanonicalPeeling_final_zero
      D
      (slabTwoReplicaTargetSupportComponent D.extent
        source.1.1.1.1 source.1.2.1.1 targetFaceId)
      (fun query hquery =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget source.1
            (List.mem_filter.mp source.2).1 query hquery)
      (slabObservableTwoReplicaPairToAcceptedState source.1)
      faceId hface
    simpa only [slabObservablePairedConnectedSourceCanonicalTerminal,
      slabObservablePairedConnectedSourceCanonicalPeeling,
      slabObservablePairTargetSupportCanonicalPeeling] using hzero
  terminal_physical_eq_outside := by
    intro faceId houtside
    exact
      slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
        D rootFaceId targetFaceId htarget source.1
          (List.mem_filter.mp source.2).1 faceId houtside
  terminal_assignment_eq_outside_activeLinks := by
    intro link hlink hinactive
    exact
      slabObservablePairTargetSupportCanonicalPeeling_final_assignment_eq_outside_activeLinks
        D rootFaceId targetFaceId htarget source.1
          (List.mem_filter.mp source.2).1 link hlink hinactive

/-! ## 4. Both marked faces are literally cleared -/

theorem slabObservablePairedConnectedSourceCanonicalTerminal_root_zero
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).1.1.1 rootFaceId = 0 ∧
      (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).2.1.1 rootFaceId = 0 := by
  let cleared := slabObservablePairedConnectedSourceClearedBackground
    htarget source
  exact cleared.terminal_zero_on_component rootFaceId
    cleared.root_mem_component

theorem slabObservablePairedConnectedSourceCanonicalTerminal_target_zero
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).1.1.1 targetFaceId = 0 ∧
      (slabObservablePairedConnectedSourceCanonicalTerminal
        htarget source).2.1.1 targetFaceId = 0 := by
  let cleared := slabObservablePairedConnectedSourceClearedBackground
    htarget source
  exact cleared.terminal_zero_on_component targetFaceId
    cleared.target_mem_component

#print axioms slabObservablePairedConnectedSourceTargetComponent
#print axioms slabObservablePairedConnectedSourceCanonicalPeeling
#print axioms SlabObservablePairedConnectedClearedBackground
#print axioms slabObservablePairedConnectedSourceClearedBackground
#print axioms slabObservablePairedConnectedSourceCanonicalTerminal_root_zero
#print axioms slabObservablePairedConnectedSourceCanonicalTerminal_target_zero

end YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingClearedBackground
