/-
# The separated cylinder as literal observable-row choices

The literal row package exposes exact equalities to the canonical observable
SU(2) package list and production source.  Transport each separated-cylinder
target across those equalities.  The result is a genuine member of the
observable recoupling row, with exactly the transported cylinder weight.

Constructive contract: equality transport and finite row membership only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableFiber
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSuccess

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableEvent

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableFiber
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRow
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSuccess
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

local infix:50 " ≈ " => Q'.eqv

private theorem transportTarget_mem
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (target : FiniteBistochasticTargetAssignment right)
    (hmem : target ∈ finiteBistochasticTargetAssignments right) :
    transportFiniteBistochasticTargetAssignment hpackages target ∈
      finiteBistochasticTargetAssignments left := by
  cases hpackages
  exact hmem

/-- One transported cylinder target on the proof-carrying literal observable
row. -/
abbrev ReflectedBentGuardGraftLiteralObservableTransportedChoiceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  ReflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
    (reflectedBentGuardGraftLiteralObservableRowAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLiteralObservableSeparatedEventAtCutoff
      D hcutoff hextent state)

/-- Transport a separated-cylinder target to the canonical observable target
carrier. -/
def reflectedBentGuardGraftLiteralObservableChoiceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (choice : ReflectedBentGuardGraftLiteralObservableTransportedChoiceAtCutoff
      D hcutoff hextent state) :
    SlabObservablePairedStrandRecouplingChoice D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state) :=
  transportFiniteBistochasticTargetAssignment
    (reflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
      D hcutoff hextent state).packages_eq.symm
    choice.targetPackage.target

theorem reflectedBentGuardGraftLiteralObservableChoiceAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (choice : ReflectedBentGuardGraftLiteralObservableTransportedChoiceAtCutoff
      D hcutoff hextent state) :
    reflectedBentGuardGraftLiteralObservableChoiceAtCutoff
        D hcutoff hextent state choice ∈
      slabObservablePairedStrandRecouplingChoices D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) := by
  unfold reflectedBentGuardGraftLiteralObservableChoiceAtCutoff
    slabObservablePairedStrandRecouplingChoices
    slabPhysicalPairRecouplingKernel
  exact transportTarget_mem
    (reflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
      D hcutoff hextent state).packages_eq.symm
    choice.targetPackage.target choice.targetPackage.target_mem

/-- The canonical observable-row entry is exactly the transported cylinder
entry; no normalization or product-coordinate computation is introduced. -/
theorem reflectedBentGuardGraftLiteralObservableChoiceAtCutoff_weight_eqv
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (choice : ReflectedBentGuardGraftLiteralObservableTransportedChoiceAtCutoff
      D hcutoff hextent state) :
    slabObservablePairedStrandRecouplingWeight D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftLiteralObservableChoiceAtCutoff
          D hcutoff hextent state choice) ≈
      reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
        D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
        (reflectedBentGuardGraftLiteralObservableRowAtCutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftLiteralObservableSeparatedEventAtCutoff
          D hcutoff hextent state) choice := by
  let package := reflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
    D hcutoff hextent state
  have htransport := finiteBistochasticProductWeight_transport_eqv
    package.packages_eq.symm
    (literalObservableProductionSourceAtCutoff
      D hcutoff hextent state)
    choice.targetPackage.target
  rw [package.source_eq] at htransport
  simpa only [package,
      slabObservablePairedStrandRecouplingWeight,
      slabPhysicalPairRecouplingKernel,
      literalObservableProductionSourceAtCutoff,
      reflectedBentGuardGraftLiteralObservableChoiceAtCutoff,
      reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff]
    using htransport

#print axioms reflectedBentGuardGraftLiteralObservableChoiceAtCutoff
#print axioms reflectedBentGuardGraftLiteralObservableChoiceAtCutoff_mem
#print axioms reflectedBentGuardGraftLiteralObservableChoiceAtCutoff_weight_eqv

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableEvent
