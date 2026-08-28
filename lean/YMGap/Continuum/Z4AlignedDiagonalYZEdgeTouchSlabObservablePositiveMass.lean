/-
# Strictly positive mass of the aligned disconnected observable channel

The successful target is a prescribed column of the physical-only SU(2)
recoupling row.  Coordinatewise positivity of that row makes its exact weight
strictly positive.  Membership of the target in the successful filter then
places this positive term inside the disconnection mass.

Constructive contract: exact physical transport, the proved product-entry
positivity, and finite nonnegative summation only; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableSuccess

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservablePositiveMass

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableGraphBridge
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableSuccess
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. Physical equality transports all-coordinate row positivity -/

theorem slabObservablePairedStrandRecouplingWeight_pos_of_reference
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (hleft : source.1.1.1.1 = referenceLeft)
    (hright : source.1.2.1.1 = referenceRight)
    (hall : ∀
      (sourceAssignment : SlabPhysicalPairRecouplingSourceAssignment
        D.extent referenceLeft referenceRight)
      (targetAssignment : SlabPhysicalPairRecouplingTargetAssignment
        D.extent referenceLeft referenceRight),
      (0 : Q') < finiteBistochasticProductWeight
        sourceAssignment targetAssignment)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :
    (0 : Q') < slabObservablePairedStrandRecouplingWeight
      D rootFaceId targetFaceId source choice := by
  cases hleft
  cases hright
  exact hall _ choice

/-! ## 2. One successful positive member makes the mass positive -/

structure ObservablePositiveDisconnectionMassCertificate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (package : ObservableVacuumDisconnectedTargetPackage
      D rootFaceId targetFaceId source
      referenceLeft referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent)
    (success : ObservableRecouplingSuccessCertificate
      D rootFaceId targetFaceId source
      referenceLeft referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent package) :
    Type where
  choiceWeight_pos : (0 : Q') <
    slabObservablePairedStrandRecouplingWeight
      D rootFaceId targetFaceId source package.realized.choice
  successful_mem : package.realized.choice ∈
    slabObservablePairedStrandSuccessfulRecouplingChoices
      D rootFaceId targetFaceId source
  disconnectionMass_pos : (0 : Q') <
    slabObservablePairedStrandDisconnectionMass
      D rootFaceId targetFaceId source

def observablePositiveDisconnectionMassCertificate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (package : ObservableVacuumDisconnectedTargetPackage
      D rootFaceId targetFaceId source
      referenceLeft referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent)
    (success : ObservableRecouplingSuccessCertificate
      D rootFaceId targetFaceId source
      referenceLeft referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent package)
    (hright : source.1.2.1.1 = referenceRight)
    (hall : ∀
      (sourceAssignment : SlabPhysicalPairRecouplingSourceAssignment
        D.extent referenceLeft referenceRight)
      (targetAssignment : SlabPhysicalPairRecouplingTargetAssignment
        D.extent referenceLeft referenceRight),
      (0 : Q') < finiteBistochasticProductWeight
        sourceAssignment targetAssignment) :
    ObservablePositiveDisconnectionMassCertificate
      D rootFaceId targetFaceId source
      referenceLeft referenceRight referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent
      package success := by
  have hweight : (0 : Q') <
      slabObservablePairedStrandRecouplingWeight
        D rootFaceId targetFaceId source package.realized.choice :=
    slabObservablePairedStrandRecouplingWeight_pos_of_reference
      D rootFaceId targetFaceId source referenceLeft referenceRight
      package.leftPhysical_eq hright hall package.realized.choice
  have hsuccessful : package.realized.choice ∈
      slabObservablePairedStrandSuccessfulRecouplingChoices
        D rootFaceId targetFaceId source := by
    unfold slabObservablePairedStrandSuccessfulRecouplingChoices
    exact List.mem_filter.mpr
      ⟨package.realized.choice_mem, success.success⟩
  refine
    { choiceWeight_pos := hweight
      successful_mem := hsuccessful
      disconnectionMass_pos := ?_ }
  unfold slabObservablePairedStrandDisconnectionMass
  exact listQSum_pos_of_mem
    (slabObservablePairedStrandRecouplingWeight
      D rootFaceId targetFaceId source)
    (slabObservablePairedStrandRecouplingWeight_nonnegative
      D rootFaceId targetFaceId source)
    (slabObservablePairedStrandSuccessfulRecouplingChoices
      D rootFaceId targetFaceId source)
    hsuccessful hweight

def alignedDiagonalObservablePositiveDisconnectionMassCertificate :
    ObservablePositiveDisconnectionMassCertificate
      alignedDiagonalSwitchPhysicalData
      alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId
      alignedDiagonalSwitchRecouplingSource
      alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchRightPhysical
      alignedDiagonalTargetMeasureIndexAssignment
      alignedDiagonalMeasureProjectedFaceEdges
      alignedDiagonalMeasureFaceVertices
      alignedDiagonalMeasureFaceAdjacentB
      alignedDiagonalObservableVacuumDisconnectedTargetPackage
      alignedDiagonalObservableRecouplingSuccessCertificate :=
  observablePositiveDisconnectionMassCertificate
    alignedDiagonalSwitchPhysicalData
    alignedDiagonalSwitchRootFaceId
    alignedDiagonalSwitchTargetFaceId
    alignedDiagonalSwitchRecouplingSource
    alignedDiagonalSwitchLeftPhysical
    alignedDiagonalSwitchRightPhysical
    alignedDiagonalTargetMeasureIndexAssignment
    alignedDiagonalMeasureProjectedFaceEdges
    alignedDiagonalMeasureFaceVertices
    alignedDiagonalMeasureFaceAdjacentB
    alignedDiagonalObservableVacuumDisconnectedTargetPackage
    alignedDiagonalObservableRecouplingSuccessCertificate
    alignedDiagonalSwitchRecouplingSource_rightPhysical
    (alignedDiagonalSwitchProductWeight_pos
      alignedDiagonalSwitchLinkedList)

#print axioms slabObservablePairedStrandRecouplingWeight_pos_of_reference
#print axioms observablePositiveDisconnectionMassCertificate
#print axioms alignedDiagonalObservablePositiveDisconnectionMassCertificate

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservablePositiveMass
