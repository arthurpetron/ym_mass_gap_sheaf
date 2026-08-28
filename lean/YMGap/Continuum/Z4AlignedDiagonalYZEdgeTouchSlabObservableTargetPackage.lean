/-
# The aligned target in the observable recoupling carrier

Project the proof-carrying aligned target package into the existing
observable recoupling row without normalizing its 1,554-coordinate dependent
tuple.  The package contains the actual target and its literal observable-row
membership.  Realization into the disconnected standard assignment graph is
the next, separately typed bridge.

Constructive contract: packaged dependent targets, canonical realization
equalities, and finite graph transport only; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableGraphBridge

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableTargetPackage

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableGraphBridge
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

structure ObservableTransportedTargetPackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (rightPackages : List FiniteBistochasticQKernelPackage)
    (hpackages : slabPhysicalPairRecouplingPackages D.extent
        source.1.1.1.1 source.1.2.1.1 = rightPackages) : Type where
  transported : TransportedTargetPackage
    (slabPhysicalPairRecouplingPackages D.extent
      source.1.1.1.1 source.1.2.1.1)
    rightPackages hpackages
  observable_mem : transported.target ∈
    slabObservablePairedStrandRecouplingChoices
      D rootFaceId targetFaceId source

def observableTransportedTargetPackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (rightPackages : List FiniteBistochasticQKernelPackage)
    (hpackages : slabPhysicalPairRecouplingPackages D.extent
        source.1.1.1.1 source.1.2.1.1 = rightPackages)
    (transported : TransportedTargetPackage
      (slabPhysicalPairRecouplingPackages D.extent
        source.1.1.1.1 source.1.2.1.1)
      rightPackages hpackages) :
    ObservableTransportedTargetPackage D rootFaceId targetFaceId
      source rightPackages hpackages :=
  { transported := transported
    observable_mem := transported.target_mem }

def alignedDiagonalSwitchObservableTargetPackageFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
    (hpackages : slabPhysicalPairRecouplingPackages 5
        alignedDiagonalSwitchRecouplingSource.1.1.1.1
        alignedDiagonalSwitchRecouplingSource.1.2.1.1 =
      AlignedDiagonalSwitchLinkedPackagesFrom linkedList) :
    ObservableTransportedTargetPackage
      alignedDiagonalSwitchPhysicalData
      alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId
      alignedDiagonalSwitchRecouplingSource
      (AlignedDiagonalSwitchLinkedPackagesFrom linkedList)
      hpackages :=
  observableTransportedTargetPackage
    alignedDiagonalSwitchPhysicalData
    alignedDiagonalSwitchRootFaceId
    alignedDiagonalSwitchTargetFaceId
    alignedDiagonalSwitchRecouplingSource
    (AlignedDiagonalSwitchLinkedPackagesFrom linkedList)
    hpackages
    (transportedTargetPackage hpackages
      (alignedDiagonalSwitchTargetMembershipPackageFrom linkedList))

def alignedDiagonalSwitchObservableTargetPackage :
    ObservableTransportedTargetPackage
      alignedDiagonalSwitchPhysicalData
      alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId
      alignedDiagonalSwitchRecouplingSource
      (AlignedDiagonalSwitchLinkedPackagesFrom
        alignedDiagonalSwitchLinkedList)
      alignedDiagonalSwitchRecouplingPackages_eq :=
  alignedDiagonalSwitchObservableTargetPackageFrom
    alignedDiagonalSwitchLinkedList
    alignedDiagonalSwitchRecouplingPackages_eq

#print axioms alignedDiagonalSwitchObservableTargetPackage

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableTargetPackage
