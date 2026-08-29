/-
# The reflected bent target in the observable recoupling carrier

Project the proof-carrying reflected target into the observable recoupling
row without normalizing its large dependent tuple.  The package contains the
actual target and its literal observable-row membership.

Constructive contract: packaged dependent targets and finite membership only;
no choice, `Classical`, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableTargetPackage

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges

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

def reflectedBentSwitchObservableTargetPackageFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
    (hpackages : slabPhysicalPairRecouplingPackages 5
        reflectedBentSwitchRecouplingSource.1.1.1.1
        reflectedBentSwitchRecouplingSource.1.2.1.1 =
      ReflectedBentSwitchLinkedPackagesFrom linkedList) :
    ObservableTransportedTargetPackage
      reflectedBentPhysicalData reflectedBentRootFaceId
      reflectedBentTargetFaceId reflectedBentSwitchRecouplingSource
      (ReflectedBentSwitchLinkedPackagesFrom linkedList) hpackages :=
  observableTransportedTargetPackage
    reflectedBentPhysicalData reflectedBentRootFaceId
    reflectedBentTargetFaceId reflectedBentSwitchRecouplingSource
    (ReflectedBentSwitchLinkedPackagesFrom linkedList) hpackages
    (transportedTargetPackage hpackages
      (reflectedBentSwitchTargetMembershipPackageFrom linkedList))

def reflectedBentSwitchObservableTargetPackage :
    ObservableTransportedTargetPackage
      reflectedBentPhysicalData reflectedBentRootFaceId
      reflectedBentTargetFaceId reflectedBentSwitchRecouplingSource
      (ReflectedBentSwitchLinkedPackagesFrom reflectedBentSwitchLinkedList)
      reflectedBentSwitchRecouplingPackages_eq :=
  reflectedBentSwitchObservableTargetPackageFrom
    reflectedBentSwitchLinkedList reflectedBentSwitchRecouplingPackages_eq

#print axioms reflectedBentSwitchObservableTargetPackage

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableTargetPackage
