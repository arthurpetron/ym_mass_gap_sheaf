/-
# The two-pivot repair target is a positive observable good channel

Identify the standard observable assignment graph with the already proved
two-lobe target graph, transport the finite target through the literal source
anchor, and reuse the generic vacuum-plus-disconnection compiler.  The same
selected target then has strictly positive recoupling weight and supplies a
connected positive channel, a canonical good source, and the finite constant
physical-repair certificate.

Constructive contract: exact assignment and graph equalities, finite positive
mass, and existing explicit repair moduli only; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableConstantGoodSourceRepair
import YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabObservableChoice
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabObservablePositiveChannel

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting
open YMGap.Continuum.CompactDualSlabObservableConstantGoodSourceRepair
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceRepairContraction
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabObservableChoice
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetAssignment
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetDisconnection
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetEdges
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetRealization
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabWholeProductPositivity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservablePositiveMass
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableSuccess
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

/-! ## 1. The standard assignment graph is the classified target graph -/

theorem outwardYZCanonicalRepairRealizedAssignmentAt_eq :
    ∀ (linkedList :
        List {link // link ∈ boundaryCompleteSlabLinks 5})
      (linked : {link // link ∈ boundaryCompleteSlabLinks 5}),
      linked ∈ linkedList →
      slabFusionWitnessAssignmentAt linked.1
          (outwardYZCanonicalRepairRealizedLeftAssignmentFrom linkedList) =
        outwardYZCanonicalRepairRealizedLeftAuxiliary linked
  | [], linked, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, linked, hmem => by
      by_cases hsame : head.1 = linked.1
      · have hsubtype : head = linked := Subtype.ext hsame
        subst head
        simp [slabFusionWitnessAssignmentAt,
          outwardYZCanonicalRepairRealizedLeftAssignmentFrom]
      · have hrest : linked ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim
              (hsame (congrArg Subtype.val hhead.symm))
          · exact htail
        simp only [outwardYZCanonicalRepairRealizedLeftAssignmentFrom,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact outwardYZCanonicalRepairRealizedAssignmentAt_eq
          rest linked hrest

theorem outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem_full :
    outwardYZCanonicalRepairTargetMeasureIndexAssignment ∈
      slabFusionWitnessAssignmentsOn 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
  simpa only [outwardYZCanonicalRepairTargetMeasureIndexAssignment,
    outwardYZCanonicalRepairSwitchLinkedList,
    List.attach_map_subtype_val] using
      outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem

def outwardYZCanonicalRepairMeasureFaceStrandEdges :
    List (SlabFaceStrandEdge
      outwardYZCanonicalRepairSwitchLeftPhysical) :=
  slabFusionWitnessAssignmentFaceStrandEdges 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    (boundaryCompleteSlabLinks 5)
    outwardYZCanonicalRepairTargetMeasureIndexAssignment
    outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem_full

theorem outwardYZCanonicalRepairMeasureFaceStrandEdges_eq_target :
    outwardYZCanonicalRepairMeasureFaceStrandEdges =
      outwardYZCanonicalRepairTargetFaceStrandEdges := by
  unfold outwardYZCanonicalRepairMeasureFaceStrandEdges
    slabFusionWitnessAssignmentFaceStrandEdges
    outwardYZCanonicalRepairTargetFaceStrandEdges
  change outwardYZCanonicalRepairSwitchLinkedList.flatMap
      (slabFusionWitnessAssignmentFaceStrandEdgesAt 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5)
        outwardYZCanonicalRepairTargetMeasureIndexAssignment
        outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem_full) =
    outwardYZCanonicalRepairSwitchLinkedList.flatMap
      outwardYZCanonicalRepairTargetFaceStrandEdgesAt
  apply congrArg (fun compiler =>
    outwardYZCanonicalRepairSwitchLinkedList.flatMap compiler)
  funext linked
  unfold slabFusionWitnessAssignmentFaceStrandEdgesAt
    outwardYZCanonicalRepairTargetFaceStrandEdgesAt
    outwardYZCanonicalRepairTargetMeasureIndexAssignment
  have hlookup := outwardYZCanonicalRepairRealizedAssignmentAt_eq
    outwardYZCanonicalRepairSwitchLinkedList linked
    (List.mem_attach (boundaryCompleteSlabLinks 5) linked)
  exact slabLinkFaceStrandEdges_eq_of_auxiliary_eq _ _ hlookup

def outwardYZCanonicalRepairMeasureProjectedFaceEdges :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges outwardYZCanonicalRepairMeasureFaceStrandEdges

def outwardYZCanonicalRepairMeasureFaceVertices : List Nat :=
  slabFaceStrandFaceVertices outwardYZCanonicalRepairMeasureFaceStrandEdges

def outwardYZCanonicalRepairMeasureFaceAdjacentB
    (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB
    outwardYZCanonicalRepairMeasureProjectedFaceEdges left right

theorem outwardYZCanonicalRepairMeasureProjectedFaceEdges_eq_target :
    outwardYZCanonicalRepairMeasureProjectedFaceEdges =
      outwardYZCanonicalRepairTargetProjectedFaceEdges :=
  congrArg slabProjectedFaceEdges
    outwardYZCanonicalRepairMeasureFaceStrandEdges_eq_target

theorem outwardYZCanonicalRepairMeasureFaceVertices_eq_target :
    outwardYZCanonicalRepairMeasureFaceVertices =
      outwardYZCanonicalRepairTargetFaceVertices :=
  congrArg slabFaceStrandFaceVertices
    outwardYZCanonicalRepairMeasureFaceStrandEdges_eq_target

theorem outwardYZCanonicalRepairMeasureFaceAdjacentB_eq_target :
    outwardYZCanonicalRepairMeasureFaceAdjacentB =
      outwardYZCanonicalRepairTargetFaceAdjacentB := by
  funext left right
  unfold outwardYZCanonicalRepairMeasureFaceAdjacentB
    outwardYZCanonicalRepairTargetFaceAdjacentB
  rw [outwardYZCanonicalRepairMeasureProjectedFaceEdges_eq_target]

def outwardYZCanonicalRepairMeasure_noMarkedFaceChain :
    ChainIn outwardYZCanonicalRepairMeasureFaceAdjacentB
      outwardYZCanonicalRepairMeasureFaceVertices
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId → False :=
  fun path => by
    apply outwardYZCanonicalRepairTarget_noMarkedFaceChain
    exact transportChainIn
      outwardYZCanonicalRepairMeasureFaceAdjacentB_eq_target
      outwardYZCanonicalRepairMeasureFaceVertices_eq_target path

/-! ## 2. Transport the finite target through the observable source -/

theorem outwardYZCanonicalRepairLinkedLeftRealization_eq
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical
      outwardYZCanonicalRepairLeftFineWitness.1
      outwardYZCanonicalRepairRightFineWitness.1
      outwardYZCanonicalRepairSwitchLeftAssignment_mem
      outwardYZCanonicalRepairSwitchRightAssignment_mem
      outwardYZCanonicalRepairSwitchLeftPhysical_bounded
      outwardYZCanonicalRepairSwitchRightPhysical_bounded linkedList
      (outwardYZCanonicalRepairTargetMembershipPackageFrom
        linkedList).target).leftAssignment =
          outwardYZCanonicalRepairRealizedLeftAssignmentFrom linkedList := by
  rw [outwardYZCanonicalRepairTargetMembershipPackageFrom_target]
  exact
    (outwardYZCanonicalRepairRealizedLeftAssignmentFrom_eq_canonical
      linkedList).symm

theorem outwardYZCanonicalRepairSwitchLinkedList_eq_attach :
    outwardYZCanonicalRepairSwitchLinkedList =
      (boundaryCompleteSlabLinks 5).attach := rfl

def outwardYZCanonicalRepairObservableLeftRealization :
    TransportedLeftRealizationCertificate 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical
      outwardYZCanonicalRepairRecouplingSource.1.1.1.1
      outwardYZCanonicalRepairRecouplingSource.1.2.1.1
      outwardYZCanonicalRepairSwitchLinkedList
      outwardYZCanonicalRepairRecouplingPackages_eq
      (outwardYZCanonicalRepairTargetMembershipPackageFrom
        outwardYZCanonicalRepairSwitchLinkedList)
      outwardYZCanonicalRepairRecouplingSource.anchor
      outwardYZCanonicalRepairTargetMeasureIndexAssignment :=
  transportLinkedLeftRealizationCertificate
    outwardYZCanonicalRepairRecouplingSource_leftPhysical.symm
    outwardYZCanonicalRepairRecouplingSource_rightPhysical.symm
    outwardYZCanonicalRepairSwitchLinkedList
    outwardYZCanonicalRepairSwitchLinkedList_eq_attach
    outwardYZCanonicalRepairRecouplingPackages_eq
    outwardYZCanonicalRepairTargetMembershipPackageFrom
    outwardYZCanonicalRepairLeftFineWitness.1
    outwardYZCanonicalRepairRightFineWitness.1
    outwardYZCanonicalRepairSwitchLeftAssignment_mem
    outwardYZCanonicalRepairSwitchRightAssignment_mem
    outwardYZCanonicalRepairSwitchLeftPhysical_bounded
    outwardYZCanonicalRepairSwitchRightPhysical_bounded
    outwardYZCanonicalRepairRecouplingSource.anchor
    outwardYZCanonicalRepairRealizedLeftAssignmentFrom
    outwardYZCanonicalRepairLinkedLeftRealization_eq

def outwardYZCanonicalRepairObservableChoiceLeftAssignmentPackage :
    ObservableChoiceLeftAssignmentPackage
      outwardYZCanonicalRepairPhysicalData
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId
      outwardYZCanonicalRepairRecouplingSource
      outwardYZCanonicalRepairTargetMeasureIndexAssignment :=
  observableChoiceLeftAssignmentPackageOfTransported
    outwardYZCanonicalRepairPhysicalData
    outwardYZCanonicalRepairRootFaceId
    outwardYZCanonicalRepairTargetFaceId
    outwardYZCanonicalRepairRecouplingSource
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchRightPhysical
    outwardYZCanonicalRepairSwitchLinkedList
    outwardYZCanonicalRepairRecouplingPackages_eq
    (outwardYZCanonicalRepairTargetMembershipPackageFrom
      outwardYZCanonicalRepairSwitchLinkedList)
    outwardYZCanonicalRepairTargetMeasureIndexAssignment
    outwardYZCanonicalRepairObservableLeftRealization

/-! ## 3. Generic vacuum elimination gives observable success -/

opaque outwardYZCanonicalRepairObservableVacuumDisconnectedTargetPackage :
    ObservableVacuumDisconnectedTargetPackage
      outwardYZCanonicalRepairPhysicalData
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId
      outwardYZCanonicalRepairRecouplingSource
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairTargetMeasureIndexAssignment
      outwardYZCanonicalRepairMeasureProjectedFaceEdges
      outwardYZCanonicalRepairMeasureFaceVertices
      outwardYZCanonicalRepairMeasureFaceAdjacentB :=
  { realized :=
      outwardYZCanonicalRepairObservableChoiceLeftAssignmentPackage
    leftPhysical_eq :=
      outwardYZCanonicalRepairRecouplingSource_leftPhysical
    rightPhysical_zero := by
      intro faceId
      rw [outwardYZCanonicalRepairRecouplingSource_rightPhysical]
      exact
        outwardYZCanonicalRepairBinaryConnectedCarrier.rightPhysical_zero
          faceId
    referenceAssignment_mem :=
      outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem_full
    referenceProjectedEdges_eq := rfl
    referenceVertices_eq := rfl
    referenceAdjacent_eq := rfl
    targetPhysical := outwardYZCanonicalRepairTargetFaceId_physical
    noMarkedChain := outwardYZCanonicalRepairMeasure_noMarkedFaceChain }

def outwardYZCanonicalRepairObservableRecouplingSuccessCertificate :
    ObservableRecouplingSuccessCertificate
      outwardYZCanonicalRepairPhysicalData
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId
      outwardYZCanonicalRepairRecouplingSource
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairTargetMeasureIndexAssignment
      outwardYZCanonicalRepairMeasureProjectedFaceEdges
      outwardYZCanonicalRepairMeasureFaceVertices
      outwardYZCanonicalRepairMeasureFaceAdjacentB
      outwardYZCanonicalRepairObservableVacuumDisconnectedTargetPackage :=
  observableVacuumDisconnectedTargetSuccessCertificate
    outwardYZCanonicalRepairPhysicalData
    outwardYZCanonicalRepairRootFaceId
    outwardYZCanonicalRepairTargetFaceId
    outwardYZCanonicalRepairRecouplingSource
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairTargetMeasureIndexAssignment
    outwardYZCanonicalRepairMeasureProjectedFaceEdges
    outwardYZCanonicalRepairMeasureFaceVertices
    outwardYZCanonicalRepairMeasureFaceAdjacentB
    outwardYZCanonicalRepairObservableVacuumDisconnectedTargetPackage

/-! ## 4. Positive mass and the connected good receiver -/

def outwardYZCanonicalRepairObservablePositiveDisconnectionMassCertificate :
    ObservablePositiveDisconnectionMassCertificate
      outwardYZCanonicalRepairPhysicalData
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId
      outwardYZCanonicalRepairRecouplingSource
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical
      outwardYZCanonicalRepairTargetMeasureIndexAssignment
      outwardYZCanonicalRepairMeasureProjectedFaceEdges
      outwardYZCanonicalRepairMeasureFaceVertices
      outwardYZCanonicalRepairMeasureFaceAdjacentB
      outwardYZCanonicalRepairObservableVacuumDisconnectedTargetPackage
      outwardYZCanonicalRepairObservableRecouplingSuccessCertificate :=
  observablePositiveDisconnectionMassCertificate
    outwardYZCanonicalRepairPhysicalData
    outwardYZCanonicalRepairRootFaceId
    outwardYZCanonicalRepairTargetFaceId
    outwardYZCanonicalRepairRecouplingSource
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchRightPhysical
    outwardYZCanonicalRepairTargetMeasureIndexAssignment
    outwardYZCanonicalRepairMeasureProjectedFaceEdges
    outwardYZCanonicalRepairMeasureFaceVertices
    outwardYZCanonicalRepairMeasureFaceAdjacentB
    outwardYZCanonicalRepairObservableVacuumDisconnectedTargetPackage
    outwardYZCanonicalRepairObservableRecouplingSuccessCertificate
    outwardYZCanonicalRepairRecouplingSource_rightPhysical
    (outwardYZCanonicalRepairSwitchProductWeight_pos
      outwardYZCanonicalRepairSwitchLinkedList)

abbrev outwardYZCanonicalRepairConnectedRecouplingSource :=
  SlabObservablePairedConnectedStrandSource.toRecouplingSource
    outwardYZCanonicalRepairConnectedStrandSource

theorem outwardYZCanonicalRepairRecouplingSource_eq_connected :
    outwardYZCanonicalRepairRecouplingSource =
      outwardYZCanonicalRepairConnectedRecouplingSource := by
  apply Subtype.ext
  exact outwardYZCanonicalRepairRecouplingSource_sourcePair

def outwardYZCanonicalRepairConnectedPositivePackage :
    ObservableConnectedPositivePackage
      outwardYZCanonicalRepairPhysicalData
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId
      outwardYZCanonicalRepairConnectedRecouplingSource
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical
      outwardYZCanonicalRepairTargetMeasureIndexAssignment
      outwardYZCanonicalRepairMeasureProjectedFaceEdges
      outwardYZCanonicalRepairMeasureFaceVertices
      outwardYZCanonicalRepairMeasureFaceAdjacentB :=
  transportObservableConnectedPositivePackage
    outwardYZCanonicalRepairRecouplingSource_eq_connected
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchRightPhysical
    outwardYZCanonicalRepairTargetMeasureIndexAssignment
    outwardYZCanonicalRepairMeasureProjectedFaceEdges
    outwardYZCanonicalRepairMeasureFaceVertices
    outwardYZCanonicalRepairMeasureFaceAdjacentB
    outwardYZCanonicalRepairObservableVacuumDisconnectedTargetPackage
    outwardYZCanonicalRepairObservableRecouplingSuccessCertificate
    outwardYZCanonicalRepairObservablePositiveDisconnectionMassCertificate

def outwardYZCanonicalRepairPositiveChannelWitness :
    SlabObservablePairedConnectedPositiveChannelWitness
      outwardYZCanonicalRepairPhysicalData
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId :=
  observablePairedConnectedPositiveChannelOfPackage
    outwardYZCanonicalRepairPhysicalData
    outwardYZCanonicalRepairRootFaceId
    outwardYZCanonicalRepairTargetFaceId
    outwardYZCanonicalRepairConnectedStrandSource
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchRightPhysical
    outwardYZCanonicalRepairTargetMeasureIndexAssignment
    outwardYZCanonicalRepairMeasureProjectedFaceEdges
    outwardYZCanonicalRepairMeasureFaceVertices
    outwardYZCanonicalRepairMeasureFaceAdjacentB
    outwardYZCanonicalRepairConnectedPositivePackage

theorem outwardYZCanonicalRepairPhysicalData_coupling_pos :
    (0 : Q') < outwardYZCanonicalRepairPhysicalData.coupling := by
  decide

def outwardYZCanonicalRepairCanonicalGoodSource :=
  canonicalGoodSourceOfPositiveChannel
    outwardYZCanonicalRepairPositiveChannelWitness

def outwardYZCanonicalRepairConstantGoodSourceRepair :=
  slabObservablePairedConnectedCanonicalConstantGoodSourceRepair
    outwardYZCanonicalRepairPhysicalData
    outwardYZCanonicalRepairPhysicalData_coupling_pos
    outwardYZCanonicalRepairRootFaceId
    outwardYZCanonicalRepairTargetFaceId
    outwardYZCanonicalRepairPositiveChannelWitness

/-! ## 5. The known seven-cube bad source reaches this receiver -/

def outwardYZCanonicalRepairSevenCubeRepairOutput :=
  outwardYZCanonicalRepairConstantGoodSourceRepair.repair
    sevenCubeSwitchConnectedStrandSource

theorem outwardYZCanonicalRepairSevenCubeRepairOutput_eq_goodSource :
    outwardYZCanonicalRepairSevenCubeRepairOutput =
      outwardYZCanonicalRepairCanonicalGoodSource := by
  rfl

#print axioms outwardYZCanonicalRepairMeasureFaceStrandEdges_eq_target
#print axioms outwardYZCanonicalRepairMeasure_noMarkedFaceChain
#print axioms outwardYZCanonicalRepairObservableLeftRealization
#print axioms outwardYZCanonicalRepairObservableRecouplingSuccessCertificate
#print axioms outwardYZCanonicalRepairObservablePositiveDisconnectionMassCertificate
#print axioms outwardYZCanonicalRepairPositiveChannelWitness
#print axioms outwardYZCanonicalRepairCanonicalGoodSource
#print axioms outwardYZCanonicalRepairConstantGoodSourceRepair
#print axioms outwardYZCanonicalRepairSevenCubeRepairOutput_eq_goodSource

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabObservablePositiveChannel
