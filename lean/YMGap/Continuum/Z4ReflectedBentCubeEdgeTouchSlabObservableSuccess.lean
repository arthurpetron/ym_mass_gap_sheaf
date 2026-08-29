/-
# A positive observable recoupling row that disconnects the marked faces

Keep the complete dependent target column behind a generic realization
interface.  The realized left replica is then the already-classified
side-preserving graph, while a vacuum-labelled right replica cannot contain
even one strand-copy vertex.  Hence the paired observable graph is exactly
the disconnected left graph and the selected row is successful.

Constructive contract: exact realization, impossibility of `Fin 0`, and finite
rooted-component connectivity only; no choice, `Classical`, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableSuccess

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. A generic interface hiding the complete target tuple -/

structure ObservableChoiceLeftAssignmentPackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (expected : SlabFusionWitnessAssignment) : Type where
  choice : SlabObservablePairedStrandRecouplingChoice
    D rootFaceId targetFaceId source
  choice_mem : choice ∈ slabObservablePairedStrandRecouplingChoices
    D rootFaceId targetFaceId source
  leftAssignment_eq :
    (slabObservablePairedStrandRecoupledAssignments
      D rootFaceId targetFaceId source choice).leftAssignment = expected

def observableChoiceLeftAssignmentPackageOfTransported
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (firstLeftPhysical firstRightPhysical : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks D.extent})
    (hpackages : slabPhysicalPairRecouplingPackages D.extent
        source.1.1.1.1 source.1.2.1.1 =
      LinkedPhysicalPairPackages D.extent
        firstLeftPhysical firstRightPhysical linkedList)
    (sourceTarget : TargetMembershipPackage
      (LinkedPhysicalPairPackages D.extent
        firstLeftPhysical firstRightPhysical linkedList))
    (expected : SlabFusionWitnessAssignment)
    (certificate : TransportedLeftRealizationCertificate
      D.cutoff D.extent
      firstLeftPhysical firstRightPhysical
      source.1.1.1.1 source.1.2.1.1
      linkedList hpackages sourceTarget source.anchor expected) :
    ObservableChoiceLeftAssignmentPackage
      D rootFaceId targetFaceId source expected :=
  { choice := certificate.transported.target
    choice_mem := certificate.transported.target_mem
    leftAssignment_eq := certificate.leftAssignment_eq }

def reflectedBentObservableChoiceLeftAssignmentPackage :
    ObservableChoiceLeftAssignmentPackage
      reflectedBentPhysicalData
      reflectedBentRootFaceId
      reflectedBentTargetFaceId
      reflectedBentSwitchRecouplingSource
      reflectedBentTargetMeasureIndexAssignment :=
  observableChoiceLeftAssignmentPackageOfTransported
    reflectedBentPhysicalData
    reflectedBentRootFaceId
    reflectedBentTargetFaceId
    reflectedBentSwitchRecouplingSource
    reflectedBentSwitchLeftPhysical
    reflectedBentSwitchRightPhysical
    reflectedBentSwitchLinkedList
    reflectedBentSwitchRecouplingPackages_eq
    (reflectedBentSwitchTargetMembershipPackageFrom
      reflectedBentSwitchLinkedList)
    reflectedBentTargetMeasureIndexAssignment
    reflectedBentObservableLeftRealization

/-! ## 2. A symbolic vacuum-plus-disconnected-left certificate -/

structure ObservableVacuumDisconnectedTargetPackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referencePhysical : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool) : Type where
  realized : ObservableChoiceLeftAssignmentPackage
    D rootFaceId targetFaceId source referenceAssignment
  leftPhysical_eq : source.1.1.1.1 = referencePhysical
  rightPhysical_zero : ∀ faceId, source.1.2.1.1 faceId = 0
  referenceAssignment_mem : referenceAssignment ∈
    slabFineFusionWitnesses D referencePhysical
  referenceProjectedEdges_eq :
    slabProjectedFaceEdges
        (slabFineFusionWitnessFaceStrandEdges D referencePhysical
          referenceAssignment referenceAssignment_mem) =
      referenceProjectedEdges
  referenceVertices_eq :
    slabFaceStrandFaceVertices
        (slabFineFusionWitnessFaceStrandEdges D referencePhysical
          referenceAssignment referenceAssignment_mem) =
      referenceVertices
  referenceAdjacent_eq :
    slabProjectedFaceAdjacentB referenceProjectedEdges = referenceAdjacent
  targetPhysical : targetFaceId ∈ slabPhysicalFaceEdges D.extent
  noMarkedChain :
    ChainIn referenceAdjacent referenceVertices rootFaceId targetFaceId → False

opaque reflectedBentObservableVacuumDisconnectedTargetPackage :
    ObservableVacuumDisconnectedTargetPackage
      reflectedBentPhysicalData
      reflectedBentRootFaceId
      reflectedBentTargetFaceId
      reflectedBentSwitchRecouplingSource
      reflectedBentSwitchLeftPhysical
      reflectedBentTargetMeasureIndexAssignment
      reflectedBentMeasureProjectedFaceEdges
      reflectedBentMeasureFaceVertices
      reflectedBentMeasureFaceAdjacentB :=
  { realized := reflectedBentObservableChoiceLeftAssignmentPackage
    leftPhysical_eq := reflectedBentSwitchRecouplingSource_leftPhysical
    rightPhysical_zero := by
      intro faceId
      rw [reflectedBentSwitchRecouplingSource_rightPhysical]
      exact reflectedBentBinaryConnectedCarrier.rightPhysical_zero faceId
    referenceAssignment_mem :=
      reflectedBentTargetMeasureIndexAssignment_mem_full
    referenceProjectedEdges_eq := rfl
    referenceVertices_eq := rfl
    referenceAdjacent_eq := rfl
    targetPhysical := reflectedBentTargetFaceId_physical
    noMarkedChain := reflectedBentMeasure_noMarkedFaceChain }

/-! ## 3. Vacuum edge elimination and equality transport -/

theorem slabFaceStrandEdge_false_of_physical_zero
    {physical : SlabLabelling}
    (hzero : ∀ faceId, physical faceId = 0)
    (edge : SlabFaceStrandEdge physical) : False := by
  have hslot := edge.source.slot.isLt
  have hz := hzero edge.source.faceId
  omega

theorem slabFaceStrandEdgeList_eq_nil_of_physical_zero
    {physical : SlabLabelling}
    (hzero : ∀ faceId, physical faceId = 0)
    (edges : List (SlabFaceStrandEdge physical)) : edges = [] := by
  cases edges with
  | nil => rfl
  | cons edge _ =>
      exact (slabFaceStrandEdge_false_of_physical_zero hzero edge).elim

theorem slabProjectedFineFusionWitnessFaceStrandEdges_eq_of_eq
    (D : SlabPhysicalData)
    {firstPhysical secondPhysical : SlabLabelling}
    (hphysical : firstPhysical = secondPhysical)
    (firstAssignment secondAssignment : SlabFusionWitnessAssignment)
    (first_mem : firstAssignment ∈ slabFineFusionWitnesses D firstPhysical)
    (second_mem : secondAssignment ∈ slabFineFusionWitnesses D secondPhysical)
    (hassignment : firstAssignment = secondAssignment) :
    slabProjectedFaceEdges
        (slabFineFusionWitnessFaceStrandEdges D firstPhysical
          firstAssignment first_mem) =
      slabProjectedFaceEdges
        (slabFineFusionWitnessFaceStrandEdges D secondPhysical
          secondAssignment second_mem) := by
  cases hphysical
  cases hassignment
  rfl

theorem slabFineFusionWitnessFaceVertices_eq_of_eq
    (D : SlabPhysicalData)
    {firstPhysical secondPhysical : SlabLabelling}
    (hphysical : firstPhysical = secondPhysical)
    (firstAssignment secondAssignment : SlabFusionWitnessAssignment)
    (first_mem : firstAssignment ∈ slabFineFusionWitnesses D firstPhysical)
    (second_mem : secondAssignment ∈ slabFineFusionWitnesses D secondPhysical)
    (hassignment : firstAssignment = secondAssignment) :
    slabFaceStrandFaceVertices
        (slabFineFusionWitnessFaceStrandEdges D firstPhysical
          firstAssignment first_mem) =
      slabFaceStrandFaceVertices
        (slabFineFusionWitnessFaceStrandEdges D secondPhysical
          secondAssignment second_mem) := by
  cases hphysical
  cases hassignment
  rfl

theorem slabObservablePairedFaceConnectedB_true_root_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = true) :
    rootFaceId ∈
      rootComponent
        (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
        (slabObservableTwoReplicaPairPairedFaceVertices D pair)
        targetFaceId := by
  unfold slabObservableTwoReplicaPairPairedFaceConnectedB
    slabObservableTwoReplicaPairPairedFaceSwapMask
    slabObservableTwoReplicaPairTargetFaceComponent at hconnected
  exact of_decide_eq_true hconnected

theorem slabObservablePairedFaceConnectedB_false_of_no_chain
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (hpair : pair ∈
      slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
    (referenceAdjacent : Nat → Nat → Bool)
    (referenceVertices : List Nat)
    (hadjacent :
      slabObservableTwoReplicaPairPairedFaceAdjacentB D pair =
        referenceAdjacent)
    (hvertices :
      slabObservableTwoReplicaPairPairedFaceVertices D pair =
        referenceVertices)
    (hnoChain :
      ChainIn referenceAdjacent referenceVertices
        rootFaceId targetFaceId → False) :
    slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = false := by
  cases hvalue : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair with
  | false => rfl
  | true =>
      have htargetVertex :=
        slabObservableTwoReplicaPairTarget_mem_pairedFaceVertices
          D rootFaceId targetFaceId htarget pair hpair
      have htargetComponent : targetFaceId ∈
          rootComponent
            (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
            (slabObservableTwoReplicaPairPairedFaceVertices D pair)
            targetFaceId :=
        root_mem_rootComponent _ htargetVertex
      have hrootComponent :=
        slabObservablePairedFaceConnectedB_true_root_mem
          D rootFaceId targetFaceId pair hvalue
      have hchain := rootComponent_connected
        (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
        (slabObservableTwoReplicaPairPairedFaceAdjacentB_symmetric D pair)
        htargetVertex rootFaceId targetFaceId
        hrootComponent htargetComponent
      have hchainFull : ChainIn
          (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
          (slabObservableTwoReplicaPairPairedFaceVertices D pair)
          rootFaceId targetFaceId :=
        ChainIn.mono
          (fun point hpoint => rootComponent_subset
            (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
            htargetVertex hpoint)
          hchain
      exact (hnoChain
        (transportChainIn hadjacent hvertices hchainFull)).elim

/-! ## 4. The generic certificate contracts to observable success -/

structure ObservableRecouplingSuccessCertificate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referencePhysical : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (package : ObservableVacuumDisconnectedTargetPackage
      D rootFaceId targetFaceId source
      referencePhysical referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent) : Type where
  success : slabObservablePairedStrandRecouplingSuccessB
    D rootFaceId targetFaceId source package.realized.choice = true

def observableVacuumDisconnectedTargetSuccessCertificate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referencePhysical : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (package : ObservableVacuumDisconnectedTargetPackage
      D rootFaceId targetFaceId source
      referencePhysical referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent) :
    ObservableRecouplingSuccessCertificate
      D rootFaceId targetFaceId source
      referencePhysical referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent package := by
  let pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source package.realized.choice
  have hleftPhysical : pair.1.1.1 = referencePhysical := by
    exact package.leftPhysical_eq
  have hleftAssignment : pair.1.1.2 = referenceAssignment := by
    exact package.realized.leftAssignment_eq
  have hrightZero : ∀ faceId, pair.2.1.1 faceId = 0 := by
    intro faceId
    exact package.rightPhysical_zero faceId
  have hrightEdges :
      slabObservableTwoReplicaPairRightStrandEdges D pair = [] :=
    slabFaceStrandEdgeList_eq_nil_of_physical_zero hrightZero _
  have hleftProjected :
      slabProjectedFaceEdges
          (slabObservableTwoReplicaPairLeftStrandEdges D pair) =
        referenceProjectedEdges := by
    refine (slabProjectedFineFusionWitnessFaceStrandEdges_eq_of_eq
      D hleftPhysical pair.1.1.2 referenceAssignment
      pair.1.assignment_mem package.referenceAssignment_mem
      hleftAssignment).trans ?_
    exact package.referenceProjectedEdges_eq
  have hleftVertices :
      slabFaceStrandFaceVertices
          (slabObservableTwoReplicaPairLeftStrandEdges D pair) =
        referenceVertices := by
    refine (slabFineFusionWitnessFaceVertices_eq_of_eq
      D hleftPhysical pair.1.1.2 referenceAssignment
      pair.1.assignment_mem package.referenceAssignment_mem
      hleftAssignment).trans ?_
    exact package.referenceVertices_eq
  have hpairedEdges :
      slabObservableTwoReplicaPairPairedFaceEdges D pair =
        referenceProjectedEdges := by
    unfold slabObservableTwoReplicaPairPairedFaceEdges
    rw [hleftProjected, hrightEdges]
    simp [slabProjectedFaceEdges]
  have hpairedVertices :
      slabObservableTwoReplicaPairPairedFaceVertices D pair =
        referenceVertices := by
    unfold slabObservableTwoReplicaPairPairedFaceVertices
    rw [hleftVertices, hrightEdges]
    simp [slabFaceStrandFaceVertices, slabFaceStrandVertices]
  have hpairedAdjacent :
      slabObservableTwoReplicaPairPairedFaceAdjacentB D pair =
        referenceAdjacent := by
    funext left right
    unfold slabObservableTwoReplicaPairPairedFaceAdjacentB
    rw [hpairedEdges]
    exact congrFun (congrFun package.referenceAdjacent_eq left) right
  have hpair_mem : pair ∈
      slabObservableFourCellSourcePairs D rootFaceId targetFaceId :=
    slabObservablePairedStrandRecoupledPair_mem_source
      D rootFaceId targetFaceId source package.realized.choice
  have hconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = false :=
    slabObservablePairedFaceConnectedB_false_of_no_chain
      D rootFaceId targetFaceId pair package.targetPhysical hpair_mem
      referenceAdjacent referenceVertices
      hpairedAdjacent hpairedVertices package.noMarkedChain
  refine { success := ?_ }
  unfold slabObservablePairedStrandRecouplingSuccessB
  rw [hconnected]
  rfl

def reflectedBentObservableRecouplingSuccessCertificate :
    ObservableRecouplingSuccessCertificate
      reflectedBentPhysicalData
      reflectedBentRootFaceId
      reflectedBentTargetFaceId
      reflectedBentSwitchRecouplingSource
      reflectedBentSwitchLeftPhysical
      reflectedBentTargetMeasureIndexAssignment
      reflectedBentMeasureProjectedFaceEdges
      reflectedBentMeasureFaceVertices
      reflectedBentMeasureFaceAdjacentB
      reflectedBentObservableVacuumDisconnectedTargetPackage :=
  observableVacuumDisconnectedTargetSuccessCertificate
    reflectedBentPhysicalData
    reflectedBentRootFaceId
    reflectedBentTargetFaceId
    reflectedBentSwitchRecouplingSource
    reflectedBentSwitchLeftPhysical
    reflectedBentTargetMeasureIndexAssignment
    reflectedBentMeasureProjectedFaceEdges
    reflectedBentMeasureFaceVertices
    reflectedBentMeasureFaceAdjacentB
    reflectedBentObservableVacuumDisconnectedTargetPackage

#print axioms reflectedBentObservableChoiceLeftAssignmentPackage
#print axioms reflectedBentObservableVacuumDisconnectedTargetPackage
#print axioms slabFaceStrandEdgeList_eq_nil_of_physical_zero
#print axioms observableVacuumDisconnectedTargetSuccessCertificate
#print axioms reflectedBentObservableRecouplingSuccessCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableSuccess
