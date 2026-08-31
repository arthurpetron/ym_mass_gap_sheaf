/-
# Every literal separated-cylinder observable choice succeeds

Each proof-carrying member of the literal observable cylinder is transported
to the canonical observable row.  Its canonical realization agrees with the
recursive guarded realization, whose standard projected graph was proved to
separate the marked faces.  This module contracts those facts to the actual
observable success Boolean without exposing the enormous dependent target
tuple at the public theorem boundary.

Constructive contract: equality transport, proof irrelevance, and exact graph
comparison only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableEvent
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraphBridge
import YMGap.Continuum.CompactDualSlabTransportedPairedRealizationCertificate
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChannel

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccess

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabTransportedPairedRealizationCertificate
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableFiber
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRow
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChannel
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSuccess
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

local infix:50 " ≈ " => YMGap.Constructive.Q'.eqv

private theorem transportTarget_mem_local
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (target : FiniteBistochasticTargetAssignment right)
    (target_mem : target ∈ finiteBistochasticTargetAssignments right) :
    transportFiniteBistochasticTargetAssignment hpackages target ∈
      finiteBistochasticTargetAssignments left := by
  cases hpackages
  exact target_mem

private theorem transportTarget_injective_local
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (first second : FiniteBistochasticTargetAssignment right)
    (heq : transportFiniteBistochasticTargetAssignment hpackages first =
      transportFiniteBistochasticTargetAssignment hpackages second) :
    first = second := by
  cases hpackages
  exact heq

/-- The cylinder weight with its large row and event parameters hidden behind
a unary boundary on the proof-carrying literal choice. -/
def reflectedBentGuardGraftLiteralObservableTransportedChoiceWeightAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (choice : ReflectedBentGuardGraftLiteralObservableTransportedChoiceAtCutoff
      D hcutoff hextent state) : YMGap.Constructive.Q' :=
  reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
    (reflectedBentGuardGraftLiteralObservableRowAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLiteralObservableSeparatedEventAtCutoff
      D hcutoff hextent state) choice

/-- The proof-carrying cylinder list behind a light finite-index boundary. -/
def reflectedBentGuardGraftLiteralObservableTransportedChoicesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  reflectedBentGuardGraftPivotCylinderTransportedChoicesAtCutoff
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
    (reflectedBentGuardGraftLiteralObservableRowAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLiteralObservableSeparatedEventAtCutoff
      D hcutoff hextent state)

/-- Weight of the cylinder member at a finite index, without exposing that
member in later result types. -/
def reflectedBentGuardGraftLiteralObservableCylinderWeightAtIndex
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (index : Fin
      (reflectedBentGuardGraftLiteralObservableTransportedChoicesAtCutoff
        D hcutoff hextent state).length) : YMGap.Constructive.Q' :=
  reflectedBentGuardGraftLiteralObservableTransportedChoiceWeightAtCutoff
    D hcutoff hextent state
    ((reflectedBentGuardGraftLiteralObservableTransportedChoicesAtCutoff
      D hcutoff hextent state).get index)

/-- Generic successful weighted choice.  Keeping the row source symbolic is
the small boundary that prevents concrete dependent target normalization. -/
structure ObservableSuccessfulWeightedChoice
    (D : SlabPhysicalData) : Type where
  rootFaceId : Nat
  targetFaceId : Nat
  source : SlabObservablePairedStrandRecouplingSource
    D rootFaceId targetFaceId
  observableChoice : SlabObservablePairedStrandRecouplingChoice D
    rootFaceId targetFaceId source
  observableChoice_mem : observableChoice ∈
    slabObservablePairedStrandRecouplingChoices D
      rootFaceId targetFaceId source
  success : slabObservablePairedStrandRecouplingSuccessB D
    rootFaceId targetFaceId source observableChoice = true

/-- Inductive serialization boundary for a successful symbolic choice. -/
inductive ObservableSuccessfulWeightedChoiceExists
    (D : SlabPhysicalData) : Type where
  | mk (package : ObservableSuccessfulWeightedChoice D)

def observableSuccessfulWeightedChoiceExistsOfDisconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source)
    (choice_mem : choice ∈ slabObservablePairedStrandRecouplingChoices
      D rootFaceId targetFaceId source)
    (referenceLeft referenceRight : SlabLabelling)
    (referenceLeftAssignment referenceRightAssignment :
      SlabFusionWitnessAssignment)
    (referenceLeft_mem : referenceLeftAssignment ∈
      slabFineFusionWitnesses D referenceLeft)
    (referenceRight_mem : referenceRightAssignment ∈
      slabFineFusionWitnesses D referenceRight)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (hleftPhysical : source.1.1.1.1 = referenceLeft)
    (hrightPhysical : source.1.2.1.1 = referenceRight)
    (hleftAssignment : (source.anchor.realize choice).leftAssignment =
      referenceLeftAssignment)
    (hrightAssignment : (source.anchor.realize choice).rightAssignment =
      referenceRightAssignment)
    (hprojected :
      slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment referenceLeft_mem) ++
        slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment referenceRight_mem) =
      referenceProjectedEdges)
    (hvertices :
      slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment referenceLeft_mem) ++
        slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment referenceRight_mem) =
      referenceVertices)
    (hadjacent : slabProjectedFaceAdjacentB referenceProjectedEdges =
      referenceAdjacent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (hnoChain : ChainIn referenceAdjacent referenceVertices
      rootFaceId targetFaceId → False) :
    ObservableSuccessfulWeightedChoiceExists D := by
  have hsuccess := slabObservablePairedNonvacuumDisconnectedTargetSuccess
    D rootFaceId targetFaceId source choice referenceLeft referenceRight
    referenceLeftAssignment referenceRightAssignment
    referenceLeft_mem referenceRight_mem referenceProjectedEdges
    referenceVertices referenceAdjacent hleftPhysical hrightPhysical
    hleftAssignment hrightAssignment hprojected hvertices hadjacent
    htarget hnoChain
  exact .mk
    { rootFaceId := rootFaceId
      targetFaceId := targetFaceId
      source := source
      observableChoice := choice
      observableChoice_mem := choice_mem
      success := hsuccess }

def ObservableSuccessfulWeightedChoiceExists.ofDisconnectedPackage
    {D : SlabPhysicalData}
    (package : ObservablePairedDisconnectedTargetPackage D) :
    ObservableSuccessfulWeightedChoiceExists D :=
  .mk
    { rootFaceId := package.rootFaceId
      targetFaceId := package.targetFaceId
      source := package.source
      observableChoice := package.realized.choice
      observableChoice_mem := package.realized.choice_mem
      success := package.success }

/-- Extent-transported boundary for the generic disconnected-target builder.
The equality is eliminated while all package and graph data remain symbolic,
so a concrete extent-five caller never asks elaboration to identify its large
linked product with `D.extent` argument by argument. -/
def observablePairedDisconnectedTargetPackageOfTransportedAtExtent
    (D : SlabPhysicalData) (extent : Nat) (hextent : D.extent = extent)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hpackages : slabPhysicalPairRecouplingPackages extent
        source.1.1.1.1 source.1.2.1.1 =
      LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList)
    (sourceTarget : TargetMembershipPackage
      (LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList))
    (referenceLeftAssignment referenceRightAssignment :
      SlabFusionWitnessAssignment)
    (certificate : TransportedPairedRealizationCertificate
      D.cutoff extent referenceLeft referenceRight
      source.1.1.1.1 source.1.2.1.1 linkedList hpackages
      sourceTarget
      (by simpa only [hextent] using source.anchor)
      referenceLeftAssignment referenceRightAssignment)
    (leftPhysical_eq : source.1.1.1.1 = referenceLeft)
    (rightPhysical_eq : source.1.2.1.1 = referenceRight)
    (leftAssignment_mem : referenceLeftAssignment ∈
      slabFineFusionWitnesses D referenceLeft)
    (rightAssignment_mem : referenceRightAssignment ∈
      slabFineFusionWitnesses D referenceRight)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (projectedEdges_eq :
      slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment leftAssignment_mem) ++
        slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment rightAssignment_mem) =
        referenceProjectedEdges)
    (vertices_eq :
      slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment leftAssignment_mem) ++
        slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment rightAssignment_mem) =
        referenceVertices)
    (adjacent_eq :
      slabProjectedFaceAdjacentB referenceProjectedEdges = referenceAdjacent)
    (targetPhysical : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (noMarkedChain : ChainIn referenceAdjacent referenceVertices
      rootFaceId targetFaceId → False) :
    ObservablePairedDisconnectedTargetPackage D := by
  cases hextent
  exact observablePairedDisconnectedTargetPackageOfTransported
    D rootFaceId targetFaceId source referenceLeft referenceRight
    linkedList hpackages sourceTarget referenceLeftAssignment
    referenceRightAssignment certificate leftPhysical_eq rightPhysical_eq
    leftAssignment_mem rightAssignment_mem referenceProjectedEdges
    referenceVertices referenceAdjacent projectedEdges_eq vertices_eq
    adjacent_eq targetPhysical noMarkedChain

/-- Transport one written-link target into the canonical observable row after
eliminating the extent equality at a symbolic boundary. -/
def observablePairedTargetOfWrittenAtExtent
    (D : SlabPhysicalData) (extent : Nat) (hextent : D.extent = extent)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hpackages : slabPhysicalPairRecouplingPackages extent
        source.1.1.1.1 source.1.2.1.1 =
      LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList)
    (target : FiniteBistochasticTargetAssignment
      (LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList)) :
    SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source :=
  transportFiniteBistochasticTargetAssignment
    ((congrArg (fun currentExtent =>
      slabPhysicalPairRecouplingPackages currentExtent
        source.1.1.1.1 source.1.2.1.1) hextent).trans hpackages)
    target

theorem observablePairedTargetOfWrittenAtExtent_mem
    (D : SlabPhysicalData) (extent : Nat) (hextent : D.extent = extent)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hpackages : slabPhysicalPairRecouplingPackages extent
        source.1.1.1.1 source.1.2.1.1 =
      LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList)
    (target : FiniteBistochasticTargetAssignment
      (LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList))
    (target_mem : target ∈ finiteBistochasticTargetAssignments
      (LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList)) :
    observablePairedTargetOfWrittenAtExtent D extent hextent
        rootFaceId targetFaceId source referenceLeft referenceRight
        linkedList hpackages target ∈
      slabObservablePairedStrandRecouplingChoices
        D rootFaceId targetFaceId source := by
  unfold observablePairedTargetOfWrittenAtExtent
    slabObservablePairedStrandRecouplingChoices
    slabPhysicalPairRecouplingKernel
  exact transportTarget_mem_local
    ((congrArg (fun currentExtent =>
      slabPhysicalPairRecouplingPackages currentExtent
        source.1.1.1.1 source.1.2.1.1) hextent).trans hpackages)
    target target_mem

theorem observablePairedTargetOfWrittenAtExtent_injective
    (D : SlabPhysicalData) (extent : Nat) (hextent : D.extent = extent)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hpackages : slabPhysicalPairRecouplingPackages extent
        source.1.1.1.1 source.1.2.1.1 =
      LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList)
    (left right : FiniteBistochasticTargetAssignment
      (LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList))
    (heq : observablePairedTargetOfWrittenAtExtent D extent hextent
        rootFaceId targetFaceId source referenceLeft referenceRight
          linkedList hpackages left =
      observablePairedTargetOfWrittenAtExtent D extent hextent
        rootFaceId targetFaceId source referenceLeft referenceRight
          linkedList hpackages right) :
    left = right := by
  exact transportTarget_injective_local
    ((congrArg (fun currentExtent =>
      slabPhysicalPairRecouplingPackages currentExtent
        source.1.1.1.1 source.1.2.1.1) hextent).trans hpackages)
    left right heq

/-- Consume a symbolic transported realization certificate and exact graph
data into success of the corresponding canonical observable-row choice. -/
theorem observablePairedTargetOfWrittenAtExtent_success
    (D : SlabPhysicalData) (extent : Nat) (hextent : D.extent = extent)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hpackages : slabPhysicalPairRecouplingPackages extent
        source.1.1.1.1 source.1.2.1.1 =
      LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList)
    (sourceTarget : TargetMembershipPackage
      (LinkedPhysicalPairPackages extent
        referenceLeft referenceRight linkedList))
    (referenceLeftAssignment referenceRightAssignment :
      SlabFusionWitnessAssignment)
    (certificate : TransportedPairedRealizationCertificate
      D.cutoff extent referenceLeft referenceRight
      source.1.1.1.1 source.1.2.1.1 linkedList hpackages
      sourceTarget
      (by simpa only [hextent] using source.anchor)
      referenceLeftAssignment referenceRightAssignment)
    (leftPhysical_eq : source.1.1.1.1 = referenceLeft)
    (rightPhysical_eq : source.1.2.1.1 = referenceRight)
    (leftAssignment_mem : referenceLeftAssignment ∈
      slabFineFusionWitnesses D referenceLeft)
    (rightAssignment_mem : referenceRightAssignment ∈
      slabFineFusionWitnesses D referenceRight)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (projectedEdges_eq :
      slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment leftAssignment_mem) ++
        slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment rightAssignment_mem) =
        referenceProjectedEdges)
    (vertices_eq :
      slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment leftAssignment_mem) ++
        slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment rightAssignment_mem) =
        referenceVertices)
    (adjacent_eq :
      slabProjectedFaceAdjacentB referenceProjectedEdges = referenceAdjacent)
    (targetPhysical : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (noMarkedChain : ChainIn referenceAdjacent referenceVertices
      rootFaceId targetFaceId → False) :
    slabObservablePairedStrandRecouplingSuccessB D rootFaceId targetFaceId
      source
      (observablePairedTargetOfWrittenAtExtent D extent hextent
        rootFaceId targetFaceId source referenceLeft referenceRight
        linkedList hpackages sourceTarget.target) = true := by
  cases hextent
  have hchoice : certificate.transported.target =
      transportFiniteBistochasticTargetAssignment
        hpackages sourceTarget.target := by
    rw [certificate.transported.target_eq, certificate.sourceTarget_eq]
  have hsuccess := slabObservablePairedNonvacuumDisconnectedTargetSuccess
    D rootFaceId targetFaceId source certificate.transported.target
    referenceLeft referenceRight referenceLeftAssignment
    referenceRightAssignment leftAssignment_mem rightAssignment_mem
    referenceProjectedEdges referenceVertices referenceAdjacent
    leftPhysical_eq rightPhysical_eq certificate.leftAssignment_eq
    certificate.rightAssignment_eq projectedEdges_eq vertices_eq
    adjacent_eq targetPhysical noMarkedChain
  unfold observablePairedTargetOfWrittenAtExtent
  rw [← hchoice]
  exact hsuccess

/-- Transport a pivot-cylinder column along equality of two symbolic written
link lists.  Keeping both lists symbolic makes the dependent equality cheap to
check once and prevents normalization of the concrete full-slab tuple. -/
def transportPivotCylinderTargetAlongLinks
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (sourceLinks targetLinks : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : sourceLinks = targetLinks)
    (target : FiniteBistochasticTargetAssignment
      (sourceLinks.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) :
    FiniteBistochasticTargetAssignment
      (targetLinks.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) :=
  transportFiniteBistochasticTargetAssignment
    (congrArg (fun links => links.map fun linked =>
      slabPhysicalPairRecouplingPackageAtLink 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linked) hlinks).symm target

theorem transportPivotCylinderTargetAlongLinks_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (sourceLinks targetLinks : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : sourceLinks = targetLinks)
    (target : FiniteBistochasticTargetAssignment
      (sourceLinks.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (htarget : target ∈
      reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state sourceLinks) :
    transportPivotCylinderTargetAlongLinks
        D hextent state sourceLinks targetLinks hlinks target ∈
      reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state targetLinks := by
  cases hlinks
  exact htarget

/-- One-target version of the symbolic transported paired-realization
compiler.  Unlike the family compiler, the caller may supply an arbitrary
cylinder column rather than a canonical target family. -/
def transportSingleLinkedPairedRealizationCertificate
    {K extent : Nat}
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent})
    (hlinks : linkedList = (boundaryCompleteSlabLinks extent).attach)
    (hpackages₂ : slabPhysicalPairRecouplingPackages extent
        leftPhysical₂ rightPhysical₂ =
      LinkedPhysicalPairPackages extent
        leftPhysical₁ rightPhysical₁ linkedList)
    (sourceTarget : TargetMembershipPackage
      (LinkedPhysicalPairPackages extent
        leftPhysical₁ rightPhysical₁ linkedList))
    (firstLeftAssignment firstRightAssignment :
      SlabFusionWitnessAssignment)
    (firstLeft_mem : firstLeftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstRight_mem : firstRightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstLeftBounded : SlabFaceLabellingBounded K extent leftPhysical₁)
    (firstRightBounded : SlabFaceLabellingBounded K extent rightPhysical₁)
    (secondAnchor : SlabPhysicalPairCanonicalAnchor K extent
      leftPhysical₂ rightPhysical₂)
    (expectedLeft expectedRight : SlabFusionWitnessAssignment)
    (hcanonical :
      let canonical := slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem firstLeftBounded firstRightBounded
        linkedList sourceTarget.target
      expectedLeft = canonical.leftAssignment ∧
        expectedRight = canonical.rightAssignment) :
    TransportedPairedRealizationCertificate K extent
      leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂
      linkedList hpackages₂ sourceTarget secondAnchor
      expectedLeft expectedRight := by
  have hpackages₁ : slabPhysicalPairRecouplingPackages extent
      leftPhysical₁ rightPhysical₁ =
    LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList := by
    cases hlinks
    rfl
  let transported := transportedTargetPackage hpackages₂ sourceTarget
  have htarget := transportedTarget_eq_physicalTransport
    hleft hright
    (LinkedPhysicalPairPackages extent
      leftPhysical₁ rightPhysical₁ linkedList)
    hpackages₁ hpackages₂ sourceTarget
  have hanchor := canonicalAnchor_realize_physicalTransport_assignments_eq
    hleft hright firstLeftAssignment firstRightAssignment
    firstLeft_mem firstRight_mem firstLeftBounded firstRightBounded
    secondAnchor
    (transportFiniteBistochasticTargetAssignment
      hpackages₁ sourceTarget.target)
  have hlinked :
      let first := slabPhysicalPairCanonicalTargetAssignmentsResult
        K extent leftPhysical₁ rightPhysical₁
        firstLeftAssignment firstRightAssignment
        firstLeft_mem firstRight_mem firstLeftBounded firstRightBounded
        (transportFiniteBistochasticTargetAssignment
          hpackages₁ sourceTarget.target)
      first.leftAssignment = expectedLeft ∧
        first.rightAssignment = expectedRight := by
    cases hlinks
    exact ⟨hcanonical.1.symm, hcanonical.2.symm⟩
  refine
    { transported := transported
      sourceTarget_eq := transportedTargetPackage_sourceTarget
        hpackages₂ sourceTarget
      leftAssignment_eq := ?_
      rightAssignment_eq := ?_ }
  · rw [htarget]
    exact hanchor.1.trans hlinked.1
  · rw [htarget]
    exact hanchor.2.trans hlinked.2

def literalCylinderLeftAssignment
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
    D hcutoff hextent state linkedList target

def literalCylinderRightAssignment
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
    D hcutoff hextent state linkedList target

theorem literalCylinderLeftAssignment_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) :
    literalCylinderLeftAssignment D hcutoff hextent state linkedList target ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  have hmem :=
    reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_mem
      D hcutoff hextent state linkedList target
  have hlinksVal : linkedList.map Subtype.val =
      boundaryCompleteSlabLinks 5 :=
    (congrArg (List.map Subtype.val) hlinks).trans
      (List.attach_map_subtype_val (boundaryCompleteSlabLinks 5))
  rw [hlinksVal] at hmem
  simpa only [literalCylinderLeftAssignment,
    slabFineFusionWitnesses, hextent] using hmem

theorem literalCylinderRightAssignment_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) :
    literalCylinderRightAssignment D hcutoff hextent state linkedList target ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftRightPhysical D hextent state) := by
  have hmem :=
    reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff_mem
      D hcutoff hextent state linkedList target
  have hlinksVal : linkedList.map Subtype.val =
      boundaryCompleteSlabLinks 5 :=
    (congrArg (List.map Subtype.val) hlinks).trans
      (List.attach_map_subtype_val (boundaryCompleteSlabLinks 5))
  rw [hlinksVal] at hmem
  simpa only [literalCylinderRightAssignment,
    slabFineFusionWitnesses, hextent] using hmem

theorem literalCylinderProjectedEdges_eq_standard
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) :
    slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (literalCylinderLeftAssignment
              D hcutoff hextent state linkedList target)
            (literalCylinderLeftAssignment_mem
              D hcutoff hextent state linkedList hlinks target)) ++
        slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D
            (reflectedBentGuardGraftRightPhysical D hextent state)
            (literalCylinderRightAssignment
              D hcutoff hextent state linkedList target)
            (literalCylinderRightAssignment_mem
              D hcutoff hextent state linkedList hlinks target)) =
      reflectedBentGuardGraftStandardProjectedFaceEdgesFromTargetAtCutoff
        D hcutoff hextent state linkedList target := by
  have hlinksVal : linkedList.map Subtype.val =
      boundaryCompleteSlabLinks 5 :=
    (congrArg (List.map Subtype.val) hlinks).trans
      (List.attach_map_subtype_val (boundaryCompleteSlabLinks 5))
  unfold reflectedBentGuardGraftStandardProjectedFaceEdgesFromTargetAtCutoff
    reflectedBentGuardGraftStandardLeftProjectedFaceEdgesFromTargetAtCutoff
    reflectedBentGuardGraftStandardRightProjectedFaceEdgesFromTargetAtCutoff
    slabFineFusionWitnessFaceStrandEdges
  simp only [literalCylinderLeftAssignment,
    literalCylinderRightAssignment, hextent, hlinksVal]

theorem literalCylinderFaceVertices_eq_standard
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) :
    slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (literalCylinderLeftAssignment
              D hcutoff hextent state linkedList target)
            (literalCylinderLeftAssignment_mem
              D hcutoff hextent state linkedList hlinks target)) ++
        slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D
            (reflectedBentGuardGraftRightPhysical D hextent state)
            (literalCylinderRightAssignment
              D hcutoff hextent state linkedList target)
            (literalCylinderRightAssignment_mem
              D hcutoff hextent state linkedList hlinks target)) =
      reflectedBentGuardGraftStandardFaceVerticesFromTargetAtCutoff
        D hcutoff hextent state linkedList target := by
  rw [slabFaceStrandFaceVertices_eq_projectedEndpoints,
    slabFaceStrandFaceVertices_eq_projectedEndpoints,
    ← List.flatMap_append,
    literalCylinderProjectedEdges_eq_standard
      D hcutoff hextent state linkedList hlinks target]
  rfl

theorem literalCylinderObservablePackages_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach) :
    slabPhysicalPairRecouplingPackages 5
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.2.1.1 =
      linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked := by
  have hfull :=
    reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
      D hcutoff hextent state
  have hmapped := congrArg (fun links => links.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state) linked) hlinks
  have hfull' : slabPhysicalPairRecouplingPackages 5
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.2.1.1 =
      (boundaryCompleteSlabLinks 5).attach.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked := by
    simpa only [hextent] using hfull
  exact hfull'.trans hmapped.symm

opaque literalCylinderPairedRealizationCertificate
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (target_mem : target ∈ finiteBistochasticTargetAssignments
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) :
    let source := reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state
    let sourceTarget : TargetMembershipPackage
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked) :=
      { target := target, target_mem := target_mem }
    let anchor : SlabPhysicalPairCanonicalAnchor D.cutoff 5
        source.1.1.1.1 source.1.2.1.1 := by
      simpa only [source, hextent] using source.anchor
    TransportedPairedRealizationCertificate D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      source.1.1.1.1 source.1.2.1.1 linkedList
      (literalCylinderObservablePackages_eq
        D hcutoff hextent state linkedList hlinks)
      sourceTarget anchor
      (literalCylinderLeftAssignment
        D hcutoff hextent state linkedList target)
      (literalCylinderRightAssignment
        D hcutoff hextent state linkedList target) := by
  let source := reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
    D hcutoff hextent state
  let sourceTarget : TargetMembershipPackage
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) :=
    { target := target, target_mem := target_mem }
  let anchor : SlabPhysicalPairCanonicalAnchor D.cutoff 5
      source.1.1.1.1 source.1.2.1.1 := by
    simpa only [source, hextent] using source.anchor
  apply transportSingleLinkedPairedRealizationCertificate
    ((reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical
      D hcutoff hextent state).symm)
    ((reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical
      D hcutoff hextent state).symm)
    linkedList hlinks
    (literalCylinderObservablePackages_eq
      D hcutoff hextent state linkedList hlinks)
    sourceTarget
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
      D hextent state)
    anchor
    (literalCylinderLeftAssignment
      D hcutoff hextent state linkedList target)
    (literalCylinderRightAssignment
      D hcutoff hextent state linkedList target)
  exact reflectedBentGuardGraftRealizedAssignmentsFromTargetAtCutoff_eq_canonical
    D hcutoff hextent state linkedList target


/-- Symbolic input package for a full-row target with a standard-graph
disconnection witness.  Bundling the heterogeneous target keeps it out of the
success theorem's public binder spine. -/
inductive ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Type where
  | mk
      (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (hlinks : linkedList = (boundaryCompleteSlabLinks 5).attach)
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked))
      (target_mem : target ∈ finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked))
      (hnoChain : ChainIn
        (reflectedBentGuardGraftStandardFaceAdjacentBFromTargetAtCutoff
          D hcutoff hextent state linkedList target)
        (reflectedBentGuardGraftStandardFaceVerticesFromTargetAtCutoff
          D hcutoff hextent state linkedList target)
        reflectedBentRootFaceId reflectedBentTargetFaceId → False)

def ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff.observableChoice
    {D : SlabPhysicalData} {hcutoff : 1 ≤ D.cutoff}
    {hextent : D.extent = 5}
    {state : SlabAcceptedTwoReplicaState D}
    (input : ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state) :
    SlabObservablePairedStrandRecouplingChoice D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state) :=
  match input with
  | .mk linkedList hlinks target _ _ =>
      observablePairedTargetOfWrittenAtExtent D 5 hextent
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linkedList
        (literalCylinderObservablePackages_eq
          D hcutoff hextent state linkedList hlinks)
        target

theorem ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff.observableChoice_mem
    {D : SlabPhysicalData} {hcutoff : 1 ≤ D.cutoff}
    {hextent : D.extent = 5}
    {state : SlabAcceptedTwoReplicaState D}
    (input : ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state) :
    input.observableChoice ∈
      slabObservablePairedStrandRecouplingChoices D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) := by
  rcases input with ⟨linkedList, hlinks, target, target_mem, hnoChain⟩
  exact observablePairedTargetOfWrittenAtExtent_mem D 5 hextent
    reflectedBentRootFaceId reflectedBentTargetFaceId
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
    linkedList
    (literalCylinderObservablePackages_eq
      D hcutoff hextent state linkedList hlinks)
    target target_mem

/-- Every bundled literal separated-cylinder target produces a successful
choice in the canonical observable row. -/
opaque reflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff_success
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (input : ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state) :
    slabObservablePairedStrandRecouplingSuccessB D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state) input.observableChoice = true := by
  rcases input with ⟨linkedList, hlinks, target, target_mem, hnoChain⟩
  let source := reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
    D hcutoff hextent state
  let referenceLeft := reflectedBentGuardGraftLeftPhysical D hextent state
  let referenceRight := reflectedBentGuardGraftRightPhysical D hextent state
  let referenceLeftAssignment :=
    literalCylinderLeftAssignment
      D hcutoff hextent state linkedList target
  let referenceRightAssignment :=
    literalCylinderRightAssignment
      D hcutoff hextent state linkedList target
  have referenceLeft_mem : referenceLeftAssignment ∈
      slabFineFusionWitnesses D referenceLeft := by
    simpa only [referenceLeftAssignment, referenceLeft] using
      literalCylinderLeftAssignment_mem
        D hcutoff hextent state linkedList hlinks target
  have referenceRight_mem : referenceRightAssignment ∈
      slabFineFusionWitnesses D referenceRight := by
    simpa only [referenceRightAssignment, referenceRight] using
      literalCylinderRightAssignment_mem
        D hcutoff hextent state linkedList hlinks target
  let referenceProjectedEdges :=
    reflectedBentGuardGraftStandardProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target
  let referenceVertices :=
    reflectedBentGuardGraftStandardFaceVerticesFromTargetAtCutoff
      D hcutoff hextent state linkedList target
  let referenceAdjacent :=
    reflectedBentGuardGraftStandardFaceAdjacentBFromTargetAtCutoff
      D hcutoff hextent state linkedList target
  have hprojected :
      slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment referenceLeft_mem) ++
        slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment referenceRight_mem) =
      referenceProjectedEdges := by
    simpa only [referenceLeftAssignment, referenceRightAssignment,
      referenceLeft, referenceRight, referenceProjectedEdges] using
      literalCylinderProjectedEdges_eq_standard
        D hcutoff hextent state linkedList hlinks target
  have hvertices :
      slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment referenceLeft_mem) ++
        slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment referenceRight_mem) =
      referenceVertices := by
    simpa only [referenceLeftAssignment, referenceRightAssignment,
      referenceLeft, referenceRight, referenceVertices] using
      literalCylinderFaceVertices_eq_standard
        D hcutoff hextent state linkedList hlinks target
  let hpackages := literalCylinderObservablePackages_eq
    D hcutoff hextent state linkedList hlinks
  let sourceTarget : TargetMembershipPackage
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          referenceLeft referenceRight linked) :=
    { target := target, target_mem := target_mem }
  let anchor : SlabPhysicalPairCanonicalAnchor D.cutoff 5
      source.1.1.1.1 source.1.2.1.1 := by
    simpa only [source, hextent] using source.anchor
  let certificate : TransportedPairedRealizationCertificate D.cutoff 5
      referenceLeft referenceRight source.1.1.1.1 source.1.2.1.1
      linkedList hpackages sourceTarget anchor
      referenceLeftAssignment referenceRightAssignment := by
    simpa only [hpackages, sourceTarget, anchor, source, referenceLeft,
      referenceRight, referenceLeftAssignment, referenceRightAssignment] using
      literalCylinderPairedRealizationCertificate
        D hcutoff hextent state linkedList hlinks target target_mem
  simpa only [
      ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff.observableChoice,
      source, referenceLeft, referenceRight, hpackages, sourceTarget] using
    (observablePairedTargetOfWrittenAtExtent_success
      D 5 hextent reflectedBentRootFaceId reflectedBentTargetFaceId source
      referenceLeft referenceRight linkedList hpackages sourceTarget
      referenceLeftAssignment referenceRightAssignment certificate
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical
        D hcutoff hextent state)
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical
        D hcutoff hextent state)
      referenceLeft_mem referenceRight_mem referenceProjectedEdges
      referenceVertices referenceAdjacent hprojected hvertices rfl
      reflectedBentTargetFaceId_physical hnoChain)

#print axioms reflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff_success

/-- Every pivot-cylinder member has a successful canonical observable-row
choice.  Membership supplies both the full target-product witness and the
pinned pivot used by the symbolic graph compiler. -/
opaque reflectedBentGuardGraftLiteralObservableSuccessfulChoiceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5}),
      linkedList = (boundaryCompleteSlabLinks 5).attach →
      ∀ (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
        target ∈ reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
          D hcutoff hextent state linkedList →
          ObservableSuccessfulWeightedChoiceExists D := by
  intro linkedList hlinks target htarget
  let input : ReflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff
      D hcutoff hextent state :=
    .mk linkedList hlinks target
      (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_mem_full
        D hcutoff hextent state linkedList target htarget)
      (reflectedBentGuardGraftStandardTarget_noMarkedFaceChainAtCutoff
        D hcutoff hextent state linkedList target
        (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_pinned
          D hcutoff hextent state linkedList target htarget))
  exact .mk
    { rootFaceId := reflectedBentRootFaceId
      targetFaceId := reflectedBentTargetFaceId
      source := reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state
      observableChoice := input.observableChoice
      observableChoice_mem := input.observableChoice_mem
      success :=
        reflectedBentGuardGraftLiteralObservablePinnedTargetAtCutoff_success
          D hcutoff hextent state input }

#print axioms reflectedBentGuardGraftLiteralObservableSuccessfulChoiceAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccess
