/-
# The guarded target as an opaque successful observable channel

The complete cutoff-one, extent-five recoupling target is a large dependent
tuple.  Its realization and its graph classification have already been proved
separately.  This module contracts those facts through a small package whose
public fields are exactly the two realized assignments and the classified
paired graph.  The concrete target tuple remains behind the package boundary.

The concrete guarded package below still records the geometric-success half.
This module now also proves the generic final contraction: once
coordinatewise SU(2) positivity is attached to that same opaque choice, the
package constructs the literal local positive channel.  The remaining
concrete specialization is deliberately not exposed as a giant dependent
target statement.

Constructive contract: dependent finite products, exact graph equalities, and
the existing paired-realization certificate only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel
import YMGap.Continuum.CompactDualSlabTransportedTargetPositiveEntry
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSuccess
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPairedRealization

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChannel

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabTransportedTargetPositiveEntry
open YMGap.Continuum.CompactDualSlabTransportedPairedRealizationCertificate
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSuccess
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPairedRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

/-! ## 1. A small paired-realization boundary -/

/-- Coordinatewise positivity of one raw observable choice, kept behind a
small named proposition so target packages need not expose their complete
dependent product in structure declarations. -/
inductive ObservableChoicePairedLocallyPositive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) : Prop where
  | mk
      (coordinatewise : FiniteBistochasticCoordinatewisePositive
        (slabPhysicalPairRecouplingProductionSource
          D.cutoff D.extent source.1.1.1.1 source.1.2.1.1
          source.1.1.1.2 source.1.2.1.2
          source.1.1.assignment_mem
          (slabExpandedFineSourceEntryAssignment_mem source.1.2))
        choice)

/-- Hide the transported dependent target while retaining the exact choice,
membership, and the two assignment equations consumed by graph success. -/
structure ObservableChoicePairedAssignmentPackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (expectedLeft expectedRight : SlabFusionWitnessAssignment) : Type where
  choice : SlabObservablePairedStrandRecouplingChoice
    D rootFaceId targetFaceId source
  choice_mem : choice ∈ slabObservablePairedStrandRecouplingChoices
    D rootFaceId targetFaceId source
  leftAssignment_eq :
    (source.anchor.realize choice).leftAssignment = expectedLeft
  rightAssignment_eq :
    (source.anchor.realize choice).rightAssignment = expectedRight

/-- Forget the transport implementation only after it has supplied both
realization equations. -/
def observableChoicePairedAssignmentPackageOfTransported
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
    (expectedLeft expectedRight : SlabFusionWitnessAssignment)
    (certificate : TransportedPairedRealizationCertificate
      D.cutoff D.extent
      firstLeftPhysical firstRightPhysical
      source.1.1.1.1 source.1.2.1.1
      linkedList hpackages sourceTarget source.anchor
      expectedLeft expectedRight) :
    ObservableChoicePairedAssignmentPackage
      D rootFaceId targetFaceId source expectedLeft expectedRight where
  choice := certificate.transported.target
  choice_mem := certificate.transported.target_mem
  leftAssignment_eq := certificate.leftAssignment_eq
  rightAssignment_eq := certificate.rightAssignment_eq

/-! ## 2. Contract exact graph data to success -/

/-- A nonvacuum paired target whose realized graph has a named separating
coloring.  This structure mentions no concrete dependent target tuple. -/
structure ObservablePairedDisconnectedTargetPackage
    (D : SlabPhysicalData) : Type where
  rootFaceId : Nat
  targetFaceId : Nat
  source : SlabObservablePairedStrandRecouplingSource
    D rootFaceId targetFaceId
  referenceLeft : SlabLabelling
  referenceRight : SlabLabelling
  referenceLeftAssignment : SlabFusionWitnessAssignment
  referenceRightAssignment : SlabFusionWitnessAssignment
  referenceProjectedEdges : List SlabProjectedFaceEdge
  referenceVertices : List Nat
  referenceAdjacent : Nat → Nat → Bool
  realized : ObservableChoicePairedAssignmentPackage
    D rootFaceId targetFaceId source
      referenceLeftAssignment referenceRightAssignment
  leftPhysical_eq : source.1.1.1.1 = referenceLeft
  rightPhysical_eq : source.1.2.1.1 = referenceRight
  leftAssignment_mem : referenceLeftAssignment ∈
    slabFineFusionWitnesses D referenceLeft
  rightAssignment_mem : referenceRightAssignment ∈
    slabFineFusionWitnesses D referenceRight
  projectedEdges_eq :
    slabProjectedFaceEdges
        (slabFineFusionWitnessFaceStrandEdges D referenceLeft
          referenceLeftAssignment leftAssignment_mem) ++
      slabProjectedFaceEdges
        (slabFineFusionWitnessFaceStrandEdges D referenceRight
          referenceRightAssignment rightAssignment_mem) =
      referenceProjectedEdges
  vertices_eq :
    slabFaceStrandFaceVertices
        (slabFineFusionWitnessFaceStrandEdges D referenceLeft
          referenceLeftAssignment leftAssignment_mem) ++
      slabFaceStrandFaceVertices
        (slabFineFusionWitnessFaceStrandEdges D referenceRight
          referenceRightAssignment rightAssignment_mem) =
      referenceVertices
  adjacent_eq :
    slabProjectedFaceAdjacentB referenceProjectedEdges = referenceAdjacent
  targetPhysical : targetFaceId ∈ slabPhysicalFaceEdges D.extent
  noMarkedChain :
    ChainIn referenceAdjacent referenceVertices rootFaceId targetFaceId → False

/-- The package fields are precisely the hypotheses of the already-proved
two-nonvacuum success theorem. -/
theorem ObservablePairedDisconnectedTargetPackage.success
    {D : SlabPhysicalData}
    (package : ObservablePairedDisconnectedTargetPackage D) :
    slabObservablePairedStrandRecouplingSuccessB
      D package.rootFaceId package.targetFaceId package.source
      package.realized.choice = true := by
  exact slabObservablePairedNonvacuumDisconnectedTargetSuccess
    D package.rootFaceId package.targetFaceId
    package.source package.realized.choice
    package.referenceLeft package.referenceRight
    package.referenceLeftAssignment package.referenceRightAssignment
    package.leftAssignment_mem package.rightAssignment_mem
    package.referenceProjectedEdges package.referenceVertices
    package.referenceAdjacent
    package.leftPhysical_eq package.rightPhysical_eq
    package.realized.leftAssignment_eq package.realized.rightAssignment_eq
    package.projectedEdges_eq package.vertices_eq package.adjacent_eq
    package.targetPhysical package.noMarkedChain

/-- One opaque graph-success package together with connectedness of its source
and coordinatewise positivity of the very same chosen target.  The inductive
wrapper keeps those large dependent fields out of public result-type
normalization. -/
inductive ObservablePairedDisconnectedPositiveTargetPackage
    (D : SlabPhysicalData) : Type where
  | mk
      (package : ObservablePairedDisconnectedTargetPackage D)
      (source_connected :
        slabObservableTwoReplicaPairPairedSupportConnectedB
          D package.rootFaceId package.targetFaceId package.source.1 = true)
      (locally_positive : ObservableChoicePairedLocallyPositive
        D package.rootFaceId package.targetFaceId package.source
          package.realized.choice)

def ObservablePairedDisconnectedPositiveTargetPackage.rootFaceId
    {D : SlabPhysicalData}
    (positivePackage : ObservablePairedDisconnectedPositiveTargetPackage D) : Nat :=
  match positivePackage with
  | .mk package _ _ => package.rootFaceId

def ObservablePairedDisconnectedPositiveTargetPackage.targetFaceId
    {D : SlabPhysicalData}
    (positivePackage : ObservablePairedDisconnectedPositiveTargetPackage D) : Nat :=
  match positivePackage with
  | .mk package _ _ => package.targetFaceId

/-- Geometric disconnection and local SU(2) positivity for the same opaque
choice construct the literal positive connected channel. -/
def ObservablePairedDisconnectedPositiveTargetPackage.toLocalPositiveChannel
    {D : SlabPhysicalData}
    (positivePackage : ObservablePairedDisconnectedPositiveTargetPackage D) :
    SlabObservablePairedConnectedLocalPositiveChannel D
      positivePackage.rootFaceId positivePackage.targetFaceId := by
  cases positivePackage with
  | mk package source_connected locally_positive =>
      let connected : SlabObservablePairedConnectedStrandSource
          D package.rootFaceId package.targetFaceId :=
        ⟨package.source.1,
          List.mem_filter.mpr ⟨package.source.2, source_connected⟩⟩
      exact .mk connected (.mk package.realized.choice
        package.realized.choice_mem
        (by
          simpa only [connected,
            SlabObservablePairedConnectedStrandSource.toRecouplingSource] using
            package.success)
        (by
          cases locally_positive with
          | mk coordinatewise =>
              unfold SlabObservablePairedConnectedChoiceLocallyPositive
              simpa only [connected,
                slabObservablePairedConnectedProductionSource,
                SlabObservablePairedConnectedStrandSource.toRecouplingSource] using
                coordinatewise))

/-- Assemble the opaque graph package while every dependent carrier remains
symbolic.  Concrete specializations therefore need not normalize their full
target tuples merely to construct record projections. -/
def observablePairedDisconnectedTargetPackageOfTransported
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks D.extent})
    (hpackages : slabPhysicalPairRecouplingPackages D.extent
        source.1.1.1.1 source.1.2.1.1 =
      LinkedPhysicalPairPackages D.extent
        referenceLeft referenceRight linkedList)
    (sourceTarget : TargetMembershipPackage
      (LinkedPhysicalPairPackages D.extent
        referenceLeft referenceRight linkedList))
    (referenceLeftAssignment referenceRightAssignment :
      SlabFusionWitnessAssignment)
    (certificate : TransportedPairedRealizationCertificate
      D.cutoff D.extent
      referenceLeft referenceRight source.1.1.1.1 source.1.2.1.1
      linkedList hpackages sourceTarget source.anchor
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
    (targetPhysical : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (noMarkedChain :
      ChainIn referenceAdjacent referenceVertices rootFaceId targetFaceId →
        False) :
    ObservablePairedDisconnectedTargetPackage D where
  rootFaceId := rootFaceId
  targetFaceId := targetFaceId
  source := source
  referenceLeft := referenceLeft
  referenceRight := referenceRight
  referenceLeftAssignment := referenceLeftAssignment
  referenceRightAssignment := referenceRightAssignment
  referenceProjectedEdges := referenceProjectedEdges
  referenceVertices := referenceVertices
  referenceAdjacent := referenceAdjacent
  realized := observableChoicePairedAssignmentPackageOfTransported
    D rootFaceId targetFaceId source referenceLeft referenceRight
    linkedList hpackages sourceTarget referenceLeftAssignment
    referenceRightAssignment certificate
  leftPhysical_eq := leftPhysical_eq
  rightPhysical_eq := rightPhysical_eq
  leftAssignment_mem := leftAssignment_mem
  rightAssignment_mem := rightAssignment_mem
  projectedEdges_eq := projectedEdges_eq
  vertices_eq := vertices_eq
  adjacent_eq := adjacent_eq
  targetPhysical := targetPhysical
  noMarkedChain := noMarkedChain

/-! ## 3. The concrete guarded package -/

/-- The guarded target, realization, and separating graph packaged without
exposing the complete dependent target in the declaration result. -/
opaque reflectedBentGuardGraftObservableDisconnectedTargetPackage
    (state : SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData) :
    ObservablePairedDisconnectedTargetPackage
      reflectedBentGuardAnchorData := by
  let D := reflectedBentGuardAnchorData
  let hcutoff : D.cutoff = 1 := by decide
  let hextent : D.extent = 5 := by decide
  let source := reflectedBentGuardGraftRawObservableRecouplingSource
    D hcutoff hextent state
  let certificate := reflectedBentGuardGraftRawPairedRealizationCertificate
    D hcutoff hextent state
  let linked := (boundaryCompleteSlabLinks 5).attach
  let hpackages : slabPhysicalPairRecouplingPackages D.extent
      source.1.1.1.1 source.1.2.1.1 =
      ReflectedBentGuardGraftLinkedPackagesFrom D hextent state linked := by
    simpa only [source, hcutoff, hextent, linked] using
      reflectedBentGuardGraftRawObservableRecouplingPackages_eq
        D hcutoff hextent state
  let sourceTarget := reflectedBentGuardGraftTargetMembershipPackageFrom
    D hcutoff hextent state linked
  let transportedCertificate : TransportedPairedRealizationCertificate
      D.cutoff D.extent
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      source.1.1.1.1 source.1.2.1.1 linked hpackages sourceTarget
      source.anchor
      (reflectedBentGuardGraftRealizedLeftAssignment D hcutoff hextent state)
      (reflectedBentGuardGraftRealizedRightAssignment
        D hcutoff hextent state) := by
    simpa only [hcutoff, hextent, linked, sourceTarget] using certificate
  apply observablePairedDisconnectedTargetPackageOfTransported
    D reflectedBentRootFaceId reflectedBentTargetFaceId source
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
    linked hpackages sourceTarget
    (reflectedBentGuardGraftRealizedLeftAssignment D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignment D hcutoff hextent state)
    transportedCertificate
    (reflectedBentGuardGraftLeftPositiveEntry_physical
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightExpandedEntry_physical
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedLeftAssignment_mem
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignment_mem
      D hcutoff hextent state)
    (reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
      D hcutoff hextent state)
    (reflectedBentGuardGraftPositiveTargetFaceVertices
      D hcutoff hextent state)
    (reflectedBentGuardGraftPositiveTargetFaceAdjacentB
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedPairedProjectedFaceEdges_eq_target
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedPairedFaceVertices_eq_target
      D hcutoff hextent state)
    rfl
    (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
    (reflectedBentGuardGraftPositiveTarget_noMarkedFaceChain
      D hcutoff hextent state)

#print axioms observableChoicePairedAssignmentPackageOfTransported
#print axioms ObservablePairedDisconnectedTargetPackage.success
#print axioms ObservablePairedDisconnectedPositiveTargetPackage.toLocalPositiveChannel
#print axioms reflectedBentGuardGraftObservableDisconnectedTargetPackage

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChannel
