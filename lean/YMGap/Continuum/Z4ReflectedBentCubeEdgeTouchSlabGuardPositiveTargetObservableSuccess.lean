/-
# Exact success compiler for a two-nonvacuum observable target

If a selected recoupling column realizes two reference assignments whose
combined projected graph and vertex carrier have no marked-face chain, then
the observable success Boolean is true.  This is the non-vacuum analogue of
the older vacuum-right compiler and accepts the guarded target graph proved
in the imported bridge once its final dependent realization equalities are
supplied.

Constructive contract: anchor independence, exact graph transport, and finite
rooted-component connectivity only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableSuccess

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSuccess

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableSuccess
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

/-! ## 1. A two-nonvacuum exact-graph success principle -/

theorem slabObservablePairedNonvacuumDisconnectedTargetSuccess
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
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
    slabObservablePairedStrandRecouplingSuccessB
      D rootFaceId targetFaceId source choice = true := by
  let pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source choice
  have hleftProjected :
      slabProjectedFaceEdges
          (slabObservableTwoReplicaPairLeftStrandEdges D pair) =
        slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment referenceLeft_mem) := by
    exact slabProjectedFineFusionWitnessFaceStrandEdges_eq_of_eq
      D hleftPhysical pair.1.1.2 referenceLeftAssignment
      pair.1.assignment_mem referenceLeft_mem hleftAssignment
  have hrightProjected :
      slabProjectedFaceEdges
          (slabObservableTwoReplicaPairRightStrandEdges D pair) =
        slabProjectedFaceEdges
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment referenceRight_mem) := by
    exact slabProjectedFineFusionWitnessFaceStrandEdges_eq_of_eq
      D hrightPhysical pair.2.1.2 referenceRightAssignment
      (slabExpandedFineSourceEntryAssignment_mem pair.2)
      referenceRight_mem hrightAssignment
  have hleftVertices :
      slabFaceStrandFaceVertices
          (slabObservableTwoReplicaPairLeftStrandEdges D pair) =
        slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceLeft
            referenceLeftAssignment referenceLeft_mem) := by
    exact slabFineFusionWitnessFaceVertices_eq_of_eq
      D hleftPhysical pair.1.1.2 referenceLeftAssignment
      pair.1.assignment_mem referenceLeft_mem hleftAssignment
  have hrightVertices :
      slabFaceStrandFaceVertices
          (slabObservableTwoReplicaPairRightStrandEdges D pair) =
        slabFaceStrandFaceVertices
          (slabFineFusionWitnessFaceStrandEdges D referenceRight
            referenceRightAssignment referenceRight_mem) := by
    exact slabFineFusionWitnessFaceVertices_eq_of_eq
      D hrightPhysical pair.2.1.2 referenceRightAssignment
      (slabExpandedFineSourceEntryAssignment_mem pair.2)
      referenceRight_mem hrightAssignment
  have hpairedEdges :
      slabObservableTwoReplicaPairPairedFaceEdges D pair =
        referenceProjectedEdges := by
    unfold slabObservableTwoReplicaPairPairedFaceEdges
    rw [hleftProjected, hrightProjected]
    exact hprojected
  have hpairedVertices :
      slabObservableTwoReplicaPairPairedFaceVertices D pair =
        referenceVertices := by
    unfold slabObservableTwoReplicaPairPairedFaceVertices
    rw [hleftVertices, hrightVertices]
    exact hvertices
  have hpairedAdjacent :
      slabObservableTwoReplicaPairPairedFaceAdjacentB D pair =
        referenceAdjacent := by
    unfold slabObservableTwoReplicaPairPairedFaceAdjacentB
    rw [hpairedEdges]
    exact hadjacent
  have hpair_mem : pair ∈
      slabObservableFourCellSourcePairs D rootFaceId targetFaceId :=
    slabObservablePairedStrandRecoupledPair_mem_source
      D rootFaceId targetFaceId source choice
  have hconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = false :=
    slabObservablePairedFaceConnectedB_false_of_no_chain
      D rootFaceId targetFaceId pair htarget hpair_mem
      referenceAdjacent referenceVertices
      hpairedAdjacent hpairedVertices hnoChain
  unfold slabObservablePairedStrandRecouplingSuccessB
  rw [hconnected]
  rfl

#print axioms slabObservablePairedNonvacuumDisconnectedTargetSuccess

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSuccess
