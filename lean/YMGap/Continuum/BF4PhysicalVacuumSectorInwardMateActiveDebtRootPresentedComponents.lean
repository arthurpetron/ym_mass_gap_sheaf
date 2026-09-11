/-
# The two active debt-root strands generate a closed global selection

After inserting the root-first presentation into a complete presented source
background, both distinguished strand edges live in one finite global graph.
This file roots that graph at each edge source and takes the Boolean union of
the two constructive components.  The union contains both required root face
copies and is closed across every displayed edge, hence across every ordered
local terminal partner.

The two components are not asserted to be distinct or equal.  Retaining their
union is the exact statement needed to remove one strand at each side of the
stretched root vertex without inventing a connectivity claim.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The inserted graph and its two constructive seeds -/

abbrev RootInsertedPresentedFaceStrandEdges
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :=
  presentedSlabFusionWitnessAssignmentFaceStrandEdges K 1 physical links
    (rootInsertedPresentedSlabFusionWitnessAssignment
      carrier links background hroot)

def rootLeftFirstChannelSeed
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    SlabFaceStrandSeed
      (RootInsertedPresentedFaceStrandEdges
        carrier links background hroot) :=
  SlabFaceStrandSeed.ofEdge
    (rootLeftFirstChannelEdge_mem_inserted_global
      carrier links background hroot)

def rootRightFirstChannelSeed
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    SlabFaceStrandSeed
      (RootInsertedPresentedFaceStrandEdges
        carrier links background hroot) :=
  SlabFaceStrandSeed.ofEdge
    (rootRightFirstChannelEdge_mem_inserted_global
      carrier links background hroot)

@[simp] theorem rootLeftFirstChannelSeed_root
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    (rootLeftFirstChannelSeed carrier links background hroot).root =
      leftRootCopy carrier :=
  rootLeftFirstChannelEdge_source carrier

@[simp] theorem rootRightFirstChannelSeed_root
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    (rootRightFirstChannelSeed carrier links background hroot).root =
      rightRootCopy carrier :=
  rootRightFirstChannelEdge_source carrier

/-! ## 2. Union the two rooted components without assuming connectivity -/

def rootFirstChannelComponentUnionSelected
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links)
    (copy : SlabFaceStrandCopy physical) : Bool :=
  (rootLeftFirstChannelSeed carrier links background hroot).selected copy ||
    (rootRightFirstChannelSeed carrier links background hroot).selected copy

theorem rootFirstChannelComponentUnionSelected_eq_of_edge_mem
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links)
    {edge : SlabFaceStrandEdge physical}
    (hedge : edge ∈ RootInsertedPresentedFaceStrandEdges
      carrier links background hroot) :
    rootFirstChannelComponentUnionSelected
        carrier links background hroot edge.target =
      rootFirstChannelComponentUnionSelected
        carrier links background hroot edge.source := by
  unfold rootFirstChannelComponentUnionSelected
  rw [SlabFaceStrandSeed.selected_eq_of_edge_mem _ hedge,
    SlabFaceStrandSeed.selected_eq_of_edge_mem _ hedge]

/-- At every displayed link, the two-root union is closed under the exact
physical terminal partner of that link's retained presentation. -/
def rootFirstChannelComponentUnionAtLinkSelection
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links)
    (linked : {link // link ∈ links}) :
    OrderedSlabLinkPartnerClosedFaceSelection K
      (rootInsertedPresentedSlabFusionWitnessAssignment
        carrier links background hroot linked) where
  selected := rootFirstChannelComponentUnionSelected
    carrier links background hroot
  partner_closed := by
    intro terminal
    exact rootFirstChannelComponentUnionSelected_eq_of_edge_mem
      carrier links background hroot
      (presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
        K 1 physical links
        (rootInsertedPresentedSlabFusionWitnessAssignment
          carrier links background hroot)
        linked terminal)

@[simp] theorem rootFirstChannelComponentUnionSelected_leftRoot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    rootFirstChannelComponentUnionSelected carrier links background hroot
      (leftRootCopy carrier) = true := by
  unfold rootFirstChannelComponentUnionSelected
  rw [← rootLeftFirstChannelSeed_root carrier links background hroot,
    SlabFaceStrandSeed.selected_root]
  rfl

@[simp] theorem rootFirstChannelComponentUnionSelected_rightRoot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    rootFirstChannelComponentUnionSelected carrier links background hroot
      (rightRootCopy carrier) = true := by
  unfold rootFirstChannelComponentUnionSelected
  rw [← rootRightFirstChannelSeed_root carrier links background hroot,
    SlabFaceStrandSeed.selected_root]
  cases (rootLeftFirstChannelSeed
    carrier links background hroot).selected
      (rootRightFirstChannelSeed carrier links background hroot).root <;> rfl

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootLeftFirstChannelSeed
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootRightFirstChannelSeed
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionSelected_eq_of_edge_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionAtLinkSelection
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionSelected_leftRoot
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionSelected_rightRoot
