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
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
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

/-! ## 3. Peel the union into one accepted presented assignment -/

/-- Lower the common physical field by the exact face-copy count of the
two-root component union. -/
def rootFirstChannelComponentUnionLowerPhysical
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    EdgeLabelling :=
  lowerSlabPhysicalByFaceStrandSelection
    (rootFirstChannelComponentUnionSelected carrier links background hroot)

/-- The coherent removal at one displayed presentation, packaged as an
accepted witness over the common lowered physical field. -/
def rootFirstChannelComponentUnionLoweredWitnessAt
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links)
    (linked : {link // link ∈ links}) :
    PresentedSlabLinkFusionWitness K 1
      (rootFirstChannelComponentUnionLowerPhysical
        carrier links background hroot)
      linked.1 :=
  let sourceAssignment := rootInsertedPresentedSlabFusionWitnessAssignment
    carrier links background hroot
  let sourceWitness := sourceAssignment linked
  let selection := rootFirstChannelComponentUnionAtLinkSelection
    carrier links background hroot linked
  { order := sourceWitness.order
    auxiliary := lowerEdgeLabellingBy sourceWitness.auxiliary selection.drop
    auxiliary_mem := by
      exact
        OrderedSlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem_global
          selection }

/-- Peeling the union at every link gives a complete heterogeneous assignment
accepted over one common lowered physical labelling. -/
def rootFirstChannelComponentUnionLoweredAssignment
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    PresentedSlabFusionWitnessAssignment K 1
      (rootFirstChannelComponentUnionLowerPhysical
        carrier links background hroot)
      links :=
  fun linked => rootFirstChannelComponentUnionLoweredWitnessAt
    carrier links background hroot linked

private theorem boolCountFrom_pos_of_true
    (selected : Nat → Bool) : ∀ start length offset : Nat,
    offset < length → selected (start + offset) = true →
      0 < boolCountFrom selected start length
  | _, 0, offset, hoffset, _ => by omega
  | start, length + 1, 0, _, htrue => by
      rw [boolCountFrom]
      simp only [Nat.add_zero] at htrue
      rw [htrue]
      simp only [boolIndicator]
      omega
  | start, length + 1, offset + 1, hoffset, htrue => by
      rw [boolCountFrom]
      have htail : 0 < boolCountFrom selected (start + 1) length :=
        boolCountFrom_pos_of_true selected (start + 1) length offset
          (by omega) (by
            have hindex : start + 1 + offset = start + (offset + 1) := by
              omega
            rw [hindex]
            exact htrue)
      omega

theorem rootFirstChannelComponentUnionSelectionCount_leftRoot_pos
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    0 < slabFaceStrandSelectionCount
      (rootFirstChannelComponentUnionSelected carrier links background hroot)
      (leftRootCopy carrier).faceId := by
  apply boolCountFrom_pos_of_true
    (slabFaceStrandSelectionAt
      (rootFirstChannelComponentUnionSelected
        carrier links background hroot)
      (leftRootCopy carrier).faceId)
    0 (physical (leftRootCopy carrier).faceId)
    (leftRootCopy carrier).slot.val (leftRootCopy carrier).slot.isLt
  rw [Nat.zero_add, slabFaceStrandSelectionAt_fin]
  exact rootFirstChannelComponentUnionSelected_leftRoot
    carrier links background hroot

theorem rootFirstChannelComponentUnionSelectionCount_rightRoot_pos
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    0 < slabFaceStrandSelectionCount
      (rootFirstChannelComponentUnionSelected carrier links background hroot)
      (rightRootCopy carrier).faceId := by
  apply boolCountFrom_pos_of_true
    (slabFaceStrandSelectionAt
      (rootFirstChannelComponentUnionSelected
        carrier links background hroot)
      (rightRootCopy carrier).faceId)
    0 (physical (rightRootCopy carrier).faceId)
    (rightRootCopy carrier).slot.val (rightRootCopy carrier).slot.isLt
  rw [Nat.zero_add, slabFaceStrandSelectionAt_fin]
  exact rootFirstChannelComponentUnionSelected_rightRoot
    carrier links background hroot

/-- The accepted union peel strictly lowers the physical label on the left
root face. -/
theorem rootFirstChannelComponentUnionLowerPhysical_leftRoot_lt
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    rootFirstChannelComponentUnionLowerPhysical carrier links background hroot
        (leftRootCopy carrier).faceId <
      physical (leftRootCopy carrier).faceId := by
  have hpositive : 0 < physical (leftRootCopy carrier).faceId :=
    (leftRootCopy carrier).slot.isLt
  have hdrop :=
    rootFirstChannelComponentUnionSelectionCount_leftRoot_pos
      carrier links background hroot
  unfold rootFirstChannelComponentUnionLowerPhysical
    lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  exact Nat.sub_lt hpositive hdrop

/-- The same accepted peel strictly lowers the right root face. -/
theorem rootFirstChannelComponentUnionLowerPhysical_rightRoot_lt
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (links : List SlabLink)
    (background : PresentedSlabFusionWitnessAssignment K 1 physical links)
    (hroot : (cubeDebtRootIncidence carrier.word).1.link ∈ links) :
    rootFirstChannelComponentUnionLowerPhysical carrier links background hroot
        (rightRootCopy carrier).faceId <
      physical (rightRootCopy carrier).faceId := by
  have hpositive : 0 < physical (rightRootCopy carrier).faceId :=
    (rightRootCopy carrier).slot.isLt
  have hdrop :=
    rootFirstChannelComponentUnionSelectionCount_rightRoot_pos
      carrier links background hroot
  unfold rootFirstChannelComponentUnionLowerPhysical
    lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  exact Nat.sub_lt hpositive hdrop

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
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionLowerPhysical
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionLoweredWitnessAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionLoweredAssignment
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionSelectionCount_leftRoot_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionLowerPhysical_leftRoot_lt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.rootFirstChannelComponentUnionLowerPhysical_rightRoot_lt
