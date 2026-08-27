/-
# The paired face component forced by a two-replica switch

A facewise two-replica transposition preserves every physical heat weight,
but it preserves the local intertwiner constraints only when its Boolean mask
is constant across every physical strand pairing in both replicas.  The
slot-zero component of the first replica is too small for that purpose: two
different strand slots of one physical face receive the same facewise switch
value.

This module constructs the correct finite obstruction graph.  It projects
every physical strand edge in each accepted expanded replica to its two face
identifiers, takes the union of the two projected edge lists, and selects the
component rooted at the target face.  On the complementary event the root is
fixed, the target is swapped, and the mask is proved closed across every
literal strand edge in either replica.  Thus the global graph component
compiles to the exact linkwise partner-closed selections consumed by the
existing local removal machinery.

Honest scope: no accepted switched output assignments or decoder are built
here, and no activity bound is asserted for the stronger paired-face
connected residue.  In particular, the earlier one-replica slot-zero decay
bound is not silently reused for this larger event.

Constructive contract: finite lists, Boolean adjacency, explicit rooted
components, and literal membership proofs only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, `noncomputable`, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
import YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent

namespace YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRootSeed
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Project literal strand edges to physical-face edges -/

/-- One physical-face edge obtained by forgetting the strand slots and the
link label of a literal strand edge. -/
structure SlabProjectedFaceEdge : Type where
  source : Nat
  target : Nat
  deriving DecidableEq

/-- Forget the slot data of one literal strand edge. -/
def slabProjectedFaceEdge
    {physical : SlabLabelling} (edge : SlabFaceStrandEdge physical) :
    SlabProjectedFaceEdge where
  source := edge.source.faceId
  target := edge.target.faceId

/-- Project a complete strand-edge list facewise. -/
def slabProjectedFaceEdges
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical)) :
    List SlabProjectedFaceEdge :=
  edges.map slabProjectedFaceEdge

/-- The face identifiers of every literal strand-copy endpoint.  Retaining
the source strand carrier makes endpoint membership proofs definitionally
close to the already verified global graph. -/
def slabFaceStrandFaceVertices
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical)) :
    List Nat :=
  (slabFaceStrandVertices edges).map fun copy => copy.faceId

/-- A displayed strand edge's source face belongs to the projected vertex
carrier. -/
theorem slabFaceStrandEdge_source_face_mem_vertices
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    {edge : SlabFaceStrandEdge physical} (hmem : edge ∈ edges) :
    edge.source.faceId ∈ slabFaceStrandFaceVertices edges := by
  unfold slabFaceStrandFaceVertices
  exact List.mem_map.mpr
    ⟨edge.source, slabFaceStrandEdge_source_mem_vertices hmem, rfl⟩

/-- A displayed strand edge's target face belongs to the projected vertex
carrier. -/
theorem slabFaceStrandEdge_target_face_mem_vertices
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    {edge : SlabFaceStrandEdge physical} (hmem : edge ∈ edges) :
    edge.target.faceId ∈ slabFaceStrandFaceVertices edges := by
  unfold slabFaceStrandFaceVertices
  exact List.mem_map.mpr
    ⟨edge.target, slabFaceStrandEdge_target_mem_vertices hmem, rfl⟩

/-- One projected edge connects two face identifiers in either orientation. -/
def slabProjectedFaceEdgeConnectsB
    (edge : SlabProjectedFaceEdge) (left right : Nat) : Bool :=
  (decide (edge.source = left) && decide (edge.target = right)) ||
    (decide (edge.source = right) && decide (edge.target = left))

/-- Boolean adjacency generated by a finite list of projected face edges. -/
def slabProjectedFaceAdjacentB
    (edges : List SlabProjectedFaceEdge) (left right : Nat) : Bool :=
  edges.any fun edge => slabProjectedFaceEdgeConnectsB edge left right

/-- The projected face adjacency is symmetric by construction. -/
theorem slabProjectedFaceAdjacentB_symmetric
    (edges : List SlabProjectedFaceEdge) :
    SymmetricAdj (slabProjectedFaceAdjacentB edges) := by
  intro left right
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      change
        (slabProjectedFaceEdgeConnectsB edge left right ||
            slabProjectedFaceAdjacentB rest left right) =
          (slabProjectedFaceEdgeConnectsB edge right left ||
            slabProjectedFaceAdjacentB rest right left)
      rw [ih]
      unfold slabProjectedFaceEdgeConnectsB
      exact congrArg
        (fun value => value || slabProjectedFaceAdjacentB rest right left)
        (Bool.or_comm _ _)

/-- Every displayed projected edge generates true adjacency. -/
theorem slabProjectedFaceAdjacentB_true_of_mem
    {edges : List SlabProjectedFaceEdge} {edge : SlabProjectedFaceEdge}
    (hmem : edge ∈ edges) :
    slabProjectedFaceAdjacentB edges edge.source edge.target = true := by
  unfold slabProjectedFaceAdjacentB
  apply List.any_eq_true.mpr
  exact ⟨edge, hmem, by simp [slabProjectedFaceEdgeConnectsB]⟩

/-! ## 2. The union graph of an attached two-replica pair -/

/-- The second attached replica exposes the same accepted-assignment
membership carried by the positive first-replica subtype. -/
def slabExpandedFineSourceEntryAssignment_mem
    {D : SlabPhysicalData} (entry : SlabExpandedFineSourceEntry D) :
    entry.1.2 ∈ slabFineFusionWitnesses D entry.1.1 :=
  (mem_slabExpandedFineSources_iff.mp entry.2).2

/-- Literal global strand edges of the first, root-positive replica. -/
def slabObservableTwoReplicaPairLeftStrandEdges
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabFaceStrandEdge pair.1.1.1) :=
  slabFineFusionWitnessFaceStrandEdges
    D pair.1.1.1 pair.1.1.2 pair.1.assignment_mem

/-- Literal global strand edges of the second attached replica. -/
def slabObservableTwoReplicaPairRightStrandEdges
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabFaceStrandEdge pair.2.1.1) :=
  slabFineFusionWitnessFaceStrandEdges
    D pair.2.1.1 pair.2.1.2
      (slabExpandedFineSourceEntryAssignment_mem pair.2)

/-- Union of both replicas after forgetting strand slots. -/
def slabObservableTwoReplicaPairPairedFaceEdges
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges (slabObservableTwoReplicaPairLeftStrandEdges D pair) ++
    slabProjectedFaceEdges (slabObservableTwoReplicaPairRightStrandEdges D pair)

/-- Union of both literal endpoint carriers after forgetting strand slots. -/
def slabObservableTwoReplicaPairPairedFaceVertices
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : List Nat :=
  slabFaceStrandFaceVertices
      (slabObservableTwoReplicaPairLeftStrandEdges D pair) ++
    slabFaceStrandFaceVertices
      (slabObservableTwoReplicaPairRightStrandEdges D pair)

/-- The paired face graph's Boolean adjacency. -/
def slabObservableTwoReplicaPairPairedFaceAdjacentB
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB
    (slabObservableTwoReplicaPairPairedFaceEdges D pair) left right

/-- The paired face graph is undirected. -/
theorem slabObservableTwoReplicaPairPairedFaceAdjacentB_symmetric
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SymmetricAdj (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair) :=
  slabProjectedFaceAdjacentB_symmetric
    (slabObservableTwoReplicaPairPairedFaceEdges D pair)

/-- The component of the union graph rooted at the face that must be
swapped. -/
def slabObservableTwoReplicaPairTargetFaceComponent
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : List Nat :=
  rootComponent (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
    (slabObservableTwoReplicaPairPairedFaceVertices D pair) targetFaceId

/-- The canonical facewise switch mask: swap exactly the target-rooted
component of the union graph. -/
def slabObservableTwoReplicaPairPairedFaceSwapMask
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId faceId : Nat) : Bool :=
  decide (faceId ∈
    slabObservableTwoReplicaPairTargetFaceComponent D pair targetFaceId)

/-- The actual obstruction predicate: the root belongs to the target-rooted
component of the union face graph. -/
def slabObservableTwoReplicaPairPairedFaceConnectedB
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : Bool :=
  slabObservableTwoReplicaPairPairedFaceSwapMask
    D pair targetFaceId rootFaceId

/-! ## 3. Source-cell endpoints and the canonical mask laws -/

/-- Membership in `11 x 00` exposes positivity of the target in the first
replica. -/
theorem slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    0 < pair.1.1.1 targetFaceId := by
  have hleft := (mem_cartesian_iff _ _ pair).mp hpair |>.1
  have hpositive := (List.mem_filter.mp hleft).2
  exact of_decide_eq_true hpositive

/-- The target face is a vertex of the paired union graph on every source
pair. -/
theorem slabObservableTwoReplicaPairTarget_mem_pairedFaceVertices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    targetFaceId ∈
      slabObservableTwoReplicaPairPairedFaceVertices D pair := by
  have hpositive := slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
    D rootFaceId targetFaceId pair hpair
  have hcopy := slabObservableRootCopy_mem_vertices
    D.cutoff D.extent targetFaceId htarget pair.1.1.1 hpositive
    pair.1.1.2 pair.1.assignment_mem
  apply List.mem_append_left
  unfold slabFaceStrandFaceVertices
  exact List.mem_map.mpr
    ⟨slabObservableRootCopy targetFaceId hpositive, hcopy, rfl⟩

/-- The fixed root face is likewise a vertex of the paired union graph. -/
theorem slabObservableTwoReplicaPairRoot_mem_pairedFaceVertices
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    rootFaceId ∈
      slabObservableTwoReplicaPairPairedFaceVertices D pair := by
  have hcopy := slabObservableRootCopy_mem_vertices
    D.cutoff D.extent rootFaceId hroot pair.1.1.1
    pair.1.source_positive pair.1.1.2 pair.1.assignment_mem
  apply List.mem_append_left
  unfold slabFaceStrandFaceVertices
  exact List.mem_map.mpr
    ⟨slabObservableRootCopy rootFaceId pair.1.source_positive,
      hcopy, rfl⟩

/-- The target-rooted component always swaps the target face. -/
theorem slabObservableTwoReplicaPairPairedFaceSwapMask_target
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
      D pair targetFaceId targetFaceId = true := by
  unfold slabObservableTwoReplicaPairPairedFaceSwapMask
    slabObservableTwoReplicaPairTargetFaceComponent
  exact decide_eq_true
    (root_mem_rootComponent
      (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
      (slabObservableTwoReplicaPairTarget_mem_pairedFaceVertices
        D rootFaceId targetFaceId htarget pair hpair))

/-- On the complementary obstruction event, the same canonical mask fixes
the root face. -/
theorem slabObservableTwoReplicaPairPairedFaceSwapMask_root_of_disconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hdisconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = false) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
      D pair targetFaceId rootFaceId = false :=
  hdisconnected

/-! ## 4. Closure across every literal edge of both replicas -/

private theorem pairedFaceSwapMask_eq_of_adjacent
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    {source target : Nat}
    (hsourceVertex : source ∈
      slabObservableTwoReplicaPairPairedFaceVertices D pair)
    (htargetVertex : target ∈
      slabObservableTwoReplicaPairPairedFaceVertices D pair)
    (hadjacent : slabObservableTwoReplicaPairPairedFaceAdjacentB
      D pair source target = true) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId target =
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId source := by
  have hseed := slabObservableTwoReplicaPairTarget_mem_pairedFaceVertices
    D rootFaceId targetFaceId htarget pair hpair
  have hsym := slabObservableTwoReplicaPairPairedFaceAdjacentB_symmetric D pair
  by_cases hsource : source ∈
      slabObservableTwoReplicaPairTargetFaceComponent D pair targetFaceId
  · have htargetMem : target ∈
        slabObservableTwoReplicaPairTargetFaceComponent
          D pair targetFaceId :=
      rootComponent_closed_under_edge
        (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
        hsym hseed hsource
        htargetVertex hadjacent
    simp [slabObservableTwoReplicaPairPairedFaceSwapMask,
      hsource, htargetMem]
  · by_cases htargetMem : target ∈
        slabObservableTwoReplicaPairTargetFaceComponent
          D pair targetFaceId
    · have hreverse :
          slabObservableTwoReplicaPairPairedFaceAdjacentB
            D pair target source = true := by
        rw [hsym target source]
        exact hadjacent
      have hsource' : source ∈
          slabObservableTwoReplicaPairTargetFaceComponent
            D pair targetFaceId :=
        rootComponent_closed_under_edge
          (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
          hsym hseed htargetMem
          hsourceVertex hreverse
      exact False.elim (hsource hsource')
    · simp [slabObservableTwoReplicaPairPairedFaceSwapMask,
        hsource, htargetMem]

/-- **Left-replica closure.**  The canonical face mask has equal values on
the two faces of every literal strand edge in the first replica. -/
theorem slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_left_edge
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    {edge : SlabFaceStrandEdge pair.1.1.1}
    (hedge : edge ∈ slabObservableTwoReplicaPairLeftStrandEdges D pair) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId edge.target.faceId =
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId edge.source.faceId := by
  apply pairedFaceSwapMask_eq_of_adjacent
    D rootFaceId targetFaceId htarget pair hpair
  · exact List.mem_append_left _
      (slabFaceStrandEdge_source_face_mem_vertices hedge)
  · exact List.mem_append_left _
      (slabFaceStrandEdge_target_face_mem_vertices hedge)
  · unfold slabObservableTwoReplicaPairPairedFaceAdjacentB
    change slabProjectedFaceAdjacentB
      (slabObservableTwoReplicaPairPairedFaceEdges D pair)
      (slabProjectedFaceEdge edge).source
      (slabProjectedFaceEdge edge).target = true
    apply slabProjectedFaceAdjacentB_true_of_mem
    unfold slabObservableTwoReplicaPairPairedFaceEdges
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨edge, hedge, rfl⟩)

/-- **Right-replica closure.**  The same canonical face mask has equal
values on every literal strand edge in the second replica. -/
theorem slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_right_edge
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    {edge : SlabFaceStrandEdge pair.2.1.1}
    (hedge : edge ∈ slabObservableTwoReplicaPairRightStrandEdges D pair) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId edge.target.faceId =
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId edge.source.faceId := by
  apply pairedFaceSwapMask_eq_of_adjacent
    D rootFaceId targetFaceId htarget pair hpair
  · exact List.mem_append_right _
      (slabFaceStrandEdge_source_face_mem_vertices hedge)
  · exact List.mem_append_right _
      (slabFaceStrandEdge_target_face_mem_vertices hedge)
  · unfold slabObservableTwoReplicaPairPairedFaceAdjacentB
    change slabProjectedFaceAdjacentB
      (slabObservableTwoReplicaPairPairedFaceEdges D pair)
      (slabProjectedFaceEdge edge).source
      (slabProjectedFaceEdge edge).target = true
    apply slabProjectedFaceAdjacentB_true_of_mem
    unfold slabObservableTwoReplicaPairPairedFaceEdges
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨edge, hedge, rfl⟩)

/-! ## 5. Compile global closure to every accepted local link -/

/-- **Generic global-to-local compiler.**  Any Boolean selection on physical
strand copies that is closed across every edge of one accepted global
assignment restricts to the partner-closed selection required at each local
link.  The two replica-specific theorems above provide exactly the `hclosed`
input for the paired face mask. -/
def slabGlobalEdgeClosedSelectionAtLink
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (selected : SlabFaceStrandCopy physical → Bool)
    (hclosed : ∀ {edge : SlabFaceStrandEdge physical},
      edge ∈ slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment →
      selected edge.target = selected edge.source)
    (linked : {link // link ∈ links}) :
    let auxiliary := slabFusionWitnessAssignmentAt linked.1 assignment
    let hmem := slabFusionWitnessAssignmentAt_mem_local
      K extent physical links assignment hassignment linked.1 linked.2
    SlabLinkPartnerClosedFaceSelection
      K extent physical linked.1 auxiliary hmem := by
  dsimp
  refine
    { selected := selected
      partner_closed := ?_ }
  intro terminal
  let edge := slabLinkFaceStrandEdgeOfTerminal
    K extent physical linked.1
      (slabFusionWitnessAssignmentAt linked.1 assignment)
      (slabFusionWitnessAssignmentAt_mem_local
        K extent physical links assignment hassignment linked.1 linked.2)
      terminal
  have hedge : edge ∈
      slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment :=
    slabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
      K extent physical links assignment hassignment linked terminal
  exact hclosed hedge

/-! ## 6. The stronger exact source partition -/

/-- Source pairs on which the paired union face component does not connect
the target to the root. -/
def slabObservablePairedFaceSeparatedFourCellSourcePairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellSourcePairs D rootFaceId targetFaceId).filter
    fun pair => !(
      slabObservableTwoReplicaPairPairedFaceConnectedB
        D rootFaceId targetFaceId pair)

/-- The exact paired-face connected obstruction inside `11 x 00`. -/
def slabObservablePairedFaceConnectedFourCellSourcePairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellSourcePairs D rootFaceId targetFaceId).filter
    fun pair => slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair

/-- The source determinant cell is exactly the disjoint weighted sum of the
new switchable sector and the paired-face obstruction sector. -/
theorem slabObservableFourCellSourcePairs_pairedFace_partition
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs D rootFaceId targetFaceId) ≈
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedFaceSeparatedFourCellSourcePairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedFaceConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  have hpartition := listQSum_filter_partition
    (slabObservableTwoReplicaPairWeight D)
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId =>
      slabObservableTwoReplicaPairPairedFaceConnectedB
        D rootFaceId targetFaceId pair)
    (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
  exact Q'.eqv_trans _ _ _ hpartition (Q'.add_comm_eqv _ _)

/-! ## Dependency gates -/

#print axioms slabObservableTwoReplicaPairPairedFaceSwapMask_target
#print axioms slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_left_edge
#print axioms slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_right_edge
#print axioms slabGlobalEdgeClosedSelectionAtLink
#print axioms slabObservableFourCellSourcePairs_pairedFace_partition

end YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
