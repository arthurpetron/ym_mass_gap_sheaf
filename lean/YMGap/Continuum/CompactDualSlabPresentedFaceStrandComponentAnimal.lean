/-
# A two-root presented strand union is one genuine Z4 lattice animal

A presented slab assignment may retain a different certified face order at
every link.  This module first proves that every edge of its global strand
graph still projects to a genuine plaquette adjacency through the displayed
link.  It then projects each rooted strand component to a duplicate-free
connected plaquette support.

The load-bearing contraction joins two such supports when their roots share a
physical link.  After deduplication their union is one connected Z4 animal,
even when the two strand components are disjoint.  Its support length is paid
by the exact selected-copy peel mass of the Boolean component union, so overlap
is never double counted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAnimal

set_option autoImplicit false

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Presented strand edges retain genuine geometric adjacency -/

/-- A terminal pair in an arbitrary certified face order shares the displayed
slab link on both of its physical plaquettes. -/
def orderedSlabLinkFaceStrandEdgeOfTerminalAdjacent
    (K : Nat) {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent
        (orderedSlabLinkFaceStrandEdgeOfTerminal
          K physical order auxiliary hmem terminal).source.faceId)
      (slabPlaquetteAt extent
        (orderedSlabLinkFaceStrandEdgeOfTerminal
          K physical order auxiliary hmem terminal).target.faceId) := by
  refine { link := link, on_p := ?_, on_q := ?_ }
  · change decide
      (link ∈ edgesOf
        (slabPlaquetteAt extent
          (orderedSlabLinkPhysicalTerminalOccurrence
            K physical order auxiliary hmem terminal).faceId)) = true
    exact decide_eq_true_eq.mpr
      (link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
        (OrderedSlabLinkFaceStrandOccurrence.faceId_mem_incident
          (orderedSlabLinkPhysicalTerminalOccurrence
            K physical order auxiliary hmem terminal)))
  · change decide
      (link ∈ edgesOf
        (slabPlaquetteAt extent
          (orderedSlabLinkPhysicalTerminalOccurrence K physical order
            auxiliary hmem
              (orderedSlabLinkPhysicalStrandPartner
                K physical order auxiliary hmem terminal)).faceId)) = true
    exact decide_eq_true_eq.mpr
      (link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
        (OrderedSlabLinkFaceStrandOccurrence.faceId_mem_incident
          (orderedSlabLinkPhysicalTerminalOccurrence K physical order
            auxiliary hmem
              (orderedSlabLinkPhysicalStrandPartner
                K physical order auxiliary hmem terminal))))

/-- All edges of one ordered presentation with their actual plaquette
adjacency witnesses retained as Type-level data. -/
def orderedSlabLinkGeometricFaceStrandEdges
    (K : Nat) {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order) :
    List (SlabGeometricFaceStrandEdge extent physical) :=
  (orderedSlabLinkPhysicalStrandTerminals
    K physical order auxiliary hmem).map fun terminal =>
      { edge := orderedSlabLinkFaceStrandEdgeOfTerminal
          K physical order auxiliary hmem terminal
        adjacent := orderedSlabLinkFaceStrandEdgeOfTerminalAdjacent
          K order auxiliary hmem terminal }

theorem orderedSlabLinkGeometricFaceStrandEdges_map_edge
    (K : Nat) {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order) :
    (orderedSlabLinkGeometricFaceStrandEdges
      K order auxiliary hmem).map SlabGeometricFaceStrandEdge.edge =
      orderedSlabLinkFaceStrandEdges K physical order auxiliary hmem := by
  unfold orderedSlabLinkGeometricFaceStrandEdges
    orderedSlabLinkFaceStrandEdges
  rw [List.map_map]
  apply List.map_congr_left
  intro terminal _
  rfl

def presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdgesAt
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (linked : {link // link ∈ links}) :
    List (SlabGeometricFaceStrandEdge extent physical) :=
  let witness := assignment linked
  orderedSlabLinkGeometricFaceStrandEdges K witness.order
    witness.auxiliary witness.auxiliary_mem

def presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdges
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) :
    List (SlabGeometricFaceStrandEdge extent physical) :=
  links.attach.flatMap
    (presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdgesAt
      K extent physical links assignment)

private theorem flatMapCongrLeftLocal {A B : Type}
    (items : List A) (left right : A -> List B)
    (heq : forall item, item ∈ items -> left item = right item) :
    items.flatMap left = items.flatMap right := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.flatMap_cons,
        heq head List.mem_cons_self]
      apply congrArg (fun suffix => right head ++ suffix)
      apply ih
      intro item hitem
      exact heq item (List.mem_cons_of_mem head hitem)

theorem presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdges_map_edge
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) :
    (presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdges
      K extent physical links assignment).map
        SlabGeometricFaceStrandEdge.edge =
      presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment := by
  unfold presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdges
    presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdgesAt
    presentedSlabFusionWitnessAssignmentFaceStrandEdges
    presentedSlabFusionWitnessAssignmentFaceStrandEdgesAt
  rw [List.map_flatMap]
  apply flatMapCongrLeftLocal
  intro linked _
  exact orderedSlabLinkGeometricFaceStrandEdges_map_edge
    K (assignment linked).order (assignment linked).auxiliary
      (assignment linked).auxiliary_mem

/-- Every Boolean adjacency in a heterogeneous presented graph projects to a
genuine Z4 plaquette adjacency. -/
def presentedSlabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (left right : SlabFaceStrandCopy physical)
    (hadj : slabFaceStrandAdjacentB
      (presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment) left right = true) :
    z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent left.faceId)
      (slabPlaquetteAt extent right.faceId) := by
  rw [←
    presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdges_map_edge
      K extent physical links assignment] at hadj
  exact slabGeometricFaceStrandAdjacentWitness left right
    (presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdges
      K extent physical links assignment) hadj

/-! ## 2. One presented rooted component -/

/-- The duplicate-free plaquette support of a rooted component in a
heterogeneous presented graph. -/
def presentedComponentPlaquetteSupport
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) : List Z4Plaq :=
  (seed.component.map
    (slabFaceStrandCopyPlaquette (extent := extent))).eraseDups

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    forall predicate : A -> Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filterTrueLocal {A : Type} : forall items : List A,
    items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

private theorem eraseDupsLengthLeLocal {A : Type}
    [BEq A] (items : List A) :
    items.eraseDups.length <= items.length := by
  cases items with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hfilter := List.length_filter_le
        (fun item : A => !item == head) tail
      have ih := eraseDupsLengthLeLocal
        (tail.filter fun item => !item == head)
      omega
termination_by items.length
decreasing_by
  simp_wf
  omega

theorem mem_presentedComponentPlaquetteSupport_iff
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (plaquette : Z4Plaq) :
    plaquette ∈ presentedComponentPlaquetteSupport seed ↔
      ∃ copy, copy ∈ seed.component ∧
        slabFaceStrandCopyPlaquette (extent := extent) copy = plaquette := by
  simp [presentedComponentPlaquetteSupport,
    slabFaceStrandCopyPlaquette]

def presentedComponentPlaquetteSupportCopyValue
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (plaquette : Z4Plaq) : SlabFaceStrandCopy physical :=
  listFirstMappedPreimageOr
    (slabFaceStrandCopyPlaquette (extent := extent)) seed.root plaquette
      seed.component

theorem presentedComponentPlaquetteSupportCopyValue_mem
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (plaquette : Z4Plaq) :
    presentedComponentPlaquetteSupportCopyValue seed plaquette ∈
      seed.component := by
  rcases listFirstMappedPreimageOr_mem_or_eq_fallback
      (slabFaceStrandCopyPlaquette (extent := extent)) seed.root plaquette
      seed.component with hmem | hroot
  · exact hmem
  · change listFirstMappedPreimageOr
        (slabFaceStrandCopyPlaquette (extent := extent)) seed.root plaquette
          seed.component ∈ seed.component
    rw [hroot]
    unfold SlabFaceStrandSeed.component
    exact root_mem_rootComponent
      (slabFaceStrandAdjacentB
        (presentedSlabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment))
      seed.root_mem

theorem presentedComponentPlaquetteSupportCopyValue_projection
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ presentedComponentPlaquetteSupport seed) :
    slabFaceStrandCopyPlaquette (extent := extent)
      (presentedComponentPlaquetteSupportCopyValue seed plaquette) =
        plaquette := by
  exact listFirstMappedPreimageOr_projection
    (slabFaceStrandCopyPlaquette (extent := extent)) seed.root plaquette
      seed.component (List.mem_eraseDups.mp hplaquette)

theorem presentedComponentPlaquetteSupport_nodup
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    (presentedComponentPlaquetteSupport seed).Nodup := by
  unfold presentedComponentPlaquetteSupport
  exact eraseDupsNodupLocal _

theorem presentedRootPlaquette_mem_componentSupport
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    slabPlaquetteAt extent seed.root.faceId ∈
      presentedComponentPlaquetteSupport seed := by
  apply (mem_presentedComponentPlaquetteSupport_iff seed _).mpr
  refine ⟨seed.root, ?_, rfl⟩
  unfold SlabFaceStrandSeed.component
  exact root_mem_rootComponent
    (slabFaceStrandAdjacentB
      (presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment))
    seed.root_mem

theorem presentedComponentPlaquetteSupport_subset_boundaryCompleteSlab
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ presentedComponentPlaquetteSupport seed) :
    plaquette ∈ boundaryCompleteSlabPlaquettes extent := by
  obtain ⟨copy, hcopy, hcopyEq⟩ :=
    (mem_presentedComponentPlaquetteSupport_iff seed plaquette).mp hplaquette
  rw [← hcopyEq]
  exact slabPlaquetteAt_mem
    (PresentedSlabFusionWitnessFaceStrandSeed.component_faceId_physical
      seed copy hcopy)

/-- Structural projection of a presented strand-component path to the
corresponding internal plaquette path. -/
def presentedComponentChainToPlaquetteChain
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    {left right : SlabFaceStrandCopy physical} ->
      FiniteBoolGraphComponents.ChainIn
        (slabFaceStrandAdjacentB
          (presentedSlabFusionWitnessAssignmentFaceStrandEdges
            K extent physical links assignment))
        seed.component left right ->
      PolymerModel.ChainIn z4Chain.toLattice
        (presentedComponentPlaquetteSupport seed)
        (slabPlaquetteAt extent left.faceId)
        (slabPlaquetteAt extent right.faceId)
  | _, _, FiniteBoolGraphComponents.ChainIn.refl copy =>
      PolymerModel.ChainIn.refl _
  | left, _right,
      FiniteBoolGraphComponents.ChainIn.step
        (b := next) hadj hnext rest =>
      PolymerModel.ChainIn.step
        (presentedSlabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
          K extent physical links assignment left next hadj)
        ((mem_presentedComponentPlaquetteSupport_iff seed _).mpr
          ⟨next, hnext, rfl⟩)
        (presentedComponentChainToPlaquetteChain seed rest)

def presentedComponentPlaquetteSupport_connected
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      (presentedComponentPlaquetteSupport seed) := by
  intro leftPlaquette rightPlaquette hleft hright
  let left := presentedComponentPlaquetteSupportCopyValue seed leftPlaquette
  let right := presentedComponentPlaquetteSupportCopyValue seed rightPlaquette
  have hleftComponent : left ∈ seed.component :=
    presentedComponentPlaquetteSupportCopyValue_mem seed leftPlaquette
  have hrightComponent : right ∈ seed.component :=
    presentedComponentPlaquetteSupportCopyValue_mem seed rightPlaquette
  have hleftEq : slabPlaquetteAt extent left.faceId = leftPlaquette := by
    simpa [left, slabFaceStrandCopyPlaquette] using
      presentedComponentPlaquetteSupportCopyValue_projection
        seed leftPlaquette hleft
  have hrightEq : slabPlaquetteAt extent right.faceId = rightPlaquette := by
    simpa [right, slabFaceStrandCopyPlaquette] using
      presentedComponentPlaquetteSupportCopyValue_projection
        seed rightPlaquette hright
  have hstrand := rootComponent_connected
    (slabFaceStrandAdjacentB
      (presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment))
    (slabFaceStrandAdjacentB_symmetric
      (presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment))
    seed.root_mem left right hleftComponent hrightComponent
  have hprojected := presentedComponentChainToPlaquetteChain seed hstrand
  rw [hleftEq, hrightEq] at hprojected
  exact hprojected

/-! ## 3. Join two root components through one physical root link -/

/-- Deduplicate the geometric union of two rooted presented components. -/
def presentedSeedUnionPlaquetteSupport
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) : List Z4Plaq :=
  (presentedComponentPlaquetteSupport left ++
    presentedComponentPlaquetteSupport right).eraseDups

theorem mem_presentedSeedUnionPlaquetteSupport_iff
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (plaquette : Z4Plaq) :
    plaquette ∈ presentedSeedUnionPlaquetteSupport left right ↔
      plaquette ∈ presentedComponentPlaquetteSupport left ++
        presentedComponentPlaquetteSupport right := by
  simp [presentedSeedUnionPlaquetteSupport]

theorem presentedSeedUnionPlaquetteSupport_nodup
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    (presentedSeedUnionPlaquetteSupport left right).Nodup := by
  unfold presentedSeedUnionPlaquetteSupport
  exact eraseDupsNodupLocal _

theorem presentedLeftRootPlaquette_mem_seedUnionSupport
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    slabPlaquetteAt extent left.root.faceId ∈
      presentedSeedUnionPlaquetteSupport left right := by
  unfold presentedSeedUnionPlaquetteSupport
  exact List.mem_eraseDups.mpr (List.mem_append.mpr
    (Or.inl (presentedRootPlaquette_mem_componentSupport left)))

theorem presentedRightRootPlaquette_mem_seedUnionSupport
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    slabPlaquetteAt extent right.root.faceId ∈
      presentedSeedUnionPlaquetteSupport left right := by
  unfold presentedSeedUnionPlaquetteSupport
  exact List.mem_eraseDups.mpr (List.mem_append.mpr
    (Or.inr (presentedRootPlaquette_mem_componentSupport right)))

private def plaquetteChainInTrans {support : List Z4Plaq} :
    {first middle last : Z4Plaq} ->
      PolymerModel.ChainIn z4Chain.toLattice support first middle ->
      PolymerModel.ChainIn z4Chain.toLattice support middle last ->
      PolymerModel.ChainIn z4Chain.toLattice support first last
  | _, _, _, .refl _, right => right
  | _, _, _, .step adjacent hnext rest, right =>
      .step adjacent hnext (plaquetteChainInTrans rest right)

private def plaquetteChainInMono {small large : List Z4Plaq}
    (hsubset : forall plaquette, plaquette ∈ small -> plaquette ∈ large) :
    {first last : Z4Plaq} ->
      PolymerModel.ChainIn z4Chain.toLattice small first last ->
      PolymerModel.ChainIn z4Chain.toLattice large first last
  | _, _, .refl plaquette => .refl plaquette
  | _, _, .step adjacent hnext rest =>
      .step adjacent (hsubset _ hnext) (plaquetteChainInMono hsubset rest)

private def connectedInAppendOfBridge
    {left right : List Z4Plaq}
    (hleft : PolymerModel.connectedIn (L := z4Chain.toLattice) left)
    (hright : PolymerModel.connectedIn (L := z4Chain.toLattice) right)
    {leftBridge rightBridge : Z4Plaq}
    (hleftBridge : leftBridge ∈ left)
    (hrightBridge : rightBridge ∈ right)
    (hbridge : z4Chain.toLattice.Adjacent leftBridge rightBridge) :
    PolymerModel.connectedIn (L := z4Chain.toLattice) (left ++ right) := by
  intro first last hfirst hlast
  by_cases hfirstLeft : first ∈ left
  · by_cases hlastLeft : last ∈ left
    · exact plaquetteChainInMono
        (fun plaquette hplaquette =>
          List.mem_append.mpr (Or.inl hplaquette))
        (hleft first last hfirstLeft hlastLeft)
    · have hlastRight : last ∈ right :=
        (List.mem_append.mp hlast).resolve_left hlastLeft
      exact plaquetteChainInTrans
        (plaquetteChainInMono
          (fun plaquette hplaquette =>
            List.mem_append.mpr (Or.inl hplaquette))
          (hleft first leftBridge hfirstLeft hleftBridge))
        (.step hbridge (List.mem_append.mpr (Or.inr hrightBridge))
          (plaquetteChainInMono
            (fun plaquette hplaquette =>
              List.mem_append.mpr (Or.inr hplaquette))
            (hright rightBridge last hrightBridge hlastRight)))
  · have hfirstRight : first ∈ right :=
      (List.mem_append.mp hfirst).resolve_left hfirstLeft
    by_cases hlastLeft : last ∈ left
    · exact plaquetteChainInTrans
        (plaquetteChainInMono
          (fun plaquette hplaquette =>
            List.mem_append.mpr (Or.inr hplaquette))
          (hright first rightBridge hfirstRight hrightBridge))
        (.step (adjacentSymm hbridge)
          (List.mem_append.mpr (Or.inl hleftBridge))
          (plaquetteChainInMono
            (fun plaquette hplaquette =>
              List.mem_append.mpr (Or.inl hplaquette))
            (hleft leftBridge last hleftBridge hlastLeft)))
    · have hlastRight : last ∈ right :=
        (List.mem_append.mp hlast).resolve_left hlastLeft
      exact plaquetteChainInMono
        (fun plaquette hplaquette =>
          List.mem_append.mpr (Or.inr hplaquette))
        (hright first last hfirstRight hlastRight)

/-- If the two roots share a link, the deduplicated union support is internally
connected.  This does not require the strand components to intersect. -/
def presentedSeedUnionPlaquetteSupport_connected
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (hrootAdjacent : z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent left.root.faceId)
      (slabPlaquetteAt extent right.root.faceId)) :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      (presentedSeedUnionPlaquetteSupport left right) := by
  let rawSupport := presentedComponentPlaquetteSupport left ++
    presentedComponentPlaquetteSupport right
  have hraw : PolymerModel.connectedIn (L := z4Chain.toLattice) rawSupport :=
    connectedInAppendOfBridge
      (presentedComponentPlaquetteSupport_connected left)
      (presentedComponentPlaquetteSupport_connected right)
      (presentedRootPlaquette_mem_componentSupport left)
      (presentedRootPlaquette_mem_componentSupport right)
      hrootAdjacent
  intro first last hfirst hlast
  have hfirstRaw : first ∈
      presentedComponentPlaquetteSupport left ++
        presentedComponentPlaquetteSupport right := by
    exact (mem_presentedSeedUnionPlaquetteSupport_iff
      left right first).mp hfirst
  have hlastRaw : last ∈
      presentedComponentPlaquetteSupport left ++
        presentedComponentPlaquetteSupport right := by
    exact (mem_presentedSeedUnionPlaquetteSupport_iff
      left right last).mp hlast
  apply plaquetteChainInMono
    (fun plaquette hplaquette =>
      (mem_presentedSeedUnionPlaquetteSupport_iff
        left right plaquette).mpr hplaquette)
  exact hraw first last hfirstRaw hlastRaw

/-- The bridged union is one ordinary rooted Z4 animal. -/
theorem presentedSeedUnionPlaquetteAnimal
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (hrootAdjacent : z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent left.root.faceId)
      (slabPlaquetteAt extent right.root.faceId)) :
    IsClusterThroughIn z4Chain
      (slabPlaquetteAt extent left.root.faceId)
      (presentedSeedUnionPlaquetteSupport left right).length
      (presentedSeedUnionPlaquetteSupport left right) := by
  exact ⟨rfl,
    presentedLeftRootPlaquette_mem_seedUnionSupport left right,
    presentedSeedUnionPlaquetteSupport_nodup left right,
    ⟨presentedSeedUnionPlaquetteSupport_connected
      left right hrootAdjacent⟩⟩

/-! ## 4. The union support is paid once by physical peel mass -/

private theorem listLengthLeListNatWeightOfOneLe
    {A : Type} (weight : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> 1 <= weight item) ->
      items.length <= listNatWeight weight items
  | [], _ => Nat.le_refl 0
  | head :: tail, hweight => by
      have hhead := hweight head List.mem_cons_self
      have htail := listLengthLeListNatWeightOfOneLe weight tail
        (fun item hitem => hweight item (List.mem_cons_of_mem head hitem))
      simp only [List.length_cons, listNatWeight]
      omega

private theorem listNatWeightEqNatListSumMap {A : Type}
    (weight : A -> Nat) : forall items : List A,
    listNatWeight weight items = natListSum (items.map weight)
  | [] => rfl
  | head :: tail => by
      simp only [listNatWeight, List.map_cons, natListSum]
      rw [listNatWeightEqNatListSumMap weight tail]

private theorem listNatWeightCongrLocal {A : Type}
    (left right : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> left item = right item) ->
      listNatWeight left items = listNatWeight right items
  | [], _ => rfl
  | head :: tail, heq => by
      simp only [listNatWeight]
      rw [heq head List.mem_cons_self]
      apply congrArg (fun value => right head + value)
      apply listNatWeightCongrLocal left right tail
      intro item hitem
      exact heq item (List.mem_cons_of_mem head hitem)

private theorem seedSelectedInSupportedUnion_left
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (copy : SlabFaceStrandCopy physical) (hcopy : copy ∈ left.component) :
    (PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
      left right).closed.selected copy = true := by
  unfold PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
    PresentedSlabPartnerClosedFaceSelection.ofSeedUnion
  dsimp only
  have hleft : left.selected copy = true := by
    unfold SlabFaceStrandSeed.selected
    exact decide_eq_true_eq.mpr hcopy
  simp [hleft]

private theorem seedSelectedInSupportedUnion_right
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (copy : SlabFaceStrandCopy physical) (hcopy : copy ∈ right.component) :
    (PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
      left right).closed.selected copy = true := by
  unfold PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
    PresentedSlabPartnerClosedFaceSelection.ofSeedUnion
  dsimp only
  have hright : right.selected copy = true := by
    unfold SlabFaceStrandSeed.selected
    exact decide_eq_true_eq.mpr hcopy
  simp [hright]

/-- Deduplication plus the exact selected-copy multiplicities ensures that the
two-root union's geometric support consumes at most one unit of support per
unit of physical peel mass, including when the components overlap. -/
theorem presentedSeedUnionPlaquetteSupport_length_le_peelFaces
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    (presentedSeedUnionPlaquetteSupport left right).length <=
      (PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
        left right).peelFaces.length := by
  let selection :=
    PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion left right
  let multiplicity : Z4Plaq -> Nat := fun plaquette =>
    slabFaceStrandSelectionCount selection.closed.selected
      (slabFaceIdOfPlaquette extent plaquette)
  let physicalPlaquettes : List Z4Plaq :=
    (slabPhysicalFaceEdges extent).map (slabPlaquetteAt extent)
  have hsupportBoundary : forall plaquette,
      plaquette ∈ presentedSeedUnionPlaquetteSupport left right ->
        plaquette ∈ boundaryCompleteSlabPlaquettes extent := by
    intro plaquette hplaquette
    have hraw := List.mem_eraseDups.mp hplaquette
    rcases List.mem_append.mp hraw with hleft | hright
    · exact presentedComponentPlaquetteSupport_subset_boundaryCompleteSlab
        left plaquette hleft
    · exact presentedComponentPlaquetteSupport_subset_boundaryCompleteSlab
        right plaquette hright
  have hsupportPhysical : forall plaquette,
      plaquette ∈ presentedSeedUnionPlaquetteSupport left right ->
        plaquette ∈ physicalPlaquettes := by
    intro plaquette hplaquette
    have hboundary := hsupportBoundary plaquette hplaquette
    let faceId := slabFaceIdOfPlaquette extent plaquette
    have hfaceId : faceId ∈ slabPhysicalFaceEdges extent :=
      slabFaceIdOfPlaquette_physical hboundary
    exact List.mem_map.mpr ⟨faceId, hfaceId,
      slabPlaquetteAt_faceIdOfPlaquette hboundary⟩
  have hpositive : forall plaquette,
      plaquette ∈ presentedSeedUnionPlaquetteSupport left right ->
        1 <= multiplicity plaquette := by
    intro plaquette hplaquette
    have hraw := List.mem_eraseDups.mp hplaquette
    rcases List.mem_append.mp hraw with hleft | hright
    · obtain ⟨copy, hcopy, hcopyEq⟩ :=
        (mem_presentedComponentPlaquetteSupport_iff left plaquette).mp hleft
      have hphysical :=
        PresentedSlabFusionWitnessFaceStrandSeed.component_faceId_physical
          left copy hcopy
      have hselected := seedSelectedInSupportedUnion_left
        left right copy hcopy
      have hcount := slabFaceStrandSelectionCount_pos_of_selected
        selection.closed.selected copy hselected
      unfold multiplicity
      rw [← hcopyEq]
      change 1 <= slabFaceStrandSelectionCount selection.closed.selected
        (slabFaceIdOfPlaquette extent
          (slabPlaquetteAt extent copy.faceId))
      rw [slabFaceIdOfPlaquette_slabPlaquetteAt hphysical]
      exact hcount
    · obtain ⟨copy, hcopy, hcopyEq⟩ :=
        (mem_presentedComponentPlaquetteSupport_iff right plaquette).mp hright
      have hphysical :=
        PresentedSlabFusionWitnessFaceStrandSeed.component_faceId_physical
          right copy hcopy
      have hselected := seedSelectedInSupportedUnion_right
        left right copy hcopy
      have hcount := slabFaceStrandSelectionCount_pos_of_selected
        selection.closed.selected copy hselected
      unfold multiplicity
      rw [← hcopyEq]
      change 1 <= slabFaceStrandSelectionCount selection.closed.selected
        (slabFaceIdOfPlaquette extent
          (slabPlaquetteAt extent copy.faceId))
      rw [slabFaceIdOfPlaquette_slabPlaquetteAt hphysical]
      exact hcount
  have hlength : (presentedSeedUnionPlaquetteSupport left right).length <=
      listNatWeight multiplicity
        (presentedSeedUnionPlaquetteSupport left right) :=
    listLengthLeListNatWeightOfOneLe multiplicity _ hpositive
  have hweighted := listNatWeight_le_of_nodup_mem multiplicity
    (presentedSeedUnionPlaquetteSupport left right) physicalPlaquettes
    (presentedSeedUnionPlaquetteSupport_nodup left right) hsupportPhysical
  calc
    (presentedSeedUnionPlaquetteSupport left right).length <=
        listNatWeight multiplicity
          (presentedSeedUnionPlaquetteSupport left right) := hlength
    _ <= listNatWeight multiplicity physicalPlaquettes := hweighted
    _ = listNatWeight
        (fun faceId => multiplicity (slabPlaquetteAt extent faceId))
        (slabPhysicalFaceEdges extent) := by
      unfold physicalPlaquettes
      exact listNatWeight_map (slabPlaquetteAt extent) multiplicity _
    _ = listNatWeight
        (slabFaceStrandSelectionCount selection.closed.selected)
        (slabPhysicalFaceEdges extent) := by
      apply listNatWeightCongrLocal
      intro faceId hfaceId
      unfold multiplicity
      rw [slabFaceIdOfPlaquette_slabPlaquetteAt hfaceId]
    _ = natListSum ((slabPhysicalFaceEdges extent).map
        (slabFaceStrandSelectionCount selection.closed.selected)) :=
      listNatWeightEqNatListSumMap _ _
    _ = selection.peelFaces.length :=
      (presentedSelection_peelFaces_length_eq_physicalDrop_l1 selection).symm

#print axioms orderedSlabLinkFaceStrandEdgeOfTerminalAdjacent
#print axioms orderedSlabLinkGeometricFaceStrandEdges
#print axioms presentedSlabFusionWitnessAssignmentGeometricFaceStrandEdges_map_edge
#print axioms presentedSlabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
#print axioms presentedComponentPlaquetteSupport
#print axioms presentedComponentPlaquetteSupport_connected
#print axioms presentedSeedUnionPlaquetteSupport
#print axioms presentedSeedUnionPlaquetteSupport_connected
#print axioms presentedSeedUnionPlaquetteAnimal
#print axioms presentedSeedUnionPlaquetteSupport_length_le_peelFaces

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAnimal
