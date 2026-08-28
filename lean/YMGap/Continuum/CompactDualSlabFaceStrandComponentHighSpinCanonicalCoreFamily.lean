/-
# Assemble and pack the canonical family of core-attached components

The preceding packing theorem accepted any constructively separated family.
This module supplies the missing canonical family from the actual global
face-strand graph of one accepted fusion assignment.

The raw endpoint list may repeat a face-strand copy, so connected components
are computed on its `eraseDups` carrier.  The accepted peel machinery,
however, uses rooted components over the raw list.  Identity graph maps in
both directions prove that raw and deduplicated rooted components have the
same support.  The rooted component chosen from one canonical component is
then exactly that component up to duplicate erasure.

Each canonical component is classified by the executable high-spin reserve
check.  Exterior components emit no core anchor; blocked components emit
their decoded selected low-spin copy.  Distinct canonical components are
disjoint, so emitted anchor copies are distinct.  Thus the complete canonical
core-anchor list is duplicate-free and injects into the finite core carrier,
giving the explicit bound

```text
canonicalCoreAnchorCopies.length
  <= (number of physical faces) * threshold.
```

This is exhaustive component assembly and core packing.  It does not yet sum
the exterior decorations attached to a core component or prove finite-core
coercivity.

Constructive contract: executable finite graph components, identity graph
maps, finite `filterMap`, and duplicate-free pigeonhole only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCorePacking
import YMGap.Continuum.FiniteBoolGraphRootComponentMap

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCorePacking
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteBoolGraphRootComponentMap
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Canonical components on the duplicate-free endpoint carrier -/

/-- The endpoint carrier with repeated physical copies removed. -/
def slabFaceStrandDistinctVertices
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical)) :
    List (SlabFaceStrandCopy physical) :=
  (slabFaceStrandVertices edges).eraseDups

private theorem filtered_eraseDups_nodup {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A -> Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        apply List.nodup_cons.mpr
        refine ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filter_true : ∀ {A : Type} (items : List A),
    items.filter (fun _ => true) = items
  | _, [] => rfl
  | _, head :: tail => congrArg (List.cons head) (filter_true tail)

private theorem eraseDups_nodup {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have hnodup := filtered_eraseDups_nodup items (fun _ => true)
  rw [filter_true] at hnodup
  exact hnodup

/-- The canonical connected components of the assignment's physical
face-strand graph. -/
def slabFaceStrandCanonicalComponents
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical)) :
    List (List (SlabFaceStrandCopy physical)) :=
  graphComponents (slabFaceStrandAdjacentB edges)
    (slabFaceStrandDistinctVertices edges)

/-- The canonical component list is duplicate-free. -/
theorem slabFaceStrandCanonicalComponents_nodup
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical)) :
    (slabFaceStrandCanonicalComponents edges).Nodup := by
  unfold slabFaceStrandCanonicalComponents
  exact graphComponents_nodup _
    (eraseDups_nodup (slabFaceStrandVertices edges))

/-- Distinct canonical components have disjoint supports. -/
theorem slabFaceStrandCanonicalComponents_distinctDisjoint
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical)) :
    DistinctDisjoint (slabFaceStrandCanonicalComponents edges) := by
  unfold slabFaceStrandCanonicalComponents
  exact graphComponents_distinctDisjoint _
    (eraseDups_nodup (slabFaceStrandVertices edges))

/-! ## 2. Raw and deduplicated rooted components have the same support -/

/-- The identity graph map from the raw endpoint list to its duplicate-free
version. -/
def rawToDistinctRootedHom
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical))
    (root : SlabFaceStrandCopy physical) :
    RootedFiniteBoolGraphHom
      (slabFaceStrandAdjacentB edges) (slabFaceStrandVertices edges) root
      (slabFaceStrandAdjacentB edges) (slabFaceStrandDistinctVertices edges)
        root where
  toFun := fun copy => copy
  map_root := rfl
  map_vertex := fun _ hcopy => List.mem_eraseDups.mpr hcopy
  map_edge := fun _ _ _ _ hedge => hedge

/-- The reverse identity graph map forgets only duplicate erasure. -/
def distinctToRawRootedHom
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical))
    (root : SlabFaceStrandCopy physical) :
    RootedFiniteBoolGraphHom
      (slabFaceStrandAdjacentB edges) (slabFaceStrandDistinctVertices edges)
        root
      (slabFaceStrandAdjacentB edges) (slabFaceStrandVertices edges) root where
  toFun := fun copy => copy
  map_root := rfl
  map_vertex := fun _ hcopy => List.mem_eraseDups.mp hcopy
  map_edge := fun _ _ _ _ hedge => hedge

/-- Rooting before or after endpoint deduplication gives the same component
support. -/
theorem mem_rawRootComponent_iff_mem_distinctRootComponent
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    {root copy : SlabFaceStrandCopy physical}
    (hroot : root ∈ slabFaceStrandVertices edges) :
    copy ∈ rootComponent (slabFaceStrandAdjacentB edges)
        (slabFaceStrandVertices edges) root ↔
      copy ∈ rootComponent (slabFaceStrandAdjacentB edges)
        (slabFaceStrandDistinctVertices edges) root := by
  constructor
  · intro hcopy
    exact (rawToDistinctRootedHom edges root).map_mem_targetRootComponent
      (slabFaceStrandAdjacentB_symmetric edges)
      (slabFaceStrandAdjacentB_symmetric edges)
      hroot (List.mem_eraseDups.mpr hroot) hcopy
  · intro hcopy
    exact (distinctToRawRootedHom edges root).map_mem_targetRootComponent
      (slabFaceStrandAdjacentB_symmetric edges)
      (slabFaceStrandAdjacentB_symmetric edges)
      (List.mem_eraseDups.mpr hroot) hroot hcopy

/-! ## 3. A canonical seed for every canonical component -/

/-- A canonical component bundled with its literal membership in the
canonical component list. -/
abbrev SlabFaceStrandCanonicalComponent
    {physical : SlabLabelling} (edges : List (SlabFaceStrandEdge physical)) :=
  {component // component ∈ slabFaceStrandCanonicalComponents edges}

/-- The finite component compiler constructively supplies a root in each
canonical component. -/
def SlabFaceStrandCanonicalComponent.root
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    (component : SlabFaceStrandCanonicalComponent edges) :
    SlabFaceStrandCopy physical :=
  (graphComponents_allNonempty
    (slabFaceStrandAdjacentB edges)
    (slabFaceStrandDistinctVertices edges)
    component.1 component.2).1

/-- The computed root lies in its displayed canonical component. -/
theorem SlabFaceStrandCanonicalComponent.root_mem
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    (component : SlabFaceStrandCanonicalComponent edges) :
    component.root ∈ component.1 :=
  (graphComponents_allNonempty
    (slabFaceStrandAdjacentB edges)
    (slabFaceStrandDistinctVertices edges)
    component.1 component.2).2

/-- Regard the computed component root as the explicit seed consumed by the
accepted strand peel machinery. -/
def SlabFaceStrandCanonicalComponent.seed
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    (component : SlabFaceStrandCanonicalComponent edges) :
    SlabFaceStrandSeed edges where
  root := component.root
  root_mem := by
    apply List.mem_eraseDups.mp
    exact (graphComponents_covers
      (slabFaceStrandAdjacentB edges)
      (slabFaceStrandDistinctVertices edges) component.root).2
        ⟨component.1, component.2, component.root_mem⟩

/-- In a duplicate-free component family, the first component containing a
displayed root is the displayed component itself. -/
theorem firstContaining_eq_canonicalComponent
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    (component : SlabFaceStrandCanonicalComponent edges) :
    firstContaining component.root
      (slabFaceStrandCanonicalComponents edges) = component.1 := by
  let selected := firstContaining component.root
    (slabFaceStrandCanonicalComponents edges)
  have hexists : ∃ candidate,
      candidate ∈ slabFaceStrandCanonicalComponents edges ∧
        component.root ∈ candidate :=
    ⟨component.1, component.2, component.root_mem⟩
  have hselectedMem : selected ∈ slabFaceStrandCanonicalComponents edges :=
    firstContaining_mem component.root hexists
  have hrootSelected : component.root ∈ selected :=
    root_mem_firstContaining component.root hexists
  by_cases heq : selected = component.1
  · exact heq
  · have hdisjoint :=
      slabFaceStrandCanonicalComponents_distinctDisjoint edges
        selected hselectedMem component.1 component.2 heq
    exact False.elim (hdisjoint component.root hrootSelected component.root_mem)

/-- The deduplicated rooted component is exactly the selected canonical
component, up to the rooted compiler's final duplicate erasure. -/
theorem distinctRootComponent_eq_canonicalComponent_eraseDups
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    (component : SlabFaceStrandCanonicalComponent edges) :
    rootComponent (slabFaceStrandAdjacentB edges)
        (slabFaceStrandDistinctVertices edges) component.root =
      component.1.eraseDups := by
  unfold rootComponent
  change
    (firstContaining component.root
      (slabFaceStrandCanonicalComponents edges)).eraseDups =
        component.1.eraseDups
  rw [firstContaining_eq_canonicalComponent component]

/-- The accepted raw-list rooted seed has exactly the support of its
canonical component. -/
theorem SlabFaceStrandCanonicalComponent.mem_seed_component_iff
    {physical : SlabLabelling} {edges : List (SlabFaceStrandEdge physical)}
    (component : SlabFaceStrandCanonicalComponent edges)
    (copy : SlabFaceStrandCopy physical) :
    copy ∈ component.seed.component ↔ copy ∈ component.1 := by
  change copy ∈ rootComponent (slabFaceStrandAdjacentB edges)
      (slabFaceStrandVertices edges) component.root ↔ copy ∈ component.1
  have hroot : component.root ∈ slabFaceStrandVertices edges :=
    component.seed.root_mem
  constructor
  · intro hcopy
    have hdistinct :=
      (mem_rawRootComponent_iff_mem_distinctRootComponent hroot).1 hcopy
    rw [distinctRootComponent_eq_canonicalComponent_eraseDups component,
      List.mem_eraseDups] at hdistinct
    exact hdistinct
  · intro hcopy
    apply (mem_rawRootComponent_iff_mem_distinctRootComponent hroot).2
    rw [distinctRootComponent_eq_canonicalComponent_eraseDups component,
      List.mem_eraseDups]
    exact hcopy

/-! ## 4. Exhaustive exterior/core classification and the emitted anchors -/

/-- Apply the executable exterior/core classification to the canonical root
of one actual graph component. -/
def SlabFaceStrandCanonicalComponent.classification
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (component : SlabFaceStrandCanonicalComponent
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment))
    (threshold : Nat) :
    SlabComponentExteriorOrCoreAnchor component.seed threshold :=
  SlabFusionWitnessFaceStrandSeed.exteriorOrCoreAnchor
    component.seed threshold

/-- Emit the decoded low-spin anchor exactly in the blocked branch. -/
def SlabFaceStrandCanonicalComponent.coreAnchor?
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (threshold : Nat)
    (component : SlabFaceStrandCanonicalComponent
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment)) :
    Option (SlabFaceStrandCopy physical) :=
  match component.classification threshold with
  | .exterior _ => none
  | .core anchor => some anchor.copy

/-- A successful anchor emission retains the complete decoded core-anchor
record together with the equality identifying its copy with the output. -/
def SlabFaceStrandCanonicalComponent.coreAnchorWitnessOfSome
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat}
    (component : SlabFaceStrandCanonicalComponent
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment))
    (copy : SlabFaceStrandCopy physical)
    (hsome : component.coreAnchor? threshold = some copy) :
    Σ' anchor : SlabComponentCoreAnchor component.seed threshold,
      anchor.copy = copy := by
  cases hclass : component.classification threshold with
  | exterior reserve_paid =>
      unfold SlabFaceStrandCanonicalComponent.coreAnchor? at hsome
      rw [hclass] at hsome
      cases hsome
  | core anchor =>
      unfold SlabFaceStrandCanonicalComponent.coreAnchor? at hsome
      rw [hclass] at hsome
      simp only [Option.some.injEq] at hsome
      exact ⟨anchor, hsome⟩

/-- The complete list containing one anchor copy for every blocked canonical
component and no entry for an exterior component. -/
def slabCanonicalCoreAnchorCopies
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) : List (SlabFaceStrandCopy physical) :=
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  (slabFaceStrandCanonicalComponents edges).attach.filterMap
    (SlabFaceStrandCanonicalComponent.coreAnchor? threshold)

/-! ## 5. Distinct components emit distinct anchors -/

private theorem nodup_of_map_nodup {A B : Type} (map : A -> B) :
    ∀ {items : List A}, (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup map hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

private theorem attach_nodup_of_nodup {A : Type}
    (items : List A) (hnodup : items.Nodup) : items.attach.Nodup := by
  apply nodup_of_map_nodup Subtype.val
  rw [List.attach_map_subtype_val]
  exact hnodup

private theorem filterMap_nodup_of_separated
    {A B : Type} (emit : A -> Option B) :
    ∀ items : List A, items.Nodup ->
      (∀ left, left ∈ items -> ∀ right, right ∈ items ->
        left ≠ right -> ∀ value,
          emit left = some value -> emit right = some value -> False) ->
      (items.filterMap emit).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hseparated => by
      have hparts := List.nodup_cons.mp hnodup
      have htail := filterMap_nodup_of_separated emit tail hparts.2
        (fun left hleft right hright hne value hleftSome hrightSome =>
          hseparated left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) hne
            value hleftSome hrightSome)
      cases hemit : emit head with
      | none =>
          simp only [List.filterMap_cons, hemit]
          exact htail
      | some value =>
          simp only [List.filterMap_cons, hemit]
          apply List.nodup_cons.mpr
          refine ⟨?_, htail⟩
          intro hmem
          obtain ⟨right, hright, hrightSome⟩ := List.mem_filterMap.mp hmem
          exact hseparated head List.mem_cons_self right
            (List.mem_cons_of_mem head hright)
            (fun heq => hparts.1 (heq ▸ hright))
            value hemit hrightSome

/-- The canonical core-anchor list is duplicate-free: two equal emitted
copies would belong to two disjoint canonical components. -/
theorem slabCanonicalCoreAnchorCopies_nodup
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) :
    (slabCanonicalCoreAnchorCopies K extent physical links assignment
      hassignment threshold).Nodup := by
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  let components := slabFaceStrandCanonicalComponents edges
  unfold slabCanonicalCoreAnchorCopies
  apply filterMap_nodup_of_separated
  · exact attach_nodup_of_nodup components
      (slabFaceStrandCanonicalComponents_nodup edges)
  · intro left hleft right hright hne copy hleftSome hrightSome
    have hleftValueNe : left.1 ≠ right.1 := by
      intro hvalue
      exact hne (Subtype.ext hvalue)
    let hleftWitness := left.coreAnchorWitnessOfSome copy hleftSome
    let hrightWitness := right.coreAnchorWitnessOfSome copy hrightSome
    have hleftCopy := hleftWitness.2
    have hrightCopy := hrightWitness.2
    have hleftMemSeed : copy ∈ left.seed.component := by
      rw [← hleftCopy]
      have hselected := hleftWitness.1.selected_true
      unfold SlabFaceStrandSeed.selected at hselected
      exact of_decide_eq_true hselected
    have hrightMemSeed : copy ∈ right.seed.component := by
      rw [← hrightCopy]
      have hselected := hrightWitness.1.selected_true
      unfold SlabFaceStrandSeed.selected at hselected
      exact of_decide_eq_true hselected
    have hleftMem : copy ∈ left.1 :=
      (left.mem_seed_component_iff copy).1 hleftMemSeed
    have hrightMem : copy ∈ right.1 :=
      (right.mem_seed_component_iff copy).1 hrightMemSeed
    have hdisjoint :=
      slabFaceStrandCanonicalComponents_distinctDisjoint edges
        left.1 left.2 right.1 right.2 hleftValueNe
    exact hdisjoint copy hleftMem hrightMem

/-! ## 6. Canonical finite-core packing -/

/-- Every emitted canonical anchor lies in the explicit finite core carrier. -/
theorem slabCanonicalCoreAnchorCopies_mem_finiteCore
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat} {copy : SlabFaceStrandCopy physical}
    (hcopy : copy ∈ slabCanonicalCoreAnchorCopies
      K extent physical links assignment hassignment threshold) :
    copy ∈ slabFiniteCoreFaceStrandCopies extent physical threshold := by
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  unfold slabCanonicalCoreAnchorCopies at hcopy
  obtain ⟨component, hcomponent, hsome⟩ := List.mem_filterMap.mp hcopy
  let anchorWitness := component.coreAnchorWitnessOfSome copy hsome
  have hanchorCopy := anchorWitness.2
  unfold slabFiniteCoreFaceStrandCopies
  apply List.mem_flatMap.mpr
  refine ⟨copy.faceId, ?_, ?_⟩
  · rw [← hanchorCopy]
    exact anchorWitness.1.face_physical
  · apply mem_faceCoreStrandCopiesAt_of_slot_lt
    rw [← hanchorCopy]
    exact anchorWitness.1.slot_core

/-- The exhaustive canonical core-component count is bounded by the literal
finite low-spin carrier. -/
theorem slabCanonicalCoreAnchorCopies_length_le_finiteCore
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) :
    (slabCanonicalCoreAnchorCopies K extent physical links assignment
      hassignment threshold).length <=
      (slabFiniteCoreFaceStrandCopies extent physical threshold).length :=
  CayleyPruferInjection.nodup_subset_length_le
    (slabCanonicalCoreAnchorCopies K extent physical links assignment
      hassignment threshold)
    (slabFiniteCoreFaceStrandCopies extent physical threshold)
    (slabCanonicalCoreAnchorCopies_nodup K extent physical links assignment
      hassignment threshold)
    (fun _ hcopy => slabCanonicalCoreAnchorCopies_mem_finiteCore hcopy)

/-- Final canonical packing bound: the complete number of blocked components
is at most `threshold` per physical face. -/
theorem slabCanonicalCoreAnchorCopies_length_le_faces_mul_threshold
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) :
    (slabCanonicalCoreAnchorCopies K extent physical links assignment
      hassignment threshold).length <=
      (slabPhysicalFaceEdges extent).length * threshold :=
  Nat.le_trans
    (slabCanonicalCoreAnchorCopies_length_le_finiteCore
      K extent physical links assignment hassignment threshold)
    (slabFiniteCoreFaceStrandCopies_length_le extent physical threshold)

#print axioms slabFaceStrandDistinctVertices
#print axioms slabFaceStrandCanonicalComponents
#print axioms slabFaceStrandCanonicalComponents_nodup
#print axioms slabFaceStrandCanonicalComponents_distinctDisjoint
#print axioms rawToDistinctRootedHom
#print axioms distinctToRawRootedHom
#print axioms mem_rawRootComponent_iff_mem_distinctRootComponent
#print axioms SlabFaceStrandCanonicalComponent.root
#print axioms SlabFaceStrandCanonicalComponent.seed
#print axioms firstContaining_eq_canonicalComponent
#print axioms distinctRootComponent_eq_canonicalComponent_eraseDups
#print axioms SlabFaceStrandCanonicalComponent.mem_seed_component_iff
#print axioms SlabFaceStrandCanonicalComponent.classification
#print axioms SlabFaceStrandCanonicalComponent.coreAnchor?
#print axioms SlabFaceStrandCanonicalComponent.coreAnchorWitnessOfSome
#print axioms slabCanonicalCoreAnchorCopies
#print axioms slabCanonicalCoreAnchorCopies_nodup
#print axioms slabCanonicalCoreAnchorCopies_mem_finiteCore
#print axioms slabCanonicalCoreAnchorCopies_length_le_finiteCore
#print axioms slabCanonicalCoreAnchorCopies_length_le_faces_mul_threshold

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily
