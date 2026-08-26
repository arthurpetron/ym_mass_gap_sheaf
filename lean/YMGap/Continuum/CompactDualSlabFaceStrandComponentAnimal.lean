/-
# A rooted face-strand component projects to a genuine Z4 lattice animal

The inverse component code still contains ambient slab face identifiers.  The
volume-independent replacement begins with the geometric support underlying
those identifiers.  This module maps every selected face-strand copy to its
literal corrected-slab plaquette, removes duplicate plaquettes, and proves
that the resulting list is a genuine internally connected Z4 lattice animal
through the root plaquette.

The load-bearing step is a Type-valued projection of paths.  A Boolean strand
adjacency is decoded to the literal global strand edge which realizes it.
Membership of that edge in the assignment graph recovers its displayed link
and the two incident slab faces.  The same link is therefore a witness of Z4
plaquette adjacency.  Structural recursion maps the complete strand path to a
plaquette path internal to the deduplicated geometric support.

Constructive contract: finite list recursion, decidable equality, and literal
lattice-incidence witnesses only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
import YMGap.Continuum.AdjSpanningBuild

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal

set_option autoImplicit false

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Decode Boolean strand adjacency to a literal edge -/

/-- A true one-edge connection records one of the two literal orientations. -/
def slabFaceStrandEdgeConnectsWitness
    {physical : SlabLabelling} (edge : SlabFaceStrandEdge physical)
    (left right : SlabFaceStrandCopy physical)
    (hconnect : slabFaceStrandEdgeConnectsB edge left right = true) :
    ((edge.source = left) ×' (edge.target = right)) ⊕'
      ((edge.source = right) ×' (edge.target = left)) := by
  by_cases hsource : edge.source = left
  · by_cases htarget : edge.target = right
    · exact PSum.inl ⟨hsource, htarget⟩
    · have hreverse : edge.source = right ∧ edge.target = left := by
        simpa [slabFaceStrandEdgeConnectsB, hsource, htarget] using hconnect
      exact PSum.inr ⟨hreverse.1, hreverse.2⟩
  · have hreverse : edge.source = right ∧ edge.target = left := by
      simpa [slabFaceStrandEdgeConnectsB, hsource] using hconnect
    exact PSum.inr ⟨hreverse.1, hreverse.2⟩

/-- A true adjacency in a finite strand graph constructively returns the
literal edge and its orientation. -/
def slabFaceStrandAdjacentEdgeWitness
    {physical : SlabLabelling}
    (left right : SlabFaceStrandCopy physical) :
    forall edges : List (SlabFaceStrandEdge physical),
      slabFaceStrandAdjacentB edges left right = true ->
      Sigma fun edge : SlabFaceStrandEdge physical =>
        (edge ∈ edges) ×'
          (((edge.source = left) ×' (edge.target = right)) ⊕'
            ((edge.source = right) ×' (edge.target = left)))
  | [], hadj => by cases hadj
  | edge :: edges, hadj => by
      by_cases hhead : slabFaceStrandEdgeConnectsB edge left right = true
      · exact ⟨edge, List.mem_cons_self,
          slabFaceStrandEdgeConnectsWitness edge left right hhead⟩
      · have htail : slabFaceStrandAdjacentB edges left right = true := by
          simpa [slabFaceStrandAdjacentB, hhead] using hadj
        obtain ⟨found, hfound, horientation⟩ :=
          slabFaceStrandAdjacentEdgeWitness left right edges htail
        exact ⟨found, List.mem_cons_of_mem edge hfound, horientation⟩

/-! ## 2. Certified geometric assignment edges -/

/-- The edge of one physical terminal pair is a genuine adjacency of its two
decoded slab plaquettes, witnessed by the displayed link itself. -/
def slabLinkFaceStrandEdgeOfTerminalAdjacent
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent
        (slabLinkFaceStrandEdgeOfTerminal
          K extent physical link auxiliary hmem terminal).source.faceId)
      (slabPlaquetteAt extent
        (slabLinkFaceStrandEdgeOfTerminal
          K extent physical link auxiliary hmem terminal).target.faceId) := by
  refine { link := link, on_p := ?_, on_q := ?_ }
  · change decide
      (link ∈ edgesOf
        (slabPlaquetteAt extent
          (slabLinkPhysicalTerminalFaceStrandCopy
            K extent physical link auxiliary hmem terminal).faceId)) = true
    apply decide_eq_true_eq.mpr
    apply link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
    rw [slabLinkPhysicalTerminalFaceStrandCopy_faceId]
    exact List.get_mem _ _
  · change decide
      (link ∈ edgesOf
        (slabPlaquetteAt extent
          (slabLinkPhysicalTerminalFaceStrandCopy
            K extent physical link auxiliary hmem
              (slabLinkPhysicalStrandPartner
                K extent physical link auxiliary hmem terminal)).faceId)) = true
    apply decide_eq_true_eq.mpr
    apply link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
    rw [slabLinkPhysicalTerminalFaceStrandCopy_faceId]
    exact List.get_mem _ _

/-- A strand edge paired with its genuine geometric adjacency witness. -/
structure SlabGeometricFaceStrandEdge
    (extent : Nat) (physical : SlabLabelling) : Type where
  edge : SlabFaceStrandEdge physical
  adjacent : z4Chain.toLattice.Adjacent
    (slabPlaquetteAt extent edge.source.faceId)
    (slabPlaquetteAt extent edge.target.faceId)

/-- All certified geometric strand edges contributed by one accepted link. -/
def slabLinkGeometricFaceStrandEdges
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    List (SlabGeometricFaceStrandEdge extent physical) :=
  (slabLinkPhysicalStrandTerminals
    K extent physical link auxiliary hmem).map fun terminal =>
      { edge := slabLinkFaceStrandEdgeOfTerminal
          K extent physical link auxiliary hmem terminal
        adjacent := slabLinkFaceStrandEdgeOfTerminalAdjacent
          K extent physical link auxiliary hmem terminal }

/-- Forgetting the geometric witnesses from one accepted link recovers its
literal strand-edge list. -/
theorem slabLinkGeometricFaceStrandEdges_map_edge
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    (slabLinkGeometricFaceStrandEdges
      K extent physical link auxiliary hmem).map
        SlabGeometricFaceStrandEdge.edge =
      slabLinkFaceStrandEdges K extent physical link auxiliary hmem := by
  unfold slabLinkGeometricFaceStrandEdges slabLinkFaceStrandEdges
  rw [List.map_map]
  apply List.map_congr_left
  intro terminal _
  rfl

/-- The certified geometric strand edges contributed by one link of a complete
assignment.  Factoring the dependent local lookup out of the outer
concatenation keeps reduction of the complete list within the project heartbeat
budget. -/
def slabFusionWitnessAssignmentGeometricFaceStrandEdgesAt
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (linked : {link // link ∈ links}) :
    List (SlabGeometricFaceStrandEdge extent physical) :=
  let auxiliary := slabFusionWitnessAssignmentAt linked.1 assignment
  let hmem := slabFusionWitnessAssignmentAt_mem_local
    K extent physical links assignment hassignment linked.1 linked.2
  slabLinkGeometricFaceStrandEdges
    K extent physical linked.1 auxiliary hmem

/-- The complete assignment graph with genuine plaquette adjacency retained as
Type-level data on every edge. -/
def slabFusionWitnessAssignmentGeometricFaceStrandEdges
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links) :
    List (SlabGeometricFaceStrandEdge extent physical) :=
  links.attach.flatMap
    (slabFusionWitnessAssignmentGeometricFaceStrandEdgesAt
      K extent physical links assignment hassignment)

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

/-- Forgetting the geometric witnesses recovers the literal global strand
edge list exactly. -/
theorem slabFusionWitnessAssignmentGeometricFaceStrandEdges_map_edge
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links) :
    (slabFusionWitnessAssignmentGeometricFaceStrandEdges
      K extent physical links assignment hassignment).map
        SlabGeometricFaceStrandEdge.edge =
      slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment := by
  unfold slabFusionWitnessAssignmentGeometricFaceStrandEdges
    slabFusionWitnessAssignmentGeometricFaceStrandEdgesAt
    slabFusionWitnessAssignmentFaceStrandEdges
    slabFusionWitnessAssignmentFaceStrandEdgesAt
  rw [List.map_flatMap]
  apply flatMapCongrLeftLocal
  intro linked _
  exact slabLinkGeometricFaceStrandEdges_map_edge
    K extent physical linked.1
      (slabFusionWitnessAssignmentAt linked.1 assignment) _

/-- A true adjacency in a certified edge list returns the genuine plaquette
adjacency carried by the first matching edge. -/
def slabGeometricFaceStrandAdjacentWitness
    {extent : Nat} {physical : SlabLabelling}
    (left right : SlabFaceStrandCopy physical) :
    forall edges : List (SlabGeometricFaceStrandEdge extent physical),
      slabFaceStrandAdjacentB
        (edges.map SlabGeometricFaceStrandEdge.edge) left right = true ->
      z4Chain.toLattice.Adjacent
        (slabPlaquetteAt extent left.faceId)
        (slabPlaquetteAt extent right.faceId)
  | [], hadj => by cases hadj
  | edge :: edges, hadj => by
      by_cases hhead :
          slabFaceStrandEdgeConnectsB edge.edge left right = true
      · have horientation :=
          slabFaceStrandEdgeConnectsWitness edge.edge left right hhead
        cases horientation with
        | inl hforward =>
            rw [← hforward.1, ← hforward.2]
            exact edge.adjacent
        | inr hreverse =>
            rw [← hreverse.2, ← hreverse.1]
            exact adjacentSymm edge.adjacent
      · have htail : slabFaceStrandAdjacentB
            (edges.map SlabGeometricFaceStrandEdge.edge) left right = true := by
          simpa [slabFaceStrandAdjacentB, hhead] using hadj
        exact slabGeometricFaceStrandAdjacentWitness left right edges htail

/-- Every true strand adjacency in the complete assignment graph projects to
a genuine Z4 plaquette adjacency. -/
def slabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (left right : SlabFaceStrandCopy physical)
    (hadj : slabFaceStrandAdjacentB
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment)
      left right = true) :
    z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent left.faceId)
      (slabPlaquetteAt extent right.faceId) := by
  rw [← slabFusionWitnessAssignmentGeometricFaceStrandEdges_map_edge
    K extent physical links assignment hassignment] at hadj
  exact slabGeometricFaceStrandAdjacentWitness left right
    (slabFusionWitnessAssignmentGeometricFaceStrandEdges
      K extent physical links assignment hassignment) hadj

/-! ## 3. Deduplicated geometric plaquette support -/

/-- The literal slab plaquette underlying a physical face-strand copy. -/
def slabFaceStrandCopyPlaquette
    {extent : Nat} {physical : SlabLabelling}
    (copy : SlabFaceStrandCopy physical) : Z4Plaq :=
  slabPlaquetteAt extent copy.faceId

/-- The duplicate-free geometric plaquette support of a rooted strand
component. -/
def componentPlaquetteSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : List Z4Plaq :=
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

/-- Search a finite list for the first source mapped to `target`, using an
explicit fallback if no such source occurs.  The returned data is independent
of any propositional membership proof. -/
def listFirstMappedPreimageOr {A B : Type} [DecidableEq B]
    (projection : A -> B) (fallback : A) (target : B) : List A -> A
  | [] => fallback
  | head :: tail =>
      if projection head = target then head
      else listFirstMappedPreimageOr projection fallback target tail

/-- A finite mapped-preimage search returns either an item of the searched list
or its explicit fallback. -/
theorem listFirstMappedPreimageOr_mem_or_eq_fallback
    {A B : Type} [DecidableEq B]
    (projection : A -> B) (fallback : A) (target : B) :
    forall items : List A,
      listFirstMappedPreimageOr projection fallback target items ∈ items ∨
        listFirstMappedPreimageOr projection fallback target items = fallback
  | [] => Or.inr rfl
  | head :: tail => by
      by_cases hhead : projection head = target
      · simp only [listFirstMappedPreimageOr, hhead, if_true]
        exact Or.inl List.mem_cons_self
      · simp only [listFirstMappedPreimageOr, hhead, if_false]
        rcases listFirstMappedPreimageOr_mem_or_eq_fallback
            projection fallback target tail with hmem | hfallback
        · exact Or.inl (List.mem_cons_of_mem head hmem)
        · exact Or.inr hfallback

/-- If the target occurs in the mapped list, finite search returns a source
which maps to it. -/
theorem listFirstMappedPreimageOr_projection
    {A B : Type} [DecidableEq B]
    (projection : A -> B) (fallback : A) (target : B) :
    forall items : List A, target ∈ items.map projection ->
      projection
        (listFirstMappedPreimageOr projection fallback target items) = target
  | [], hmem => by cases hmem
  | head :: tail, hmem => by
      by_cases hhead : projection head = target
      · simp [listFirstMappedPreimageOr, hhead]
      · have htail : target ∈ tail.map projection := by
          simp only [List.map_cons, List.mem_cons] at hmem
          exact hmem.resolve_left (fun h => hhead h.symm)
        simpa [listFirstMappedPreimageOr, hhead] using
          listFirstMappedPreimageOr_projection
            projection fallback target tail htail

/-- Membership in the geometric support is exactly membership of some
component copy above that plaquette. -/
theorem mem_componentPlaquetteSupport_iff
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq) :
    plaquette ∈ componentPlaquetteSupport seed ↔
      ∃ copy, copy ∈ seed.component ∧
        slabFaceStrandCopyPlaquette (extent := extent) copy = plaquette := by
  simp [componentPlaquetteSupport,
    slabFaceStrandCopyPlaquette]

/-- The first component copy above a requested plaquette, with the component
root as a total fallback. -/
def componentPlaquetteSupportCopyValue
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq) : SlabFaceStrandCopy physical :=
  listFirstMappedPreimageOr
    (slabFaceStrandCopyPlaquette (extent := extent)) seed.root plaquette
      seed.component

/-- The selected copy belongs to the rooted strand component. -/
theorem componentPlaquetteSupportCopyValue_mem
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq) :
    componentPlaquetteSupportCopyValue seed plaquette ∈ seed.component := by
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
        (slabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment hassignment))
      seed.root_mem

/-- For a member of the geometric support, the selected component copy lies
above that exact plaquette. -/
theorem componentPlaquetteSupportCopyValue_projection
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ componentPlaquetteSupport seed) :
    slabFaceStrandCopyPlaquette (extent := extent)
      (componentPlaquetteSupportCopyValue seed plaquette) = plaquette := by
  exact listFirstMappedPreimageOr_projection
    (slabFaceStrandCopyPlaquette (extent := extent)) seed.root plaquette
      seed.component (List.mem_eraseDups.mp hplaquette)

/-- The geometric component support is literally duplicate-free. -/
theorem componentPlaquetteSupport_nodup
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentPlaquetteSupport seed).Nodup := by
  unfold componentPlaquetteSupport
  exact eraseDupsNodupLocal _

/-- The selected strand root projects into the geometric component support. -/
theorem rootPlaquette_mem_componentPlaquetteSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    slabPlaquetteAt extent seed.root.faceId ∈
      componentPlaquetteSupport seed := by
  apply (mem_componentPlaquetteSupport_iff seed _).mpr
  refine ⟨seed.root, ?_, rfl⟩
  unfold SlabFaceStrandSeed.component
  exact root_mem_rootComponent
    (slabFaceStrandAdjacentB
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment))
    seed.root_mem

/-- Every geometric component plaquette lies in the enclosing finite box. -/
theorem componentPlaquetteSupport_subset_box
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq) (hplaquette : plaquette ∈
      componentPlaquetteSupport seed) :
    plaquette ∈ boxPlaquettes (extent + 1) := by
  obtain ⟨copy, hcopy, hcopyEq⟩ :=
    (mem_componentPlaquetteSupport_iff seed plaquette).mp hplaquette
  rw [← hcopyEq]
  exact (mem_boundaryCompleteSlabPlaquettes extent
    (slabPlaquetteAt extent copy.faceId)).mp
      (slabPlaquetteAt_mem
        (SlabFusionWitnessFaceStrandSeed.component_faceId_physical
          seed copy hcopy)) |>.1

/-! ## 4. Project complete strand paths to internal plaquette paths -/

/-- Structural projection of one component-internal strand path to a genuine
plaquette path internal to the deduplicated geometric support. -/
def componentChainToPlaquetteChain
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    {left right : SlabFaceStrandCopy physical} ->
      FiniteBoolGraphComponents.ChainIn
        (slabFaceStrandAdjacentB
          (slabFusionWitnessAssignmentFaceStrandEdges
            K extent physical links assignment hassignment))
        seed.component left right ->
      PolymerModel.ChainIn z4Chain.toLattice
        (componentPlaquetteSupport seed)
        (slabPlaquetteAt extent left.faceId)
        (slabPlaquetteAt extent right.faceId)
  | _, _, FiniteBoolGraphComponents.ChainIn.refl copy =>
      PolymerModel.ChainIn.refl _
  | left, _right,
      FiniteBoolGraphComponents.ChainIn.step
        (b := next) hadj hnext rest =>
      PolymerModel.ChainIn.step
        (slabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
          K extent physical links assignment hassignment left next hadj)
        ((mem_componentPlaquetteSupport_iff seed _).mpr
          ⟨next, hnext, rfl⟩)
        (componentChainToPlaquetteChain seed rest)

/-- **Geometric contraction.**  The duplicate-free plaquette support of every
rooted face-strand component is internally connected in the genuine Z4
plaquette-incidence lattice. -/
def componentPlaquetteSupport_connected
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      (componentPlaquetteSupport seed) := by
  intro leftPlaquette rightPlaquette hleft hright
  let left := componentPlaquetteSupportCopyValue seed leftPlaquette
  let right := componentPlaquetteSupportCopyValue seed rightPlaquette
  have hleftComponent : left ∈ seed.component :=
    componentPlaquetteSupportCopyValue_mem seed leftPlaquette
  have hrightComponent : right ∈ seed.component :=
    componentPlaquetteSupportCopyValue_mem seed rightPlaquette
  have hleftEq : slabPlaquetteAt extent left.faceId = leftPlaquette := by
    simpa [left, slabFaceStrandCopyPlaquette] using
      componentPlaquetteSupportCopyValue_projection seed leftPlaquette hleft
  have hrightEq : slabPlaquetteAt extent right.faceId = rightPlaquette := by
    simpa [right, slabFaceStrandCopyPlaquette] using
      componentPlaquetteSupportCopyValue_projection seed rightPlaquette hright
  have hstrand := rootComponent_connected
    (slabFaceStrandAdjacentB
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment))
    (slabFaceStrandAdjacentB_symmetric
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment))
    seed.root_mem left right hleftComponent hrightComponent
  have hprojected :=
    componentChainToPlaquetteChain seed hstrand
  rw [hleftEq, hrightEq] at hprojected
  exact hprojected

/-! ## 5. The genuine rooted-animal certificate and its size -/

/-- The geometric support, rooted at the selected strand's plaquette, is a
genuine Z4 lattice animal of its literal support size. -/
theorem componentPlaquetteAnimal
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    IsClusterThroughIn z4Chain
      (slabPlaquetteAt extent seed.root.faceId)
      (componentPlaquetteSupport seed).length
      (componentPlaquetteSupport seed) := by
  exact ⟨rfl,
    rootPlaquette_mem_componentPlaquetteSupport seed,
    componentPlaquetteSupport_nodup seed,
    ⟨componentPlaquetteSupport_connected seed⟩⟩

/-- Deduplicating the component's plaquette projection can only decrease its
size, so geometric animal size is bounded by the physical peel length. -/
theorem componentPlaquetteSupport_length_le_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentPlaquetteSupport seed).length <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have hdedup : (componentPlaquetteSupport seed).length <=
      (seed.component.map
        (slabFaceStrandCopyPlaquette (extent := extent))).length := by
    unfold componentPlaquetteSupport
    exact eraseDupsLengthLeLocal _
  rw [List.length_map] at hdedup
  exact Nat.le_trans hdedup
    (SlabFusionWitnessFaceStrandSeed.component_length_le_peelFaces_length seed)

#print axioms slabFaceStrandEdgeConnectsWitness
#print axioms slabFaceStrandAdjacentEdgeWitness
#print axioms slabLinkFaceStrandEdgeOfTerminalAdjacent
#print axioms SlabGeometricFaceStrandEdge
#print axioms slabLinkGeometricFaceStrandEdges
#print axioms slabLinkGeometricFaceStrandEdges_map_edge
#print axioms slabFusionWitnessAssignmentGeometricFaceStrandEdgesAt
#print axioms slabFusionWitnessAssignmentGeometricFaceStrandEdges
#print axioms slabFusionWitnessAssignmentGeometricFaceStrandEdges_map_edge
#print axioms slabGeometricFaceStrandAdjacentWitness
#print axioms slabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
#print axioms slabFaceStrandCopyPlaquette
#print axioms componentPlaquetteSupport
#print axioms listFirstMappedPreimageOr
#print axioms listFirstMappedPreimageOr_mem_or_eq_fallback
#print axioms listFirstMappedPreimageOr_projection
#print axioms mem_componentPlaquetteSupport_iff
#print axioms componentPlaquetteSupportCopyValue
#print axioms componentPlaquetteSupportCopyValue_mem
#print axioms componentPlaquetteSupportCopyValue_projection
#print axioms componentPlaquetteSupport_nodup
#print axioms rootPlaquette_mem_componentPlaquetteSupport
#print axioms componentPlaquetteSupport_subset_box
#print axioms componentChainToPlaquetteChain
#print axioms componentPlaquetteSupport_connected
#print axioms componentPlaquetteAnimal
#print axioms componentPlaquetteSupport_length_le_peelFaces

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
