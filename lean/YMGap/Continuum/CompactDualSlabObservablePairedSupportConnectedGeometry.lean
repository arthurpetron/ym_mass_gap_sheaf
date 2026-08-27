/-
# Geometry of the paired physical-support residue

The exact fractional contraction leaves pairs for which the root and target
faces lie in one component of the union of the two physical plaquette
supports.  This module contracts that Boolean condition to a genuine
four-dimensional lattice animal.

A true support adjacency returns the actual slab link shared by its two
faces.  Component paths therefore project to genuine Z4 plaquette paths.
After deduplication, the target-rooted support component is a finite lattice
animal containing both observable plaquettes, so its size is at least their
L-infinity separation plus one.

No weight estimate is asserted here.  The result is the geometric floor
needed by the next paired-support entropy/activity argument.

Constructive contract: finite Boolean graph paths, explicit shared links,
and genuine Z4 lattice animals only; no choice, `Classical`, `sorry`, or
new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry

set_option autoImplicit false

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Decode physical support adjacency to a shared link -/

/-- A true listed-link test constructively returns its first witnessing link
and both literal incidence proofs. -/
def slabShareListedLinkWitness
    {extent left right : Nat} :
    ∀ (links : List SlabLink),
      slabShareListedLinkB extent left right links = true →
        Sigma fun link : SlabLink =>
          (link ∈ links) ×'
            (left ∈ slabIncidentPlaqIds extent link) ×'
              (right ∈ slabIncidentPlaqIds extent link)
  | [], hadj => by cases hadj
  | link :: links, hadj => by
      by_cases hleft : left ∈ slabIncidentPlaqIds extent link
      · by_cases hright : right ∈ slabIncidentPlaqIds extent link
        · exact ⟨link, List.mem_cons_self, hleft, hright⟩
        · have htail :
              slabShareListedLinkB extent left right links = true := by
            simpa [slabShareListedLinkB, hleft, hright] using hadj
          obtain ⟨found, hfound, hfoundLeft, hfoundRight⟩ :=
            slabShareListedLinkWitness links htail
          exact ⟨found, List.mem_cons_of_mem link hfound,
            hfoundLeft, hfoundRight⟩
      · have htail :
            slabShareListedLinkB extent left right links = true := by
          simpa [slabShareListedLinkB, hleft] using hadj
        obtain ⟨found, hfound, hfoundLeft, hfoundRight⟩ :=
          slabShareListedLinkWitness links htail
        exact ⟨found, List.mem_cons_of_mem link hfound,
          hfoundLeft, hfoundRight⟩

/-- Every true physical support adjacency is a genuine adjacency of the two
decoded Z4 plaquettes, witnessed by the same displayed slab link. -/
def slabSupportFaceAdjacentToPlaquetteAdjacent
    {extent left right : Nat}
    (hadj : slabSupportFaceAdjacentB extent left right = true) :
    z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent left)
      (slabPlaquetteAt extent right) := by
  obtain ⟨link, _, hleft, hright⟩ :=
    slabShareListedLinkWitness
      (boundaryCompleteSlabLinks extent) hadj
  refine { link := link, on_p := ?_, on_q := ?_ }
  · change decide
      (link ∈ edgesOf (slabPlaquetteAt extent left)) = true
    exact decide_eq_true_eq.mpr
      (link_mem_edgesOf_slabPlaquetteAt_of_mem_incident hleft)
  · change decide
      (link ∈ edgesOf (slabPlaquetteAt extent right)) = true
    exact decide_eq_true_eq.mpr
      (link_mem_edgesOf_slabPlaquetteAt_of_mem_incident hright)

/-! ## 2. The deduplicated geometric support component -/

/-- The genuine plaquettes underlying the target-rooted union-support
component of one observable pair. -/
def slabObservableTwoReplicaPairTargetSupportPlaquettes
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : List Z4Plaq :=
  ((slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId).map
        (slabPlaquetteAt D.extent)).eraseDups

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool, (items.filter predicate).eraseDups.Nodup := by
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

private theorem filterTrueLocal {A : Type} :
    ∀ items : List A, items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

theorem slabObservableTwoReplicaPairTargetSupportPlaquettes_nodup
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) :
    (slabObservableTwoReplicaPairTargetSupportPlaquettes
      D pair targetFaceId).Nodup := by
  unfold slabObservableTwoReplicaPairTargetSupportPlaquettes
  exact eraseDupsNodupLocal _

theorem slabPlaquetteAt_mem_twoReplicaPairTargetSupportPlaquettes
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId) :
    slabPlaquetteAt D.extent faceId ∈
      slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId := by
  unfold slabObservableTwoReplicaPairTargetSupportPlaquettes
  exact List.mem_eraseDups.mpr
    (List.mem_map.mpr ⟨faceId, hface, rfl⟩)

/-- The target face belongs to its own rooted union-support component for
every source four-cell pair. -/
theorem slabObservableTwoReplicaPairTarget_mem_targetSupportComponent
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    targetFaceId ∈ slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId := by
  unfold slabTwoReplicaTargetSupportComponent
  apply root_mem_rootComponent
  apply mem_slabTwoReplicaSupportFaceVertices htarget
  exact Or.inl
    (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
      D rootFaceId targetFaceId pair hpair)

/-- The first component face above a requested geometric plaquette, with the
target face as an explicit total fallback. -/
def slabObservableTwoReplicaPairTargetSupportFaceValue
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) (plaquette : Z4Plaq) : Nat :=
  listFirstMappedPreimageOr
    (slabPlaquetteAt D.extent) targetFaceId plaquette
    (slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)

theorem slabObservableTwoReplicaPairTargetSupportFaceValue_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (plaquette : Z4Plaq) :
    slabObservableTwoReplicaPairTargetSupportFaceValue
        D pair targetFaceId plaquette ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId := by
  rcases listFirstMappedPreimageOr_mem_or_eq_fallback
      (slabPlaquetteAt D.extent) targetFaceId plaquette
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId) with hmem | hfallback
  · exact hmem
  · unfold slabObservableTwoReplicaPairTargetSupportFaceValue
    rw [hfallback]
    exact slabObservableTwoReplicaPairTarget_mem_targetSupportComponent
      D rootFaceId targetFaceId htarget pair hpair

theorem slabObservableTwoReplicaPairTargetSupportFaceValue_projection
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈
      slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId) :
    slabPlaquetteAt D.extent
        (slabObservableTwoReplicaPairTargetSupportFaceValue
          D pair targetFaceId plaquette) = plaquette := by
  exact listFirstMappedPreimageOr_projection
    (slabPlaquetteAt D.extent) targetFaceId plaquette
    (slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)
    (List.mem_eraseDups.mp hplaquette)

/-! ## 3. Project component paths to genuine plaquette paths -/

def slabTwoReplicaTargetSupportChainToPlaquetteChain
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) :
    {left right : Nat} →
      FiniteBoolGraphComponents.ChainIn
        (slabSupportFaceAdjacentB D.extent)
        (slabTwoReplicaTargetSupportComponent D.extent
          pair.1.1.1 pair.2.1.1 targetFaceId)
        left right →
      PolymerModel.ChainIn z4Chain.toLattice
        (slabObservableTwoReplicaPairTargetSupportPlaquettes
          D pair targetFaceId)
        (slabPlaquetteAt D.extent left)
        (slabPlaquetteAt D.extent right)
  | _, _, FiniteBoolGraphComponents.ChainIn.refl face =>
      PolymerModel.ChainIn.refl _
  | _left, _right,
      FiniteBoolGraphComponents.ChainIn.step
        (b := next) hadj hnext rest =>
      PolymerModel.ChainIn.step
        (slabSupportFaceAdjacentToPlaquetteAdjacent hadj)
        (slabPlaquetteAt_mem_twoReplicaPairTargetSupportPlaquettes
          D pair targetFaceId next hnext)
        (slabTwoReplicaTargetSupportChainToPlaquetteChain
          D pair targetFaceId rest)

/-- The deduplicated target-rooted union-support component is internally
connected in the genuine Z4 plaquette lattice. -/
def slabObservableTwoReplicaPairTargetSupportPlaquettes_connected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId) := by
  intro leftPlaquette rightPlaquette hleft hright
  let left := slabObservableTwoReplicaPairTargetSupportFaceValue
    D pair targetFaceId leftPlaquette
  let right := slabObservableTwoReplicaPairTargetSupportFaceValue
    D pair targetFaceId rightPlaquette
  have hleftComponent : left ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId :=
    slabObservableTwoReplicaPairTargetSupportFaceValue_mem
      D rootFaceId targetFaceId htarget pair hpair leftPlaquette
  have hrightComponent : right ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId :=
    slabObservableTwoReplicaPairTargetSupportFaceValue_mem
      D rootFaceId targetFaceId htarget pair hpair rightPlaquette
  have htargetVertex :
      targetFaceId ∈ slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1 := by
    apply mem_slabTwoReplicaSupportFaceVertices htarget
    exact Or.inl
      (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
        D rootFaceId targetFaceId pair hpair)
  have hfaces := rootComponent_connected
    (slabSupportFaceAdjacentB D.extent)
    (slabSupportFaceAdjacentB_symmetric D.extent)
    htargetVertex left right hleftComponent hrightComponent
  have hprojected :=
    slabTwoReplicaTargetSupportChainToPlaquetteChain
      D pair targetFaceId hfaces
  have hleftEq : slabPlaquetteAt D.extent left = leftPlaquette := by
    exact slabObservableTwoReplicaPairTargetSupportFaceValue_projection
      D pair targetFaceId leftPlaquette hleft
  have hrightEq : slabPlaquetteAt D.extent right = rightPlaquette := by
    exact slabObservableTwoReplicaPairTargetSupportFaceValue_projection
      D pair targetFaceId rightPlaquette hright
  rw [hleftEq, hrightEq] at hprojected
  exact hprojected

/-! ## 4. Root/target membership and the separation floor -/

theorem slabObservableTwoReplicaPairTargetPlaquette_mem_targetSupport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabPlaquetteAt D.extent targetFaceId ∈
      slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  exact ⟨targetFaceId,
    slabObservableTwoReplicaPairTarget_mem_targetSupportComponent
      D rootFaceId targetFaceId htarget pair hpair,
    rfl⟩

theorem slabObservableTwoReplicaPairRootPlaquette_mem_targetSupport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair = true) :
    slabPlaquetteAt D.extent rootFaceId ∈
      slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId := by
  have hroot : rootFaceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId := by
    exact of_decide_eq_true hconnected
  exact List.mem_eraseDups.mpr
    (List.mem_map.mpr ⟨rootFaceId, hroot, rfl⟩)

/-- The geometric support component is a genuine finite Z4 lattice animal
rooted at the target plaquette. -/
theorem slabObservableTwoReplicaPairTargetSupportAnimal
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    IsClusterThroughIn z4Chain
      (slabPlaquetteAt D.extent targetFaceId)
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId).length
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId) := by
  exact ⟨rfl,
    slabObservableTwoReplicaPairTargetPlaquette_mem_targetSupport
      D rootFaceId targetFaceId htarget pair hpair,
    slabObservableTwoReplicaPairTargetSupportPlaquettes_nodup
      D pair targetFaceId,
    ⟨slabObservableTwoReplicaPairTargetSupportPlaquettes_connected
      D rootFaceId targetFaceId htarget pair hpair⟩⟩

private theorem natDist_comm (left right : Nat) :
    natDist left right = natDist right left := by
  unfold natDist
  omega

private theorem linfDist_comm (left right : Z4Plaq) :
    linfDist left right = linfDist right left := by
  unfold linfDist
  rw [natDist_comm (cPlaq left Dir4.x0) (cPlaq right Dir4.x0),
    natDist_comm (cPlaq left Dir4.x1) (cPlaq right Dir4.x1),
    natDist_comm (cPlaq left Dir4.x2) (cPlaq right Dir4.x2),
    natDist_comm (cPlaq left Dir4.x3) (cPlaq right Dir4.x3)]

/-- **Paired-support geometric floor.**  A pair in the exact connected
residue carries at least one distinct union-support plaquette for every unit
of root-to-target L-infinity separation, including the initial plaquette. -/
theorem slabObservableTwoReplicaPairPairedSupportConnected_size_floor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair = true) :
    linfDist
          (slabPlaquetteAt D.extent rootFaceId)
          (slabPlaquetteAt D.extent targetFaceId) + 1 ≤
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId).length := by
  let support := slabObservableTwoReplicaPairTargetSupportPlaquettes
    D pair targetFaceId
  obtain ⟨animal, hanimal, hsame⟩ :=
    (z4ClusterCountBound_animal
      (slabPlaquetteAt D.extent targetFaceId)).2
      support.length support
      (slabObservableTwoReplicaPairTargetSupportAnimal
        D rootFaceId targetFaceId htarget pair hpair)
  have hrootSupport :
      slabPlaquetteAt D.extent rootFaceId ∈ support :=
    slabObservableTwoReplicaPairRootPlaquette_mem_targetSupport
      D rootFaceId targetFaceId pair hconnected
  have hrootAnimal :
      slabPlaquetteAt D.extent rootFaceId ∈ animal :=
    hsame.1 _ hrootSupport
  have hfloor := enum_linf_reach_floor
    (slabPlaquetteAt D.extent targetFaceId)
    support.length animal hanimal
    (slabPlaquetteAt D.extent rootFaceId) hrootAnimal
    (linfDist
      (slabPlaquetteAt D.extent targetFaceId)
      (slabPlaquetteAt D.extent rootFaceId))
    (Nat.le_refl _)
  have hsupportNodup : support.Nodup :=
    slabObservableTwoReplicaPairTargetSupportPlaquettes_nodup
      D pair targetFaceId
  have hanimalNodup : animal.Nodup :=
    enumPoly_nodup z4Chain
      (slabPlaquetteAt D.extent targetFaceId)
      support.length hanimal
  have hlength : animal.length = support.length :=
    (sameSupport_length_eq_of_nodup
      hsame hsupportNodup hanimalNodup).symm
  rw [hlength] at hfloor
  rw [linfDist_comm
    (slabPlaquetteAt D.extent targetFaceId)
    (slabPlaquetteAt D.extent rootFaceId)] at hfloor
  exact hfloor

end YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry.slabShareListedLinkWitness
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry.slabSupportFaceAdjacentToPlaquetteAdjacent
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry.slabObservableTwoReplicaPairTargetSupportPlaquettes_connected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry.slabObservableTwoReplicaPairTargetSupportAnimal
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry.slabObservableTwoReplicaPairPairedSupportConnected_size_floor
