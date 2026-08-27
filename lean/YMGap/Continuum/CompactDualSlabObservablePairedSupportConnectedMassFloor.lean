/-
# Physical-mass floor for the paired-support connected residue

The geometric residue component contains distinct plaquettes, but the heat
weight is indexed by twice-spin multiplicity.  Every face of the union
support carries at least one unit in one of the two replicas.  Consequently
the component's cardinality is bounded by the total twice-spin mass carried
on it, and that component mass is bounded by the full two-replica physical
mass.

Combining these elementary inequalities with the genuine lattice-animal
floor proves that a connected residue pair pays at least
`L-infinity distance + 1` units in the exponent seen by its face weights.

No entropy or summed Gibbs estimate is asserted here.

Constructive contract: finite natural-number sums and explicit support
membership only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
import YMGap.Continuum.FiniteSimpleWalk

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Mass observables -/

/-- Twice-spin mass carried by the target-rooted union-support component. -/
def slabObservableTwoReplicaPairTargetSupportMass
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : Nat :=
  listNatWeight
    (fun faceId => pair.1.1.1 faceId + pair.2.1.1 faceId)
    (slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)

/-- Complete physical twice-spin mass of both replicas on the slab. -/
def slabObservableTwoReplicaPairTotalPhysicalMass
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : Nat :=
  listNatWeight
    (fun faceId => pair.1.1.1 faceId + pair.2.1.1 faceId)
    (slabPhysicalFaceEdges D.extent)

/-! ## 2. Every retained support face pays one mass unit -/

theorem slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId) :
    faceId ∈ slabPhysicalFaceEdges D.extent := by
  have htargetVertex :
      targetFaceId ∈ slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1 := by
    apply mem_slabTwoReplicaSupportFaceVertices htarget
    exact Or.inl
      (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
        D rootFaceId targetFaceId pair hpair)
  have hvertex := rootComponent_subset
    (slabSupportFaceAdjacentB D.extent) htargetVertex hface
  exact (List.mem_filter.mp hvertex).1

theorem slabObservableTwoReplicaPairTargetSupportComponent_face_positive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId) :
    0 < pair.1.1.1 faceId ∨ 0 < pair.2.1.1 faceId := by
  have htargetVertex :
      targetFaceId ∈ slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1 := by
    apply mem_slabTwoReplicaSupportFaceVertices htarget
    exact Or.inl
      (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
        D rootFaceId targetFaceId pair hpair)
  have hvertex := rootComponent_subset
    (slabSupportFaceAdjacentB D.extent) htargetVertex hface
  have hsupport := (List.mem_filter.mp hvertex).2
  exact of_decide_eq_true hsupport

private theorem list_length_le_listNatWeight_of_one_le
    {A : Type} (weight : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → 1 ≤ weight item) →
        items.length ≤ listNatWeight weight items
  | [], _ => Nat.le_refl 0
  | head :: tail, hweight => by
      have hhead := hweight head List.mem_cons_self
      have htail := list_length_le_listNatWeight_of_one_le
        weight tail (fun item hitem =>
          hweight item (List.mem_cons_of_mem head hitem))
      simp only [List.length_cons, listNatWeight]
      omega

theorem slabObservableTwoReplicaPairTargetSupportComponent_length_le_mass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId).length ≤
      slabObservableTwoReplicaPairTargetSupportMass
        D pair targetFaceId := by
  unfold slabObservableTwoReplicaPairTargetSupportMass
  apply list_length_le_listNatWeight_of_one_le
  intro faceId hface
  rcases
      slabObservableTwoReplicaPairTargetSupportComponent_face_positive
        D rootFaceId targetFaceId htarget pair hpair faceId hface with
    hleft | hright
  · omega
  · omega

/-! ## 3. Component size and mass sit below complete pair mass -/

private theorem eraseDupsLengthLeLocal {A : Type}
    [BEq A] (items : List A) :
    items.eraseDups.length ≤ items.length := by
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

theorem slabObservableTwoReplicaPairTargetSupportPlaquettes_length_le_component
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) :
    (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId).length ≤
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId).length := by
  unfold slabObservableTwoReplicaPairTargetSupportPlaquettes
  have hdedup := eraseDupsLengthLeLocal
    ((slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId).map
        (slabPlaquetteAt D.extent))
  rw [List.length_map] at hdedup
  exact hdedup

theorem slabObservableTwoReplicaPairTargetSupportMass_le_total
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairTargetSupportMass D pair targetFaceId ≤
      slabObservableTwoReplicaPairTotalPhysicalMass D pair := by
  unfold slabObservableTwoReplicaPairTargetSupportMass
    slabObservableTwoReplicaPairTotalPhysicalMass
  apply listNatWeight_le_of_nodup_mem
  · exact rootComponent_nodup
      (slabSupportFaceAdjacentB D.extent)
      (slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1)
      targetFaceId
  · intro faceId hface
    exact
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget pair hpair faceId hface

/-! ## 4. The physical-mass separation floor -/

/-- Every connected residue pair pays the geometric separation in actual
two-replica twice-spin mass on the connected component. -/
theorem slabObservableTwoReplicaPairPairedSupportConnected_componentMass_floor
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
      slabObservableTwoReplicaPairTargetSupportMass
        D pair targetFaceId := by
  exact Nat.le_trans
    (slabObservableTwoReplicaPairPairedSupportConnected_size_floor
      D rootFaceId targetFaceId htarget pair hpair hconnected)
    (Nat.le_trans
      (slabObservableTwoReplicaPairTargetSupportPlaquettes_length_le_component
        D pair targetFaceId)
      (slabObservableTwoReplicaPairTargetSupportComponent_length_le_mass
        D rootFaceId targetFaceId htarget pair hpair))

/-- In particular, the complete physical twice-spin mass of the two replicas
is at least the observable separation plus one. -/
theorem slabObservableTwoReplicaPairPairedSupportConnected_totalMass_floor
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
      slabObservableTwoReplicaPairTotalPhysicalMass D pair :=
  Nat.le_trans
    (slabObservableTwoReplicaPairPairedSupportConnected_componentMass_floor
      D rootFaceId targetFaceId htarget pair hpair hconnected)
    (slabObservableTwoReplicaPairTargetSupportMass_le_total
      D rootFaceId targetFaceId htarget pair hpair)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor.slabObservableTwoReplicaPairTargetSupportComponent_length_le_mass
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor.slabObservableTwoReplicaPairTargetSupportMass_le_total
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor.slabObservableTwoReplicaPairPairedSupportConnected_componentMass_floor
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor.slabObservableTwoReplicaPairPairedSupportConnected_totalMass_floor
