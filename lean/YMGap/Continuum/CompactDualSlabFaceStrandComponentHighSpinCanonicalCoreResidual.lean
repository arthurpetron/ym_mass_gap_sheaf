/-
# Sum the canonical high-spin core residual without component overcount

The pointwise exterior/core split bounds one component's residual by the
threshold on every face.  Summing that bound component-by-component would
introduce a spurious factor equal to the number of components.  Canonical
components are disjoint, so their selected multiplicities on one physical
face instead have total at most the face label `p`.

The arithmetic core is the superadditive truncation estimate

```text
sum_i (d_i - c) <= (sum_i d_i) - c.
```

With `c = p - S`, this contracts the complete canonical family to residual
multiplicity at most `S` on each face.  Serializing the aggregated residual
profile therefore costs at most `number of physical faces * S`, independently
of the number of connected components.

This module proves the global residual bound.  It does not construct an
accepted simultaneous exterior-peeling trace, compare the product of all
component weights, or prove finite-core coercivity.

Constructive contract: finite Boolean counts, canonical-component
disjointness, and exact `Nat` truncation arithmetic only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreResidual

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Finite disjoint-family counting -/

private theorem listNatWeight_congr {A : Type}
    (left right : A -> Nat) :
    forall items : List A,
      (forall item, item ∈ items -> left item = right item) ->
      listNatWeight left items = listNatWeight right items
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listNatWeight]
      rw [hagree head List.mem_cons_self]
      exact congrArg (right head + ·)
        (listNatWeight_congr left right tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem)))

private theorem listNatWeight_add {A : Type}
    (left right : A -> Nat) : forall items : List A,
    listNatWeight (fun item => left item + right item) items =
      listNatWeight left items + listNatWeight right items
  | [] => rfl
  | head :: tail => by
      simp only [listNatWeight]
      rw [listNatWeight_add left right tail]
      omega

private theorem listNatWeight_indicator_eq_zero_of_not_mem
    {A B : Type} [DecidableEq B] (blocks : A -> List B) (point : B) :
    forall items : List A,
      (forall item, item ∈ items -> point ∉ blocks item) ->
      listNatWeight
          (fun item => boolIndicator (decide (point ∈ blocks item))) items = 0
  | [], _ => rfl
  | head :: tail, hnot => by
      have hhead := hnot head List.mem_cons_self
      have htail := listNatWeight_indicator_eq_zero_of_not_mem
        blocks point tail
        (fun item hitem => hnot item (List.mem_cons_of_mem head hitem))
      simp only [listNatWeight]
      have hzero : boolIndicator (decide (point ∈ blocks head)) = 0 := by
        simp [hhead, boolIndicator]
      rw [hzero, htail]

/-- At most one member of a duplicate-free disjoint block family contains a
fixed point. -/
private theorem listNatWeight_membership_indicator_le_one
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (blocks : A -> List B) : forall items : List A,
    items.Nodup ->
    (forall left, left ∈ items -> forall right, right ∈ items ->
      left ≠ right -> SupportsDisjoint (blocks left) (blocks right)) ->
    forall point : B,
      listNatWeight
          (fun item => boolIndicator (decide (point ∈ blocks item))) items <= 1
  | [], _, _, _ => by simp [listNatWeight]
  | head :: tail, hnodup, hdisjoint, point => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : point ∈ blocks head
      · have htailNot : forall item, item ∈ tail -> point ∉ blocks item := by
          intro item hitem
          have hne : head ≠ item := by
            intro heq
            subst item
            exact hparts.1 hitem
          exact hdisjoint head List.mem_cons_self item
            (List.mem_cons_of_mem head hitem) hne point hhead
        have htailZero := listNatWeight_indicator_eq_zero_of_not_mem
          blocks point tail htailNot
        simp only [listNatWeight]
        have hone : boolIndicator (decide (point ∈ blocks head)) = 1 := by
          simp [hhead, boolIndicator]
        rw [hone, htailZero]
        omega
      · have htailBound := listNatWeight_membership_indicator_le_one
          blocks tail hparts.2
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne)
          point
        simp only [listNatWeight]
        have hzero : boolIndicator (decide (point ∈ blocks head)) = 0 := by
          simp [hhead, boolIndicator]
        rw [hzero]
        simpa only [Nat.zero_add] using htailBound

private theorem listNatWeight_zero {A : Type} : forall items : List A,
    listNatWeight (fun _ => 0) items = 0
  | [] => rfl
  | _ :: tail => by
      simp only [listNatWeight]
      simpa only [Nat.zero_add] using listNatWeight_zero tail

/-- If at each position at most one Boolean row is true, the sum of all row
counts is bounded by the interval length. -/
private theorem listNatWeight_boolCountFrom_le
    {A : Type} (selected : A -> Nat -> Bool) (items : List A) :
    forall (start length : Nat),
      (forall index, start <= index -> index < start + length ->
        listNatWeight
            (fun item => boolIndicator (selected item index)) items <= 1) ->
      listNatWeight
          (fun item => boolCountFrom (selected item) start length) items <=
        length
  | _, 0, _ => by
      change listNatWeight (fun _ => 0) items <= 0
      rw [listNatWeight_zero items]
      omega
  | start, Nat.succ length, hpoint => by
      have hnow := hpoint start (by omega) (by omega)
      have htail := listNatWeight_boolCountFrom_le selected items
        (start + 1) length
        (fun index hstart hfinish => hpoint index (by omega) (by omega))
      simp only [boolCountFrom]
      rw [listNatWeight_add]
      omega

private theorem nodup_of_map_nodup {A B : Type} (map : A -> B) :
    forall {items : List A}, (items.map map).Nodup -> items.Nodup
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

/-! ## 2. Canonical components consume one physical face only once -/

/-- Total selected multiplicity of all canonical components on one face. -/
def slabCanonicalComponentSelectionMassAtFace
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (faceId : Nat) : Nat :=
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  listNatWeight
    (fun component : SlabFaceStrandCanonicalComponent edges =>
      slabFaceStrandSelectionCount component.seed.selected faceId)
    (slabFaceStrandCanonicalComponents edges).attach

/-- Disjoint canonical components have total selected multiplicity at most
the physical label on a fixed face. -/
theorem slabCanonicalComponentSelectionMassAtFace_le
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (faceId : Nat) :
    slabCanonicalComponentSelectionMassAtFace
        K extent physical links assignment hassignment faceId <=
      physical faceId := by
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  let components := slabFaceStrandCanonicalComponents edges
  let rows : List (SlabFaceStrandCanonicalComponent edges) :=
    (slabFaceStrandCanonicalComponents edges).attach
  let selectedAt : SlabFaceStrandCanonicalComponent edges -> Nat -> Bool :=
    fun component slot =>
      slabFaceStrandSelectionAt component.seed.selected faceId slot
  change listNatWeight
      (fun component : SlabFaceStrandCanonicalComponent edges =>
        boolCountFrom (selectedAt component) 0 (physical faceId)) rows <=
    physical faceId
  apply listNatWeight_boolCountFrom_le selectedAt rows 0 (physical faceId)
  intro index _ hindex
  let copy : SlabFaceStrandCopy physical :=
    { faceId := faceId, slot := ⟨index, by omega⟩ }
  have hrowEq : forall component, component ∈ rows ->
      boolIndicator (selectedAt component index) =
        boolIndicator (decide (copy ∈ component.1)) := by
    intro component _
    have hselected : selectedAt component index =
        decide (copy ∈ component.1) := by
      unfold selectedAt
      change slabFaceStrandSelectionAt component.seed.selected faceId
          copy.slot.val = decide (copy ∈ component.1)
      rw [slabFaceStrandSelectionAt_fin]
      have hcopyEq :
          ({ faceId := faceId, slot := copy.slot } :
            SlabFaceStrandCopy physical) = copy := by
        apply slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
        · rfl
        · rfl
      rw [hcopyEq]
      unfold SlabFaceStrandSeed.selected
      by_cases hmem : copy ∈ component.1
      · have hseed := (component.mem_seed_component_iff copy).2 hmem
        simp [hmem, hseed]
      · have hseed : copy ∉ component.seed.component := by
          intro hselected
          exact hmem ((component.mem_seed_component_iff copy).1 hselected)
        simp [hmem, hseed]
    rw [hselected]
  rw [listNatWeight_congr
    (fun component => boolIndicator (selectedAt component index))
    (fun component => boolIndicator (decide (copy ∈ component.1)))
    rows hrowEq]
  apply listNatWeight_membership_indicator_le_one
    (fun component : SlabFaceStrandCanonicalComponent edges => component.1)
    rows
  · exact attach_nodup_of_nodup components
      (slabFaceStrandCanonicalComponents_nodup edges)
  · intro left hleft right hright hne
    have hvalueNe : left.1 ≠ right.1 := by
      intro hvalue
      exact hne (Subtype.ext hvalue)
    exact slabFaceStrandCanonicalComponents_distinctDisjoint edges
      left.1 left.2 right.1 right.2 hvalueNe

/-! ## 3. Contract all core residuals before serialization -/

private theorem coreResidualDropCount_eq_sub_available
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat) :
    coreResidualDropCount physical threshold drop faceId =
      drop faceId - (physical faceId - threshold) := by
  unfold coreResidualDropCount exteriorDropCount
  omega

/-- Charging the same truncated reserve separately to several terms only
decreases their total remainder. -/
private theorem listNatWeight_sub_constant_le_sub_total
    {A : Type} (value : A -> Nat) (reserve : Nat) :
    forall items : List A,
      listNatWeight (fun item => value item - reserve) items <=
        listNatWeight value items - reserve
  | [] => by simp [listNatWeight]
  | head :: tail => by
      have htail := listNatWeight_sub_constant_le_sub_total
        value reserve tail
      simp only [listNatWeight]
      omega

/-- Sum all canonical component residual multiplicities on one face. -/
def slabCanonicalCoreResidualDropCount
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold faceId : Nat) : Nat :=
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  listNatWeight
    (fun component : SlabFaceStrandCanonicalComponent edges =>
      coreResidualDropCount physical threshold
        (slabFaceStrandSelectionCount component.seed.selected) faceId)
    (slabFaceStrandCanonicalComponents edges).attach

/-- **No component-count loss.**  The total residual of the exhaustive
canonical family is at most the threshold on every physical face. -/
theorem slabCanonicalCoreResidualDropCount_le_threshold
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold faceId : Nat) :
    slabCanonicalCoreResidualDropCount
        K extent physical links assignment hassignment threshold faceId <=
      threshold := by
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  let components := slabFaceStrandCanonicalComponents edges
  let rows : List (SlabFaceStrandCanonicalComponent edges) :=
    (slabFaceStrandCanonicalComponents edges).attach
  let value : SlabFaceStrandCanonicalComponent edges -> Nat :=
    fun component =>
      slabFaceStrandSelectionCount component.seed.selected faceId
  let reserve := physical faceId - threshold
  have hselection : listNatWeight value rows <= physical faceId :=
    slabCanonicalComponentSelectionMassAtFace_le
      K extent physical links assignment hassignment faceId
  have htruncate := listNatWeight_sub_constant_le_sub_total
    value reserve rows
  change listNatWeight
      (fun component : SlabFaceStrandCanonicalComponent edges =>
        coreResidualDropCount physical threshold
          (slabFaceStrandSelectionCount component.seed.selected) faceId)
      rows <= threshold
  rw [listNatWeight_congr
    (fun component : SlabFaceStrandCanonicalComponent edges =>
      coreResidualDropCount physical threshold
        (slabFaceStrandSelectionCount component.seed.selected) faceId)
    (fun component => value component - reserve)
    rows (fun component _ =>
      coreResidualDropCount_eq_sub_available physical threshold
        (slabFaceStrandSelectionCount component.seed.selected) faceId)]
  omega

/-- The canonical grouped word for the sum of all component residuals. -/
def slabCanonicalCoreResidualFaces
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) : List Nat :=
  slabFaceDropList extent
    (slabCanonicalCoreResidualDropCount
      K extent physical links assignment hassignment threshold)

private theorem length_flatMap_le
    {A B : Type} (block : A -> List B) (bound : Nat) :
    forall items : List A,
      (forall item, item ∈ items -> (block item).length <= bound) ->
      (items.flatMap block).length <= items.length * bound
  | [], _ => by simp
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := length_flatMap_le block bound tail
        (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- The serialized residual of the complete canonical family has the same
`faces * threshold` bound as a single component, not an extra component-count
factor. -/
theorem slabCanonicalCoreResidualFaces_length_le
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) :
    (slabCanonicalCoreResidualFaces
      K extent physical links assignment hassignment threshold).length <=
      (slabPhysicalFaceEdges extent).length * threshold := by
  unfold slabCanonicalCoreResidualFaces slabFaceDropList
  apply length_flatMap_le
  intro faceId _
  rw [List.length_replicate]
  exact slabCanonicalCoreResidualDropCount_le_threshold
    K extent physical links assignment hassignment threshold faceId

#print axioms slabCanonicalComponentSelectionMassAtFace
#print axioms slabCanonicalComponentSelectionMassAtFace_le
#print axioms slabCanonicalCoreResidualDropCount
#print axioms slabCanonicalCoreResidualDropCount_le_threshold
#print axioms slabCanonicalCoreResidualFaces
#print axioms slabCanonicalCoreResidualFaces_length_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreResidual
