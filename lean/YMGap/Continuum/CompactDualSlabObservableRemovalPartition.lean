/-
# Exact finite partition of observable-rooted removal fibers

The literal positive observable source list is now equipped with a
deterministic removal key: its exact lowered target and component peel size.
This module applies the generic finite deterministic-pushforward theorem to
that key.

The target universe is not an opaque deduplication.  It is the dependent
Cartesian list of every literal expanded target and every size from zero to
the explicit physical strand ceiling.  Exact target-key injectivity makes
this universe duplicate-free, while the component drop count and physical
cutoff prove coverage.  Finite Fubini then identifies the whole positive
source weight with the nested sum of the actual fixed-target source fibers.

Constructive contract: explicit finite lists, a physical strand-count bound,
and deterministic finite pushforward only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableRemovalFiber
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.CompactDualSlabObservableRemovalPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A finite physical ceiling for every component size -/

private theorem natListSum_map_le_length_mul
    {A : Type} (value : A -> Nat) (bound : Nat) :
    forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
      natListSum (items.map value) <= items.length * bound
  | [], _ => by simp [natListSum]
  | head :: tail, hbound => by
      have hhead : value head <= bound :=
        hbound head List.mem_cons_self
      have htail : natListSum (tail.map value) <= tail.length * bound :=
        natListSum_map_le_length_mul value bound tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem))
      simp only [List.map_cons, natListSum, List.length_cons]
      calc
        value head + natListSum (tail.map value) <=
            bound + tail.length * bound := Nat.add_le_add hhead htail
        _ = (tail.length + 1) * bound := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Every rooted component contains no more physical strands than the number
of slab faces times the physical cutoff. -/
theorem SlabFusionWitnessFaceStrandSeed.peelFaces_length_le_cutoff
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length <=
      (slabPhysicalFaceEdges extent).length * K := by
  rw [SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1]
  apply natListSum_map_le_length_mul
  intro faceId hface
  exact Nat.le_trans
    (slabFaceStrandSelectionCount_le seed.selected faceId)
    (hbounded faceId hface)

/-- The inclusive maximum component size used by the exact target universe. -/
def slabObservableRemovalMaxSize (D : SlabPhysicalData) : Nat :=
  D.faceEdges.length * D.cutoff

/-! ## 2. A duplicate-free complete removal-key universe -/

private theorem range_nodup_local :
    forall count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A -> List B) :
    forall source : List A, source.Nodup ->
      (forall item, item ∈ source -> (block item).Nodup) ->
      (forall left, left ∈ source -> forall right, right ∈ source ->
        left ≠ right -> forall value, value ∈ block left ->
          value ∉ block right) ->
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨item, hitem, hvalueItem⟩ := List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

/-- All sizes attached to one literal expanded target. -/
def slabExpandedFineRemovalKeyBlock
    (D : SlabPhysicalData)
    (target : SlabLabelling × SlabFusionWitnessAssignment) :
    List SlabExpandedFineRemovalKey :=
  (List.range (slabObservableRemovalMaxSize D + 1)).map
    (slabExpandedFineRemovalKey D target)

/-- Every literal expanded target paired with every size through the explicit
physical strand ceiling. -/
def slabExpandedFineRemovalKeys (D : SlabPhysicalData) :
    List SlabExpandedFineRemovalKey :=
  (slabExpandedFineSources D).flatMap
    (slabExpandedFineRemovalKeyBlock D)

/-- The explicit removal-key universe is duplicate-free. -/
theorem slabExpandedFineRemovalKeys_nodup (D : SlabPhysicalData) :
    (slabExpandedFineRemovalKeys D).Nodup := by
  unfold slabExpandedFineRemovalKeys
  apply nodup_flatMap_of_disjoint_blocks
  · exact slabExpandedFineSources_nodup D
  · intro target _
    unfold slabExpandedFineRemovalKeyBlock
    apply nodup_map_of_injOn
    · exact range_nodup_local _
    · intro left _ right _ heq
      exact congrArg SlabExpandedFineRemovalKey.peelSize heq
  · intro left hleft right hright hne value hvalueLeft hvalueRight
    obtain ⟨leftSize, _, hleftEq⟩ := List.mem_map.mp hvalueLeft
    obtain ⟨rightSize, _, hrightEq⟩ := List.mem_map.mp hvalueRight
    have hkey : slabExpandedFineRemovalKey D left leftSize =
        slabExpandedFineRemovalKey D right rightSize :=
      hleftEq.trans hrightEq.symm
    have htargetKey := congrArg SlabExpandedFineRemovalKey.targetKey hkey
    exact hne (slabExpandedFineTargetKey_eq_source_eq
      D hleft hright htargetKey)

/-! ## 3. Deterministic key pushforward of the positive source measure -/

/-- Weight of one attached positive source. -/
def slabObservablePositiveEntryWeight
    (D : SlabPhysicalData) {faceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId) : Q' :=
  slabExpandedFineSourceWeight D entry.1

/-- Removal key of one attached positive source. -/
def slabObservablePositiveEntryCode
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabExpandedFineRemovalKey :=
  entry.removalKey D faceId hface

/-- Every positive source's removal key lies in the explicit target/size
universe. -/
theorem slabObservablePositiveEntryCode_mem
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    slabObservablePositiveEntryCode D faceId hface entry ∈
      slabExpandedFineRemovalKeys D := by
  let seed := entry.seed D faceId hface
  let target : SlabLabelling × SlabFusionWitnessAssignment :=
    (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed,
      SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
  have htarget : target ∈ slabExpandedFineSources D :=
    SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
      D entry.physical_mem seed
  have hbounded : SlabFaceLabellingBounded
      D.cutoff D.extent entry.1.1 := by
    have hsound := boundedEdgeLabellings_sound
      D.cutoff D.faceEdges entry.1.1 entry.physical_mem
    intro selected hselected
    exact Nat.le_of_lt_succ (hsound.1 selected hselected)
  have hsize : (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length <
      slabObservableRemovalMaxSize D + 1 := by
    exact Nat.lt_succ_of_le
      (SlabFusionWitnessFaceStrandSeed.peelFaces_length_le_cutoff
        seed hbounded)
  unfold slabExpandedFineRemovalKeys
  apply List.mem_flatMap.mpr
  refine ⟨target, htarget, ?_⟩
  unfold slabExpandedFineRemovalKeyBlock
  apply List.mem_map.mpr
  exact ⟨(SlabFusionWitnessFaceStrandSeed.peelFaces seed).length,
    List.mem_range.mpr hsize, rfl⟩

/-- Generic deterministic fiber mass agrees exactly with the already
constructed literal fixed-target source fiber. -/
theorem slabObservablePositiveFiberWeight_eqv_removalFiber
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat) :
    fiberWeight
        (slabObservablePositiveSourceEntries D faceId)
        (slabObservablePositiveEntryWeight D)
        (slabObservablePositiveEntryCode D faceId hface)
        (slabExpandedFineRemovalKey D target peelSize) ≈
      listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveRemovalFiber
          D faceId hface target peelSize) := by
  unfold fiberWeight slabObservablePositiveRemovalFiber
    slabObservablePositiveRemovalFiberEntries
    slabObservablePositiveSourceEntries
  have hfilter :
      ((slabObservablePositiveExpandedSources D faceId).attach.filter
        (fun entry => decide
          (slabExpandedFineRemovalKey D target peelSize =
            slabObservablePositiveEntryCode D faceId hface entry))) =
      ((slabObservablePositiveExpandedSources D faceId).attach.filter
        (fun entry => decide
          (SlabObservablePositiveSourceEntry.removalKey
              D faceId hface entry =
            slabExpandedFineRemovalKey D target peelSize))) := by
    apply List.filter_congr
    intro entry _
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro heq
      exact decide_eq_true (of_decide_eq_true heq).symm
    · intro heq
      exact decide_eq_true (of_decide_eq_true heq).symm
  rw [hfilter]
  rw [listQSum_map]
  apply listQSum_congr
  intro entry
  exact Q'.eqv_refl _

/-! ## 4. Exact nested partition of the positive source weight -/

/-- Summation over the flat removal-key universe is exact finite Fubini over
literal targets and their size blocks. -/
theorem slabExpandedFineRemovalKeys_sum_eqv_nested
    (D : SlabPhysicalData) (value : SlabExpandedFineRemovalKey -> Q') :
    listQSum value (slabExpandedFineRemovalKeys D) ≈
      listQSum
        (fun target =>
          listQSum
            (fun peelSize =>
              value (slabExpandedFineRemovalKey D target peelSize))
            (List.range (slabObservableRemovalMaxSize D + 1)))
        (slabExpandedFineSources D) := by
  unfold slabExpandedFineRemovalKeys
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (slabExpandedFineRemovalKeyBlock D)
      (slabExpandedFineSources D)) ?_
  apply listQSum_congr
  intro target
  unfold slabExpandedFineRemovalKeyBlock
  exact Q'.eqv_of_eq (listQSum_map value
    (slabExpandedFineRemovalKey D target)
    (List.range (slabObservableRemovalMaxSize D + 1)))

/-- Replacing each deterministic attached-entry fiber by the corresponding
literal source-pair fiber preserves the complete nested sum. -/
theorem slabObservablePositiveRemovalFibers_eqv_nestedFiberWeights
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum
        (fun target =>
          listQSum
            (fun peelSize =>
              listQSum (slabExpandedFineSourceWeight D)
                (slabObservablePositiveRemovalFiber
                  D faceId hface target peelSize))
            (List.range (slabObservableRemovalMaxSize D + 1)))
        (slabExpandedFineSources D) ≈
      listQSum
        (fun target =>
          listQSum
            (fun peelSize =>
              fiberWeight
                (slabObservablePositiveSourceEntries D faceId)
                (slabObservablePositiveEntryWeight D)
                (slabObservablePositiveEntryCode D faceId hface)
                (slabExpandedFineRemovalKey D target peelSize))
            (List.range (slabObservableRemovalMaxSize D + 1)))
        (slabExpandedFineSources D) := by
  apply listQSum_congr
  intro target
  apply listQSum_congr
  intro peelSize
  exact Q'.eqv_symm
    (slabObservablePositiveFiberWeight_eqv_removalFiber
      D faceId hface target peelSize)

/-- **Exact observable-rooted finite Fubini.**  Summing the actual fixed-target
fibers over every literal expanded target and every size through the physical
strand ceiling recovers the complete positive-face expanded source weight. -/
theorem slabObservablePositiveRemovalFibers_weight_total
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum
        (fun target =>
          listQSum
            (fun peelSize =>
              listQSum (slabExpandedFineSourceWeight D)
                (slabObservablePositiveRemovalFiber
                  D faceId hface target peelSize))
            (List.range (slabObservableRemovalMaxSize D + 1)))
        (slabExpandedFineSources D) ≈
      listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D faceId) := by
  have htotal := fiberWeight_total
    (slabObservablePositiveSourceEntries D faceId)
    (slabObservablePositiveEntryWeight D)
    (slabObservablePositiveEntryCode D faceId hface)
    (slabExpandedFineRemovalKeys D)
    (slabExpandedFineRemovalKeys_nodup D)
    (fun entry _ => slabObservablePositiveEntryCode_mem
      D faceId hface entry)
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun peelSize =>
            fiberWeight
              (slabObservablePositiveSourceEntries D faceId)
              (slabObservablePositiveEntryWeight D)
              (slabObservablePositiveEntryCode D faceId hface)
              (slabExpandedFineRemovalKey D target peelSize))
          (List.range (slabObservableRemovalMaxSize D + 1)))
      (slabExpandedFineSources D)) _
    (slabObservablePositiveRemovalFibers_eqv_nestedFiberWeights
      D faceId hface) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fiberWeight
        (slabObservablePositiveSourceEntries D faceId)
        (slabObservablePositiveEntryWeight D)
        (slabObservablePositiveEntryCode D faceId hface))
      (slabExpandedFineRemovalKeys D)) _ ?_ ?_
  · exact Q'.eqv_symm
      (slabExpandedFineRemovalKeys_sum_eqv_nested D
        (fiberWeight
          (slabObservablePositiveSourceEntries D faceId)
          (slabObservablePositiveEntryWeight D)
          (slabObservablePositiveEntryCode D faceId hface)))
  · refine Q'.eqv_trans _ _ _ htotal ?_
    unfold slabObservablePositiveEntryWeight
      slabObservablePositiveSourceEntries
    exact Q'.eqv_of_eq
      (listQSum_attach (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D faceId))

#print axioms SlabFusionWitnessFaceStrandSeed.peelFaces_length_le_cutoff
#print axioms slabObservableRemovalMaxSize
#print axioms slabExpandedFineRemovalKeyBlock
#print axioms slabExpandedFineRemovalKeys
#print axioms slabExpandedFineRemovalKeys_nodup
#print axioms slabObservablePositiveEntryWeight
#print axioms slabObservablePositiveEntryCode
#print axioms slabObservablePositiveEntryCode_mem
#print axioms slabObservablePositiveFiberWeight_eqv_removalFiber
#print axioms slabExpandedFineRemovalKeys_sum_eqv_nested
#print axioms slabObservablePositiveRemovalFibers_eqv_nestedFiberWeights
#print axioms slabObservablePositiveRemovalFibers_weight_total

end YMGap.Continuum.CompactDualSlabObservableRemovalPartition
