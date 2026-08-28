/-
# Partition and contract every canonical exterior-removal source

The complete canonical classifier routes each expanded source either to a
specific accepted exterior component or to the finite core.  This module
collects the exterior outputs as an actual finite source list and partitions
them by the complete removal key

```text
(root face, component size, encoded lower physical/assignment target).
```

The realized-key representative partition retains one concrete exterior
source per key.  Its component therefore supplies the actual dependent target
and accepted removal witness required by the arbitrary-coupling fiber theorem.
Every representative fiber contracts by `(8/25)^n`, and finite summation gives
an explicit bound for the total exterior source weight by the corresponding
sum of weighted target representatives.

The target sum may still contain congestion: distinct root/size keys can have
the same lowered target.  This module exposes that multiplicity rather than
hiding it in a uniform constant.  It does not estimate the finite-core branch
or prove a posterior-variance fraction.

Constructive contract: literal finite expanded sources, executable canonical
classification, realized-key partition, and the accepted high-spin fiber
estimate only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabExpandedTargetKey
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorOrCore
import YMGap.Continuum.FiniteKeyRepresentativePartition

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorOrCore
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal exterior outputs of the complete source classifier -/

/-- One actual expanded source together with the canonical exterior component
selected by the complete classifier. -/
structure SlabCanonicalExteriorSourceEntry
    (D : SlabPhysicalData) (threshold : Nat) : Type where
  source : SlabLabelling × SlabFusionWitnessAssignment
  physical_mem : source.1 ∈ D.physicalLabellings
  assignment_mem : source.2 ∈
    slabFusionWitnessAssignmentsOn D.cutoff D.extent source.1
      (boundaryCompleteSlabLinks D.extent)
  component : SlabFaceStrandCanonicalComponent
    (slabFusionWitnessAssignmentFaceStrandEdges
      D.cutoff D.extent source.1 (boundaryCompleteSlabLinks D.extent)
        source.2 assignment_mem)
  rootFaceId : Nat
  rootFaceId_eq : rootFaceId = component.seed.root.faceId
  peelSize : Nat
  peelSize_eq : peelSize =
    (SlabFusionWitnessFaceStrandSeed.peelFaces component.seed).length
  reserve_paid :
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
      component.seed threshold = true

/-- The source carried by an exterior entry belongs to the literal expanded
carrier. -/
theorem SlabCanonicalExteriorSourceEntry.source_mem
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    entry.source ∈ slabExpandedFineSources D :=
  mem_slabExpandedFineSources_iff.mpr
    ⟨entry.physical_mem, entry.assignment_mem⟩

/-- Emit an exterior entry from one already evaluated complete classifier. -/
def slabCanonicalExteriorSourceEntryOfDecision?
    (D : SlabPhysicalData) (threshold : Nat)
    (source : SlabLabelling × SlabFusionWitnessAssignment)
    (physical_mem : source.1 ∈ D.physicalLabellings)
    (assignment_mem : source.2 ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent source.1
        (boundaryCompleteSlabLinks D.extent))
    (decision : SlabCanonicalExteriorOrFiniteCore
      D.cutoff D.extent source.1 (boundaryCompleteSlabLinks D.extent)
        source.2 assignment_mem threshold) :
    Option (SlabCanonicalExteriorSourceEntry D threshold) :=
  match decision with
  | .exterior component reserve_paid =>
      some
        { source := source
          physical_mem := physical_mem
          assignment_mem := assignment_mem
          component := component
          rootFaceId := component.seed.root.faceId
          rootFaceId_eq := rfl
          peelSize :=
            (SlabFusionWitnessFaceStrandSeed.peelFaces component.seed).length
          peelSize_eq := rfl
          reserve_paid := reserve_paid }
  | .finiteCore _ _ _ _ => none

/-- Run the complete canonical classifier on one attached expanded source and
emit its selected component exactly in the exterior branch. -/
def slabCanonicalExteriorSourceEntry?
    (D : SlabPhysicalData) (threshold : Nat)
    (source : {source // source ∈ slabExpandedFineSources D}) :
    Option (SlabCanonicalExteriorSourceEntry D threshold) :=
  let hsource := mem_slabExpandedFineSources_iff.mp source.2
  slabCanonicalExteriorSourceEntryOfDecision? D threshold source.1
    hsource.1 hsource.2
    (slabCanonicalExteriorOrFiniteCore
      D.cutoff D.extent source.1.1 (boundaryCompleteSlabLinks D.extent)
        source.1.2 hsource.2 threshold)

/-- The decision-level emitter never changes the displayed raw source. -/
theorem slabCanonicalExteriorSourceEntryOfDecision?_source_eq_of_some
    (D : SlabPhysicalData) (threshold : Nat)
    (source : SlabLabelling × SlabFusionWitnessAssignment)
    (physical_mem : source.1 ∈ D.physicalLabellings)
    (assignment_mem : source.2 ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent source.1
        (boundaryCompleteSlabLinks D.extent))
    (decision : SlabCanonicalExteriorOrFiniteCore
      D.cutoff D.extent source.1 (boundaryCompleteSlabLinks D.extent)
        source.2 assignment_mem threshold)
    (entry : SlabCanonicalExteriorSourceEntry D threshold)
    (hsome : slabCanonicalExteriorSourceEntryOfDecision? D threshold source
      physical_mem assignment_mem decision = some entry) :
    entry.source = source := by
  cases decision with
  | exterior component reserve_paid =>
      exact (congrArg SlabCanonicalExteriorSourceEntry.source
        (Option.some.inj hsome)).symm
  | finiteCore entries components_eq anchor_copies_eq component_count_le =>
      cases hsome

/-- Every emitted entry retains exactly the source attached at its input. -/
theorem slabCanonicalExteriorSourceEntry?_source_eq_of_some
    (D : SlabPhysicalData) (threshold : Nat)
    (source : {source // source ∈ slabExpandedFineSources D})
    (entry : SlabCanonicalExteriorSourceEntry D threshold)
    (hsome : slabCanonicalExteriorSourceEntry? D threshold source =
      some entry) :
    entry.source = source.1 := by
  unfold slabCanonicalExteriorSourceEntry? at hsome
  exact slabCanonicalExteriorSourceEntryOfDecision?_source_eq_of_some
    D threshold source.1
      (mem_slabExpandedFineSources_iff.mp source.2).1
      (mem_slabExpandedFineSources_iff.mp source.2).2 _ entry hsome

/-- All actual exterior outputs of the complete source classifier. -/
def slabCanonicalExteriorSourceEntries
    (D : SlabPhysicalData) (threshold : Nat) :
    List (SlabCanonicalExteriorSourceEntry D threshold) :=
  (slabExpandedFineSources D).attach.filterMap
    (slabCanonicalExteriorSourceEntry? D threshold)

/-- The corresponding literal exterior source-pair carrier. -/
def slabCanonicalExteriorSources
    (D : SlabPhysicalData) (threshold : Nat) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabCanonicalExteriorSourceEntries D threshold).map
    SlabCanonicalExteriorSourceEntry.source

private theorem map_filterMap_sublist_map
    {Input Output Source : Type}
    (emit : Input -> Option Output) (output : Output -> Source)
    (input : Input -> Source)
    (hsource : forall item value, emit item = some value ->
      output value = input item) : forall items : List Input,
    ((items.filterMap emit).map output).Sublist (items.map input)
  | [] => List.Sublist.slnil
  | item :: items => by
      rw [List.filterMap_cons, List.map_cons]
      cases hemit : emit item with
      | none =>
          exact List.Sublist.cons (input item)
            (map_filterMap_sublist_map emit output input hsource items)
      | some value =>
          simp only [List.map_cons]
          rw [hsource item value hemit]
          exact List.Sublist.cons₂ (input item)
            (map_filterMap_sublist_map emit output input hsource items)

private theorem nodup_of_sublist {A : Type} {selected source : List A}
    (hsub : selected.Sublist source) (hsource : source.Nodup) :
    selected.Nodup := by
  induction hsub with
  | slnil => exact List.nodup_nil
  | cons item hsub ih =>
      exact ih (List.nodup_cons.mp hsource).2
  | cons₂ item hsub ih =>
      have hparts := List.nodup_cons.mp hsource
      apply List.nodup_cons.mpr
      refine ⟨?_, ih hparts.2⟩
      intro hmem
      exact hparts.1 (List.Sublist.mem hmem hsub)

/-- The emitted literal exterior source list is duplicate-free. -/
theorem slabCanonicalExteriorSources_nodup
    (D : SlabPhysicalData) (threshold : Nat) :
    (slabCanonicalExteriorSources D threshold).Nodup := by
  apply nodup_of_sublist
  · unfold slabCanonicalExteriorSources slabCanonicalExteriorSourceEntries
    have hsub := map_filterMap_sublist_map
      (slabCanonicalExteriorSourceEntry? D threshold)
      SlabCanonicalExteriorSourceEntry.source Subtype.val
      (slabCanonicalExteriorSourceEntry?_source_eq_of_some D threshold)
      (slabExpandedFineSources D).attach
    simpa only [List.attach_map_subtype_val] using hsub
  · exact slabExpandedFineSources_nodup D

/-! ## 2. Complete decidable removal keys and their concrete targets -/

/-- The complete key needed by the adaptive inverse-fiber theorem. -/
structure SlabCanonicalExteriorRemovalKey : Type where
  rootFaceId : Nat
  peelSize : Nat
  targetKey : SlabExpandedFineTargetKey
  deriving DecidableEq

/-- The actual lowered target pair carried by one exterior entry. -/
def SlabCanonicalExteriorSourceEntry.target
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (SlabFusionWitnessFaceStrandSeed.lowerPhysical entry.component.seed,
    SlabFusionWitnessFaceStrandSeed.lowerAssignment entry.component.seed)

/-- Every concrete exterior target remains in the expanded production
carrier. -/
theorem SlabCanonicalExteriorSourceEntry.target_mem
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    entry.target ∈ slabExpandedFineSources D :=
  SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
    D entry.physical_mem entry.component.seed

/-- Encode the selected root, exact component size, and complete lowered
target. -/
def SlabCanonicalExteriorSourceEntry.removalKey
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    SlabCanonicalExteriorRemovalKey where
  rootFaceId := entry.rootFaceId
  peelSize := entry.peelSize
  targetKey := slabExpandedFineTargetKey D entry.target.1 entry.target.2

/-- Equal complete removal keys force equal concrete lowered target pairs. -/
theorem SlabCanonicalExteriorSourceEntry.target_eq_of_removalKey_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (left right : SlabCanonicalExteriorSourceEntry D threshold)
    (hkey : left.removalKey = right.removalKey) :
    left.target = right.target :=
  slabExpandedFineTargetKey_eq_source_eq D left.target_mem right.target_mem
    (congrArg SlabCanonicalExteriorRemovalKey.targetKey hkey)

/-- Equal removal keys identify the selected root face. -/
theorem SlabCanonicalExteriorSourceEntry.rootFaceId_eq_of_removalKey_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (left right : SlabCanonicalExteriorSourceEntry D threshold)
    (hkey : left.removalKey = right.removalKey) :
    left.rootFaceId = right.rootFaceId :=
  congrArg SlabCanonicalExteriorRemovalKey.rootFaceId hkey

/-- Equal removal keys identify the exact component size. -/
theorem SlabCanonicalExteriorSourceEntry.peelSize_eq_of_removalKey_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (left right : SlabCanonicalExteriorSourceEntry D threshold)
    (hkey : left.removalKey = right.removalKey) :
    left.peelSize = right.peelSize :=
  congrArg SlabCanonicalExteriorRemovalKey.peelSize hkey

/-- The adaptive inverse-fiber code of the selected canonical component. -/
def SlabCanonicalExteriorSourceEntry.entropyCode
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    ComponentAdaptiveEntropyCode :=
  componentAdaptiveEntropyCode entry.component.seed

/-! ## 3. Realized representative fibers -/

/-- One retained actual exterior source for every realized complete removal
key. -/
def slabCanonicalExteriorRepresentatives
    (D : SlabPhysicalData) (threshold : Nat) :
    List (SlabCanonicalExteriorSourceEntry D threshold) :=
  keyRepresentatives SlabCanonicalExteriorSourceEntry.removalKey
    (slabCanonicalExteriorSourceEntries D threshold)

/-- Exterior entries with the same complete removal key as one concrete
representative. -/
def slabCanonicalExteriorRepresentativeFiberEntries
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    List (SlabCanonicalExteriorSourceEntry D threshold) :=
  representativeFiber (slabCanonicalExteriorSourceEntries D threshold)
    SlabCanonicalExteriorSourceEntry.removalKey representative

/-- Literal source pairs in one complete removal fiber. -/
def slabCanonicalExteriorRepresentativeFiberSources
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabCanonicalExteriorRepresentativeFiberEntries representative).map
    SlabCanonicalExteriorSourceEntry.source

private theorem map_filter_sublist_map
    {A B : Type} (map : A -> B) (test : A -> Bool) :
    forall items : List A,
      ((items.filter test).map map).Sublist (items.map map)
  | [] => List.Sublist.slnil
  | item :: items => by
      rw [List.filter_cons, List.map_cons]
      split
      · simp only [List.map_cons]
        exact List.Sublist.cons₂ (map item)
          (map_filter_sublist_map map test items)
      · exact List.Sublist.cons (map item)
          (map_filter_sublist_map map test items)

/-- Every realized complete removal fiber is duplicate-free as a literal
source-pair list. -/
theorem slabCanonicalExteriorRepresentativeFiberSources_nodup
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    (slabCanonicalExteriorRepresentativeFiberSources representative).Nodup :=
  nodup_of_sublist
    (map_filter_sublist_map SlabCanonicalExteriorSourceEntry.source
      (fun entry => decide
        (representative.removalKey = entry.removalKey))
      (slabCanonicalExteriorSourceEntries D threshold))
    (slabCanonicalExteriorSources_nodup D threshold)

/-- Two emitted entries in the literal exterior list with the same raw source
are equal, because the executable classifier emits at most one value for one
attached source. -/
theorem slabCanonicalExteriorSourceEntry_eq_of_source_eq
    {D : SlabPhysicalData} {threshold : Nat}
    {left right : SlabCanonicalExteriorSourceEntry D threshold}
    (hleft : left ∈ slabCanonicalExteriorSourceEntries D threshold)
    (hright : right ∈ slabCanonicalExteriorSourceEntries D threshold)
    (hsource : left.source = right.source) : left = right := by
  unfold slabCanonicalExteriorSourceEntries at hleft hright
  obtain ⟨leftAttached, _, hleftSome⟩ := List.mem_filterMap.mp hleft
  obtain ⟨rightAttached, _, hrightSome⟩ := List.mem_filterMap.mp hright
  have hleftSource := slabCanonicalExteriorSourceEntry?_source_eq_of_some
    D threshold leftAttached left hleftSome
  have hrightSource := slabCanonicalExteriorSourceEntry?_source_eq_of_some
    D threshold rightAttached right hrightSome
  have hattached : leftAttached = rightAttached := by
    apply Subtype.ext
    exact hleftSource.symm.trans (hsource.trans hrightSource)
  subst rightAttached
  exact Option.some.inj (hleftSome.symm.trans hrightSome)

/-- Every entry in one representative fiber has exactly the representative's
complete removal key. -/
theorem slabCanonicalExteriorRepresentativeFiberEntry_key_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (representative entry : SlabCanonicalExteriorSourceEntry D threshold)
    (hentry : entry ∈
      slabCanonicalExteriorRepresentativeFiberEntries representative) :
    representative.removalKey = entry.removalKey :=
  of_decide_eq_true (List.mem_filter.mp hentry).2

/-- Physical cutoff boundedness for every exterior entry. -/
theorem SlabCanonicalExteriorSourceEntry.source_bounded
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    SlabFaceLabellingBounded D.cutoff D.extent entry.source.1 := by
  have hsound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges entry.source.1 entry.physical_mem
  intro faceId hface
  exact Nat.le_of_lt_succ (hsound.1 faceId hface)

private theorem nodup_of_map_nodup {A B : Type} (map : A -> B) :
    forall {items : List A}, (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup map hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

/-- The adaptive entropy codes of one representative fiber are
duplicate-free. -/
theorem slabCanonicalExteriorRepresentativeFiberCodes_nodup
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    ((slabCanonicalExteriorRepresentativeFiberEntries representative).map
      SlabCanonicalExteriorSourceEntry.entropyCode).Nodup := by
  let items := slabCanonicalExteriorRepresentativeFiberEntries representative
  have hitems : items.Nodup :=
    nodup_of_map_nodup SlabCanonicalExteriorSourceEntry.source
      (slabCanonicalExteriorRepresentativeFiberSources_nodup representative)
  apply nodup_map_of_injOn
    SlabCanonicalExteriorSourceEntry.entropyCode items hitems
  intro left hleft right hright hcode
  have hleftKey :=
    slabCanonicalExteriorRepresentativeFiberEntry_key_eq
      representative left hleft
  have hrightKey :=
    slabCanonicalExteriorRepresentativeFiberEntry_key_eq
      representative right hright
  have hkey : left.removalKey = right.removalKey :=
    hleftKey.symm.trans hrightKey
  have hroot :=
    SlabCanonicalExteriorSourceEntry.rootFaceId_eq_of_removalKey_eq
      left right hkey
  have htarget :=
    SlabCanonicalExteriorSourceEntry.target_eq_of_removalKey_eq
      left right hkey
  have hcomponentRoot : left.component.seed.root.faceId =
      right.component.seed.root.faceId :=
    left.rootFaceId_eq.symm.trans (hroot.trans right.rootFaceId_eq)
  have hsourceData := componentAdaptiveEntropyCode_eq_sourceData_eq
    left.component.seed right.component.seed hcomponentRoot
    (congrArg Prod.fst htarget) (congrArg Prod.snd htarget) hcode
  apply slabCanonicalExteriorSourceEntry_eq_of_source_eq
  · exact (List.mem_filter.mp hleft).1
  · exact (List.mem_filter.mp hright).1
  · exact Prod.ext hsourceData.1 hsourceData.2

/-- One realized representative fiber has at most the adaptive entropy base
to the component-size power. -/
theorem slabCanonicalExteriorRepresentativeFiberEntries_length_le
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    (slabCanonicalExteriorRepresentativeFiberEntries representative).length <=
      componentAdaptiveEntropyBase ^ representative.peelSize := by
  let items := slabCanonicalExteriorRepresentativeFiberEntries representative
  let encode := @SlabCanonicalExteriorSourceEntry.entropyCode D threshold
  have hsubset : forall code, code ∈ items.map encode ->
      code ∈ componentAdaptiveEntropyCarrier D.extent
        representative.rootFaceId representative.peelSize := by
    intro code hcode
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hcode
    have hkey := slabCanonicalExteriorRepresentativeFiberEntry_key_eq
      representative entry hentry
    have hroot :=
      SlabCanonicalExteriorSourceEntry.rootFaceId_eq_of_removalKey_eq
        representative entry hkey
    have hpeel :=
      SlabCanonicalExteriorSourceEntry.peelSize_eq_of_removalKey_eq
        representative entry hkey
    have hmem := componentAdaptiveEntropyCode_mem_carrier
      entry.component.seed
    rw [← entry.rootFaceId_eq, ← entry.peelSize_eq,
      ← hroot, ← hpeel] at hmem
    exact hmem
  have hbound := nodup_subset_length_le
    (items.map encode)
    (componentAdaptiveEntropyCarrier D.extent
      representative.rootFaceId representative.peelSize)
    (slabCanonicalExteriorRepresentativeFiberCodes_nodup representative)
    hsubset
  calc
    items.length = (items.map encode).length := (List.length_map _).symm
    _ <= (componentAdaptiveEntropyCarrier D.extent
          representative.rootFaceId representative.peelSize).length := hbound
    _ <= componentAdaptiveEntropyBase ^ representative.peelSize :=
      componentAdaptiveEntropyCarrier_length_le _ _ _

/-! ## 4. Exact partition and arbitrary-coupling contraction -/

/-- Corrected-slab data at an arbitrary nonnegative rational coupling. -/
def couplingSlabPhysicalData
    (w : Q') (hw0 : (0 : Q') <= w) (cutoff half : Nat) : SlabPhysicalData :=
  { coupling := w
    coupling_nonnegative := hw0
    cutoff := cutoff
    half := half }

private theorem listQSum_map_local {A B : Type}
    (value : B -> Q') (map : A -> B) : forall items : List A,
    listQSum value (items.map map) =
      listQSum (fun item => value (map item)) items
  | [] => rfl
  | head :: tail =>
      congrArg (fun rest => value (map head) + rest)
        (listQSum_map_local value map tail)

/-- The realized representative fibers recover exactly the complete exterior
source weight. -/
theorem slabCanonicalExteriorRepresentativeFibers_weight_total
    (D : SlabPhysicalData) (threshold : Nat) :
    listQSum
        (fun representative =>
          listQSum
            (fun entry => slabExpandedFineSourceWeight D entry.source)
            (slabCanonicalExteriorRepresentativeFiberEntries representative))
        (slabCanonicalExteriorRepresentatives D threshold) ≈
      listQSum (slabExpandedFineSourceWeight D)
        (slabCanonicalExteriorSources D threshold) := by
  have htotal := keyRepresentativeFibers_weight_total
    (slabCanonicalExteriorSourceEntries D threshold)
    (fun entry => slabExpandedFineSourceWeight D entry.source)
    SlabCanonicalExteriorSourceEntry.removalKey
  unfold slabCanonicalExteriorRepresentatives
    slabCanonicalExteriorRepresentativeFiberEntries
    slabCanonicalExteriorSources
  simp only [listQSum_map_local]
  exact htotal

/-- Every realized exterior fiber obeys the arbitrary-coupling strict
`(8/25)^n` bound against its concrete representative target. -/
theorem slabCanonicalExteriorRepresentativeFiber_weight_sum_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat)
    (representative : SlabCanonicalExteriorSourceEntry
      (couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half)
      (anchorPaidExteriorThreshold w)) :
    let D := couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half
    listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.source)
        (slabCanonicalExteriorRepresentativeFiberEntries representative) <=
      componentAdaptiveEntropyAnchorRatio ^
          representative.peelSize *
        slabExpandedFineSourceWeight D representative.target := by
  dsimp only [couplingSlabPhysicalData]
  apply fixedCardinalityWeightedSum_le
  · exact slabCanonicalExteriorRepresentativeFiberEntries_length_le
      representative
  · decide
  · exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
      (Q'.le_of_lt hw0) cutoff half representative.target.1
        representative.target.2
  · intro entry hentry
    have hkey := slabCanonicalExteriorRepresentativeFiberEntry_key_eq
      representative entry hentry
    have hpeel :=
      SlabCanonicalExteriorSourceEntry.peelSize_eq_of_removalKey_eq
        representative entry hkey
    have htarget :=
      SlabCanonicalExteriorSourceEntry.target_eq_of_removalKey_eq
        representative entry hkey
    have hweight :=
      SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_anchorPaidExterior_le
        hw0 hw1 cutoff half entry.component.seed entry.reserve_paid
          entry.source_bounded
    dsimp only at hweight
    have hentryWeight :
        slabExpandedFineSourceWeight
            { coupling := w
              coupling_nonnegative := Q'.le_of_lt hw0
              cutoff := cutoff
              half := half }
            entry.source <=
          anchorFaceCoefficient ^ entry.peelSize *
            slabExpandedFineSourceWeight
              { coupling := w
                coupling_nonnegative := Q'.le_of_lt hw0
                cutoff := cutoff
                half := half }
              entry.target := by
      unfold slabExpandedFineSourceWeight
        SlabCanonicalExteriorSourceEntry.target
      rw [entry.peelSize_eq]
      exact hweight
    calc
      slabExpandedFineSourceWeight
          { coupling := w
            coupling_nonnegative := Q'.le_of_lt hw0
            cutoff := cutoff
            half := half }
          entry.source <=
        anchorFaceCoefficient ^ entry.peelSize *
          slabExpandedFineSourceWeight
            { coupling := w
              coupling_nonnegative := Q'.le_of_lt hw0
              cutoff := cutoff
              half := half }
            entry.target := hentryWeight
      _ = anchorFaceCoefficient ^ representative.peelSize *
          slabExpandedFineSourceWeight
            { coupling := w
              coupling_nonnegative := Q'.le_of_lt hw0
              cutoff := cutoff
              half := half }
            representative.target :=
        (congrArg
          (fun size => anchorFaceCoefficient ^ size *
            slabExpandedFineSourceWeight
              { coupling := w
                coupling_nonnegative := Q'.le_of_lt hw0
                cutoff := cutoff
                half := half }
              entry.target)
          hpeel.symm).trans
        (congrArg
          (fun target => anchorFaceCoefficient ^ representative.peelSize *
            slabExpandedFineSourceWeight
              { coupling := w
                coupling_nonnegative := Q'.le_of_lt hw0
                cutoff := cutoff
                half := half }
              target)
          htarget.symm)

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | item :: items, hbound =>
      Q'.add_le_add
        (hbound item List.mem_cons_self)
        (listQSum_le_termwise_local left right items
          (fun other hother =>
            hbound other (List.mem_cons_of_mem item hother)))

/-- **Total exterior-source contraction with exposed target congestion.**
The complete exterior source weight is bounded by the sum of the strict
component rates times the actual target weights of the realized removal-key
representatives. -/
theorem slabCanonicalExteriorSources_weight_sum_le_target_congestion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) :
    let D := couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half
    let threshold := anchorPaidExteriorThreshold w
    listQSum (slabExpandedFineSourceWeight D)
        (slabCanonicalExteriorSources D threshold) <=
      listQSum
        (fun representative =>
          componentAdaptiveEntropyAnchorRatio ^
              representative.peelSize *
            slabExpandedFineSourceWeight D representative.target)
        (slabCanonicalExteriorRepresentatives D threshold) := by
  dsimp only
  let D := couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half
  let threshold := anchorPaidExteriorThreshold w
  have htotal := slabCanonicalExteriorRepresentativeFibers_weight_total
    D threshold
  have hsum := listQSum_le_termwise_local
    (fun representative =>
      listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.source)
        (slabCanonicalExteriorRepresentativeFiberEntries representative))
    (fun representative =>
      componentAdaptiveEntropyAnchorRatio ^
          representative.peelSize *
        slabExpandedFineSourceWeight D representative.target)
    (slabCanonicalExteriorRepresentatives D threshold)
    (fun representative _ =>
      slabCanonicalExteriorRepresentativeFiber_weight_sum_le
        hw0 hw1 cutoff half representative)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal) hsum

#print axioms SlabCanonicalExteriorSourceEntry
#print axioms SlabCanonicalExteriorSourceEntry.source_mem
#print axioms slabCanonicalExteriorSourceEntryOfDecision?
#print axioms slabCanonicalExteriorSourceEntryOfDecision?_source_eq_of_some
#print axioms slabCanonicalExteriorSourceEntry?
#print axioms slabCanonicalExteriorSourceEntry?_source_eq_of_some
#print axioms slabCanonicalExteriorSourceEntries
#print axioms slabCanonicalExteriorSources
#print axioms slabCanonicalExteriorSources_nodup
#print axioms SlabCanonicalExteriorRemovalKey
#print axioms SlabCanonicalExteriorSourceEntry.target
#print axioms SlabCanonicalExteriorSourceEntry.target_mem
#print axioms SlabCanonicalExteriorSourceEntry.removalKey
#print axioms SlabCanonicalExteriorSourceEntry.target_eq_of_removalKey_eq
#print axioms SlabCanonicalExteriorSourceEntry.rootFaceId_eq_of_removalKey_eq
#print axioms SlabCanonicalExteriorSourceEntry.peelSize_eq_of_removalKey_eq
#print axioms SlabCanonicalExteriorSourceEntry.entropyCode
#print axioms slabCanonicalExteriorRepresentatives
#print axioms slabCanonicalExteriorRepresentativeFiberEntries
#print axioms slabCanonicalExteriorRepresentativeFiberSources
#print axioms slabCanonicalExteriorRepresentativeFiberSources_nodup
#print axioms slabCanonicalExteriorSourceEntry_eq_of_source_eq
#print axioms slabCanonicalExteriorRepresentativeFiberEntry_key_eq
#print axioms SlabCanonicalExteriorSourceEntry.source_bounded
#print axioms slabCanonicalExteriorRepresentativeFiberCodes_nodup
#print axioms slabCanonicalExteriorRepresentativeFiberEntries_length_le
#print axioms couplingSlabPhysicalData
#print axioms slabCanonicalExteriorRepresentativeFibers_weight_total
#print axioms slabCanonicalExteriorRepresentativeFiber_weight_sum_le
#print axioms slabCanonicalExteriorSources_weight_sum_le_target_congestion

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorPartition
