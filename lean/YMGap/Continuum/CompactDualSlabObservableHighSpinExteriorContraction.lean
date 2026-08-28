/-
# Uniform contraction of the localized observable-rooted exterior branch

The localized high-spin exterior partition retains one representative for
every realized `(lower target, component size)` key.  This module forgets the
size and groups those representatives by lower target.  Within one target
fiber the sizes are distinct, positive, and bounded by the explicit physical
strand ceiling.  Hence their strict rates inject into the positive geometric
tail and sum to at most `8/17`.

The remaining target representatives have distinct exact finite target keys.
Pushing them into the full expanded target-key carrier bounds their total
weight by the physical partition.  Thus, for every rational `0 < w < 1`,

```text
localized observable-rooted exterior weight
  <= (8/17) * physical partition,
```

uniformly in cutoff, slab half-width, and displayed face count.  This controls
only the exterior branch.  The complementary core-blocked observable-rooted
mass, a posterior-variance fraction, and a physical transfer gap remain open.

Constructive contract: realized finite keys, explicit injection into a finite
positive geometric tail, and exact rational pushforward only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
import YMGap.Continuum.CompactDualSlabObservableRemovalGeometric

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalGeometric
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Group complete representatives by lower target -/

/-- Exact lower-target key of one localized complete-key representative. -/
def slabObservableHighSpinExteriorTargetKey
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabExpandedFineTargetKey :=
  slabExpandedFineTargetKey D
    (slabObservableHighSpinExteriorTarget hface entry).1
    (slabObservableHighSpinExteriorTarget hface entry).2

/-- Equal target keys recover equal concrete lower targets. -/
theorem slabObservableHighSpinExteriorTarget_eq_of_targetKey_eq
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservablePositiveSourceEntry D faceId)
    (hkey : slabObservableHighSpinExteriorTargetKey hface left =
      slabObservableHighSpinExteriorTargetKey hface right) :
    slabObservableHighSpinExteriorTarget hface left =
      slabObservableHighSpinExteriorTarget hface right :=
  slabExpandedFineTargetKey_eq_source_eq D
    (slabObservableHighSpinExteriorTarget_mem left)
    (slabObservableHighSpinExteriorTarget_mem right) hkey

/-- An equal lower target and equal component size restore the complete
removal key. -/
theorem slabObservableHighSpinExteriorRemovalKey_eq_of_targetKey_eq_of_peelSize_eq
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservablePositiveSourceEntry D faceId)
    (htarget : slabObservableHighSpinExteriorTargetKey hface left =
      slabObservableHighSpinExteriorTargetKey hface right)
    (hsize : slabObservableHighSpinExteriorPeelSize hface left =
      slabObservableHighSpinExteriorPeelSize hface right) :
    left.removalKey D faceId hface = right.removalKey D faceId hface := by
  change
    ({ targetKey := slabObservableHighSpinExteriorTargetKey hface left
       peelSize := slabObservableHighSpinExteriorPeelSize hface left } :
      SlabExpandedFineRemovalKey) =
    { targetKey := slabObservableHighSpinExteriorTargetKey hface right
      peelSize := slabObservableHighSpinExteriorPeelSize hface right }
  rw [htarget, hsize]

/-- One actual complete-key representative for every realized lower target. -/
def slabObservableHighSpinExteriorTargetRepresentatives
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  keyRepresentatives (slabObservableHighSpinExteriorTargetKey hface)
    (slabObservableHighSpinExteriorRepresentatives
      D faceId hface threshold)

/-- Complete-key representatives landing on the same lower target as one
concrete representative. -/
def slabObservableHighSpinExteriorTargetFiberEntries
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  representativeFiber
    (slabObservableHighSpinExteriorRepresentatives
      D faceId hface threshold)
    (slabObservableHighSpinExteriorTargetKey hface) representative

/-- Membership in a target fiber gives equality of its target key. -/
theorem slabObservableHighSpinExteriorTargetFiberEntry_key_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative entry : SlabObservablePositiveSourceEntry D faceId)
    (hentry : entry ∈
      slabObservableHighSpinExteriorTargetFiberEntries
        (hface := hface) (threshold := threshold) representative) :
    slabObservableHighSpinExteriorTargetKey hface representative =
      slabObservableHighSpinExteriorTargetKey hface entry :=
  of_decide_eq_true (List.mem_filter.mp hentry).2

private theorem nodup_of_map_nodup {A B : Type} (map : A -> B) :
    forall items : List A, (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup map tail hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

private theorem map_injective_on_of_map_nodup
    {A B : Type} (map : A -> B) : forall items : List A,
    (items.map map).Nodup ->
      forall left, left ∈ items -> forall right, right ∈ items ->
        map left = map right -> left = right
  | [], _, left, hleft, _, _, _ => absurd hleft List.not_mem_nil
  | head :: tail, hnodup, left, hleft, right, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hleft with hleftHead | hleftTail
      · subst left
        rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · exact hrightHead.symm
        · exact absurd
            (heq ▸ List.mem_map.mpr ⟨right, hrightTail, rfl⟩)
            hparts.1
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · subst right
          exact absurd
            (heq.symm ▸ List.mem_map.mpr ⟨left, hleftTail, rfl⟩)
            hparts.1
        · exact map_injective_on_of_map_nodup map tail hparts.2
            left hleftTail right hrightTail heq

/-- Localized complete representatives have distinct complete removal keys. -/
theorem slabObservableHighSpinExteriorRepresentatives_removalKeys_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    ((slabObservableHighSpinExteriorRepresentatives
        D faceId hface threshold).map
      (SlabObservablePositiveSourceEntry.removalKey D faceId hface)).Nodup := by
  unfold slabObservableHighSpinExteriorRepresentatives
  exact keyRepresentatives_keys_nodup
    (SlabObservablePositiveSourceEntry.removalKey D faceId hface)
    (slabObservableHighSpinExteriorEntries D faceId hface threshold)

/-- A lower-target fiber is duplicate-free. -/
theorem slabObservableHighSpinExteriorTargetFiberEntries_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    (slabObservableHighSpinExteriorTargetFiberEntries
      (hface := hface) (threshold := threshold) representative).Nodup := by
  apply List.Sublist.nodup List.filter_sublist
  exact nodup_of_map_nodup
    (SlabObservablePositiveSourceEntry.removalKey D faceId hface) _
    (slabObservableHighSpinExteriorRepresentatives_removalKeys_nodup
      D faceId hface threshold)

/-! ## 2. Distinct positive component sizes cost at most 8/17 -/

/-- Every localized observable-rooted component has positive size. -/
theorem slabObservableHighSpinExteriorPeelSize_pos
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    0 < slabObservableHighSpinExteriorPeelSize hface entry :=
  SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos
    (entry.seed D faceId hface)

/-- Every localized component size lies below the physical strand ceiling. -/
theorem slabObservableHighSpinExteriorPeelSize_le_removalMaxSize
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    slabObservableHighSpinExteriorPeelSize hface entry <=
      slabObservableRemovalMaxSize D :=
  SlabFusionWitnessFaceStrandSeed.peelFaces_length_le_cutoff
    (entry.seed D faceId hface)
    (slabObservableHighSpinExteriorEntry_bounded entry)

/-- Expanded source weights are nonnegative at arbitrary nonnegative
coupling. -/
theorem slabObservableExpandedFineSourceWeight_nonnegative
    (D : SlabPhysicalData)
    (source : SlabLabelling × SlabFusionWitnessAssignment) :
    (0 : Q') <= slabExpandedFineSourceWeight D source := by
  cases D with
  | mk coupling coupling_nonnegative cutoff half =>
      exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        coupling_nonnegative cutoff half source.1 source.2

/-- One fixed lower target has no residual component-size congestion. -/
theorem slabObservableHighSpinExteriorTargetFiber_rate_weight_le
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    listQSum
        (fun entry =>
          componentAdaptiveEntropyAnchorRatio ^
              slabObservableHighSpinExteriorPeelSize hface entry *
            slabExpandedFineSourceWeight D
              (slabObservableHighSpinExteriorTarget hface entry))
        (slabObservableHighSpinExteriorTargetFiberEntries
          (hface := hface) (threshold := threshold) representative) <=
      Q'.mkPos 8 17 (by decide) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinExteriorTarget hface representative) := by
  let items := slabObservableHighSpinExteriorTargetFiberEntries
    (hface := hface) (threshold := threshold) representative
  let targetWeight := slabExpandedFineSourceWeight D
    (slabObservableHighSpinExteriorTarget hface representative)
  have hcompleteKeys :=
    slabObservableHighSpinExteriorRepresentatives_removalKeys_nodup
      D faceId hface threshold
  have hinjected :
      listQSum
          (fun entry =>
            componentAdaptiveEntropyAnchorRatio ^
                slabObservableHighSpinExteriorPeelSize hface entry *
              slabExpandedFineSourceWeight D
                (slabObservableHighSpinExteriorTarget hface entry))
          items <=
        listQSum
          (fun index => targetWeight *
            componentAdaptiveEntropyAnchorRatio ^ (index + 1))
          (List.range (slabObservableRemovalMaxSize D)) := by
    apply listQSum_le_of_injective
      items (List.range (slabObservableRemovalMaxSize D))
      (fun entry =>
        componentAdaptiveEntropyAnchorRatio ^
            slabObservableHighSpinExteriorPeelSize hface entry *
          slabExpandedFineSourceWeight D
            (slabObservableHighSpinExteriorTarget hface entry))
      (fun index => targetWeight *
        componentAdaptiveEntropyAnchorRatio ^ (index + 1))
      (fun entry => slabObservableHighSpinExteriorPeelSize hface entry - 1)
    · exact slabObservableHighSpinExteriorTargetFiberEntries_nodup
        representative
    · intro entry hentry
      apply List.mem_range.mpr
      have hpos := slabObservableHighSpinExteriorPeelSize_pos hface entry
      have hle :=
        slabObservableHighSpinExteriorPeelSize_le_removalMaxSize hface entry
      omega
    · intro left hleft right hright hindex
      have hleftPos := slabObservableHighSpinExteriorPeelSize_pos hface left
      have hrightPos := slabObservableHighSpinExteriorPeelSize_pos hface right
      have hsize : slabObservableHighSpinExteriorPeelSize hface left =
          slabObservableHighSpinExteriorPeelSize hface right := by omega
      have hleftTarget := slabObservableHighSpinExteriorTargetFiberEntry_key_eq
        representative left hleft
      have hrightTarget := slabObservableHighSpinExteriorTargetFiberEntry_key_eq
        representative right hright
      have htarget : slabObservableHighSpinExteriorTargetKey hface left =
          slabObservableHighSpinExteriorTargetKey hface right :=
        hleftTarget.symm.trans hrightTarget
      have hremoval :=
        slabObservableHighSpinExteriorRemovalKey_eq_of_targetKey_eq_of_peelSize_eq
          hface left right htarget hsize
      apply map_injective_on_of_map_nodup
        (SlabObservablePositiveSourceEntry.removalKey D faceId hface)
        (slabObservableHighSpinExteriorRepresentatives
          D faceId hface threshold) hcompleteKeys
      · exact (List.mem_filter.mp hleft).1
      · exact (List.mem_filter.mp hright).1
      · exact hremoval
    · intro entry hentry
      have hkey := slabObservableHighSpinExteriorTargetFiberEntry_key_eq
        representative entry hentry
      have htarget := slabObservableHighSpinExteriorTarget_eq_of_targetKey_eq
        hface entry representative hkey.symm
      have hpos := slabObservableHighSpinExteriorPeelSize_pos hface entry
      have hsize : slabObservableHighSpinExteriorPeelSize hface entry =
          slabObservableHighSpinExteriorPeelSize hface entry - 1 + 1 := by
        omega
      rw [htarget, hsize]
      exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
    · intro index _
      exact Q'.mul_nonneg _ _
        (slabObservableExpandedFineSourceWeight_nonnegative D
          (slabObservableHighSpinExteriorTarget hface representative))
        (Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio (by decide) _)
  have hfactor := listQSum_mul_left targetWeight
    (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
    (List.range (slabObservableRemovalMaxSize D))
  have htail := componentAdaptiveEntropyAnchorRatio_positiveTail_le
    (slabObservableRemovalMaxSize D)
  have htargetNonnegative : (0 : Q') <= targetWeight :=
    slabObservableExpandedFineSourceWeight_nonnegative D
      (slabObservableHighSpinExteriorTarget hface representative)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ targetWeight
    htail htargetNonnegative
  exact Q'.le_trans' _ _ _ hinjected
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-! ## 3. Regrouping and contraction against the physical partition -/

/-- Target fibers exactly recover the complete representative rate sum. -/
theorem slabObservableHighSpinExteriorTargetFibers_rate_weight_total
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    listQSum
        (fun representative =>
          listQSum
            (fun entry =>
              componentAdaptiveEntropyAnchorRatio ^
                  slabObservableHighSpinExteriorPeelSize hface entry *
                slabExpandedFineSourceWeight D
                  (slabObservableHighSpinExteriorTarget hface entry))
            (slabObservableHighSpinExteriorTargetFiberEntries
              (hface := hface) (threshold := threshold) representative))
        (slabObservableHighSpinExteriorTargetRepresentatives
          D faceId hface threshold) ≈
      listQSum
        (fun entry =>
          componentAdaptiveEntropyAnchorRatio ^
              slabObservableHighSpinExteriorPeelSize hface entry *
            slabExpandedFineSourceWeight D
              (slabObservableHighSpinExteriorTarget hface entry))
        (slabObservableHighSpinExteriorRepresentatives
          D faceId hface threshold) := by
  exact keyRepresentativeFibers_weight_total
    (slabObservableHighSpinExteriorRepresentatives
      D faceId hface threshold)
    (fun entry =>
      componentAdaptiveEntropyAnchorRatio ^
          slabObservableHighSpinExteriorPeelSize hface entry *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinExteriorTarget hface entry))
    (slabObservableHighSpinExteriorTargetKey hface)

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

/-- Localized exterior weight is at most `8/17` times one charge per realized
lower target. -/
theorem slabObservableHighSpinExteriorSources_weight_sum_le_target_weights
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservableHighSpinExteriorSources D faceId hface
          (anchorPaidExteriorThreshold w)) <=
      Q'.mkPos 8 17 (by decide) *
        listQSum
          (fun representative => slabExpandedFineSourceWeight D
            (slabObservableHighSpinExteriorTarget hface representative))
          (slabObservableHighSpinExteriorTargetRepresentatives
            D faceId hface (anchorPaidExteriorThreshold w)) := by
  have hexterior :=
    slabObservableHighSpinExteriorSources_weight_sum_le_target_congestion
      hw0 hw1 cutoff half D hD faceId hface
  have hpartition :=
    slabObservableHighSpinExteriorTargetFibers_rate_weight_total
      D faceId hface (anchorPaidExteriorThreshold w)
  have hgroups := listQSum_le_termwise_local
    (fun representative =>
      listQSum
        (fun entry =>
          componentAdaptiveEntropyAnchorRatio ^
              slabObservableHighSpinExteriorPeelSize hface entry *
            slabExpandedFineSourceWeight D
              (slabObservableHighSpinExteriorTarget hface entry))
        (slabObservableHighSpinExteriorTargetFiberEntries
          (hface := hface) (threshold := anchorPaidExteriorThreshold w)
            representative))
    (fun representative => Q'.mkPos 8 17 (by decide) *
      slabExpandedFineSourceWeight D
        (slabObservableHighSpinExteriorTarget hface representative))
    (slabObservableHighSpinExteriorTargetRepresentatives
      D faceId hface (anchorPaidExteriorThreshold w))
    (fun representative _ =>
      slabObservableHighSpinExteriorTargetFiber_rate_weight_le representative)
  have hfactor := listQSum_mul_left (Q'.mkPos 8 17 (by decide))
    (fun representative : SlabObservablePositiveSourceEntry D faceId =>
      slabExpandedFineSourceWeight D
        (slabObservableHighSpinExteriorTarget hface representative))
    (slabObservableHighSpinExteriorTargetRepresentatives
      D faceId hface (anchorPaidExteriorThreshold w))
  exact Q'.le_trans' _ _ _ hexterior
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hgroups (Q'.le_of_eqv hfactor)))

/-- Target representatives have pairwise distinct exact target keys. -/
theorem slabObservableHighSpinExteriorTargetRepresentatives_keys_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    ((slabObservableHighSpinExteriorTargetRepresentatives
        D faceId hface threshold).map
      (slabObservableHighSpinExteriorTargetKey hface)).Nodup := by
  unfold slabObservableHighSpinExteriorTargetRepresentatives
  exact keyRepresentatives_keys_nodup
    (slabObservableHighSpinExteriorTargetKey hface)
    (slabObservableHighSpinExteriorRepresentatives
      D faceId hface threshold)

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A -> Q')
    (hvalue : forall item, (0 : Q') <= value item) :
    forall (items : List A) {selected : A},
      selected ∈ items -> value selected <= listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe : listQSum value tail <=
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih htailLe

/-- One representative per realized lower target has total weight at most the
full expanded physical partition. -/
theorem slabObservableHighSpinExteriorTargetRepresentatives_weight_le_partition
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    listQSum
        (fun representative => slabExpandedFineSourceWeight D
          (slabObservableHighSpinExteriorTarget hface representative))
        (slabObservableHighSpinExteriorTargetRepresentatives
          D faceId hface threshold) <=
      D.physicalPartition := by
  let representatives := slabObservableHighSpinExteriorTargetRepresentatives
    D faceId hface threshold
  have hrepresentatives : representatives.Nodup :=
    nodup_of_map_nodup (slabObservableHighSpinExteriorTargetKey hface)
      representatives
      (slabObservableHighSpinExteriorTargetRepresentatives_keys_nodup
        D faceId hface threshold)
  have hsum :
      listQSum
          (fun representative => slabExpandedFineSourceWeight D
            (slabObservableHighSpinExteriorTarget hface representative))
          representatives <=
        listQSum
          (fiberWeight (slabExpandedFineSources D)
            (slabExpandedFineSourceWeight D)
            (fun source => slabExpandedFineTargetKey D source.1 source.2))
          (slabExpandedFineTargetKeys D) := by
    apply listQSum_le_of_injective
      representatives (slabExpandedFineTargetKeys D)
      (fun representative => slabExpandedFineSourceWeight D
        (slabObservableHighSpinExteriorTarget hface representative))
      (fiberWeight (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (fun source => slabExpandedFineTargetKey D source.1 source.2))
      (slabObservableHighSpinExteriorTargetKey hface)
    · exact hrepresentatives
    · intro representative _
      unfold slabObservableHighSpinExteriorTargetKey
        slabExpandedFineTargetKeys
      exact List.mem_map.mpr
        ⟨slabObservableHighSpinExteriorTarget hface representative,
          slabObservableHighSpinExteriorTarget_mem representative, rfl⟩
    · intro left hleft right hright hkey
      exact map_injective_on_of_map_nodup
        (slabObservableHighSpinExteriorTargetKey hface) representatives
        (slabObservableHighSpinExteriorTargetRepresentatives_keys_nodup
          D faceId hface threshold)
        left hleft right hright hkey
    · intro representative _
      apply listQSum_member_le_nonnegative_local
        (slabExpandedFineSourceWeight D)
        (slabObservableExpandedFineSourceWeight_nonnegative D)
      apply List.mem_filter.mpr
      refine ⟨slabObservableHighSpinExteriorTarget_mem representative, ?_⟩
      apply decide_eq_true
      rfl
    · intro key _
      exact fiberWeight_nonnegative
        (slabExpandedFineSources D) (slabExpandedFineSourceWeight D)
        (fun source => slabExpandedFineTargetKey D source.1 source.2) key
        (fun source _ =>
          slabObservableExpandedFineSourceWeight_nonnegative D source)
  have hfiberTotal := fiberWeight_total
    (slabExpandedFineSources D) (slabExpandedFineSourceWeight D)
    (fun source => slabExpandedFineTargetKey D source.1 source.2)
    (slabExpandedFineTargetKeys D) (slabExpandedFineTargetKeys_nodup D)
    (fun source hsource => by
      unfold slabExpandedFineTargetKeys
      exact List.mem_map.mpr ⟨source, hsource, rfl⟩)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hfiberTotal
        (slabExpandedFineSources_weight_total D)))

/-- **Uniform localized exterior contraction.**  The fixed observable root
removes volume congestion, while the positive geometric tail removes cutoff
and size congestion. -/
theorem slabObservableHighSpinExteriorSources_weight_sum_le_partition
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservableHighSpinExteriorSources D faceId hface
          (anchorPaidExteriorThreshold w)) <=
      Q'.mkPos 8 17 (by decide) * D.physicalPartition := by
  have htargets :=
    slabObservableHighSpinExteriorSources_weight_sum_le_target_weights
      hw0 hw1 cutoff half D hD faceId hface
  have htargetTotal :=
    slabObservableHighSpinExteriorTargetRepresentatives_weight_le_partition
      D faceId hface (anchorPaidExteriorThreshold w)
  have hratioNonnegative : (0 : Q') <= Q'.mkPos 8 17 (by decide) := by
    decide
  exact Q'.le_trans' _ _ _ htargets
    (Q'.mul_le_mul_of_nonneg_left _ _ _ htargetTotal hratioNonnegative)

#print axioms slabObservableHighSpinExteriorTargetKey
#print axioms slabObservableHighSpinExteriorTarget_eq_of_targetKey_eq
#print axioms slabObservableHighSpinExteriorRemovalKey_eq_of_targetKey_eq_of_peelSize_eq
#print axioms slabObservableHighSpinExteriorTargetRepresentatives
#print axioms slabObservableHighSpinExteriorTargetFiberEntries
#print axioms slabObservableHighSpinExteriorTargetFiberEntry_key_eq
#print axioms slabObservableHighSpinExteriorRepresentatives_removalKeys_nodup
#print axioms slabObservableHighSpinExteriorTargetFiberEntries_nodup
#print axioms slabObservableHighSpinExteriorPeelSize_pos
#print axioms slabObservableHighSpinExteriorPeelSize_le_removalMaxSize
#print axioms slabObservableExpandedFineSourceWeight_nonnegative
#print axioms slabObservableHighSpinExteriorTargetFiber_rate_weight_le
#print axioms slabObservableHighSpinExteriorTargetFibers_rate_weight_total
#print axioms slabObservableHighSpinExteriorSources_weight_sum_le_target_weights
#print axioms slabObservableHighSpinExteriorTargetRepresentatives_keys_nodup
#print axioms slabObservableHighSpinExteriorTargetRepresentatives_weight_le_partition
#print axioms slabObservableHighSpinExteriorSources_weight_sum_le_partition

end YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
