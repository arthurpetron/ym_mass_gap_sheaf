/-
# Sum canonical exterior fibers over distinct component sizes

The complete canonical exterior partition retains one actual representative
for every realized key `(root face, component size, lower target)`.  This
module forgets only the component size and repartitions those representatives
by `(root face, lower target)`.

Inside one such coarser fiber the component sizes are distinct: equality of
the root, target, and size would reproduce the same complete removal key,
contradicting the duplicate-free representative-key list.  Every component
size is positive and lies below the explicit physical strand ceiling.
Consequently its total strict rate injects into the positive geometric series

```text
sum distinct realized n >= 1 of (8/25)^n <= 8/17.
```

Thus all size congestion is removed.  The resulting exterior estimate retains
exactly one target-weight charge for every realized `(lower target, root)`
pair.  Possible congestion over different roots landing on the same target is
left explicit; no volume-uniform target localization, finite-core coercivity,
posterior-variance fraction, or spectral gap is asserted here.

Constructive contract: finite realized-key partitions, an explicit injection
into a finite `List.range`, and exact rational geometric summation only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorPartition
import YMGap.Continuum.CompactDualSlabObservableRemovalGeometric

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorPartition
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalGeometric
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxPacketState

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The coarser lower-target/root key -/

/-- Forget the component size but retain the selected root and exact encoded
lower target. -/
structure SlabCanonicalExteriorTargetRootKey : Type where
  rootFaceId : Nat
  targetKey : SlabExpandedFineTargetKey
  deriving DecidableEq

/-- The coarser key of one complete exterior representative. -/
def slabCanonicalExteriorTargetRootKey
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    SlabCanonicalExteriorTargetRootKey where
  rootFaceId := entry.rootFaceId
  targetKey := slabExpandedFineTargetKey D entry.target.1 entry.target.2

/-- Equal target/root keys recover equal concrete lower targets. -/
theorem slabCanonicalExteriorTarget_eq_of_targetRootKey_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (left right : SlabCanonicalExteriorSourceEntry D threshold)
    (hkey : slabCanonicalExteriorTargetRootKey left =
      slabCanonicalExteriorTargetRootKey right) :
    left.target = right.target :=
  slabExpandedFineTargetKey_eq_source_eq D left.target_mem right.target_mem
    (congrArg SlabCanonicalExteriorTargetRootKey.targetKey hkey)

/-- Equal target/root keys recover equal selected roots. -/
theorem slabCanonicalExteriorRootFaceId_eq_of_targetRootKey_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (left right : SlabCanonicalExteriorSourceEntry D threshold)
    (hkey : slabCanonicalExteriorTargetRootKey left =
      slabCanonicalExteriorTargetRootKey right) :
    left.rootFaceId = right.rootFaceId :=
  congrArg SlabCanonicalExteriorTargetRootKey.rootFaceId hkey

/-- Restoring the component size to an equal target/root key restores the
complete removal key. -/
theorem slabCanonicalExteriorRemovalKey_eq_of_targetRootKey_eq_of_peelSize_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (left right : SlabCanonicalExteriorSourceEntry D threshold)
    (hkey : slabCanonicalExteriorTargetRootKey left =
      slabCanonicalExteriorTargetRootKey right)
    (hsize : left.peelSize = right.peelSize) :
    left.removalKey = right.removalKey := by
  change
    ({ rootFaceId := left.rootFaceId
       peelSize := left.peelSize
       targetKey := slabExpandedFineTargetKey D left.target.1 left.target.2 } :
      SlabCanonicalExteriorRemovalKey) =
    { rootFaceId := right.rootFaceId
      peelSize := right.peelSize
      targetKey := slabExpandedFineTargetKey D right.target.1 right.target.2 }
  have htargetKey :=
    congrArg SlabCanonicalExteriorTargetRootKey.targetKey hkey
  dsimp only [slabCanonicalExteriorTargetRootKey] at htargetKey
  rw [slabCanonicalExteriorRootFaceId_eq_of_targetRootKey_eq left right hkey,
    hsize, htargetKey]

/-! ## 2. Realized target/root fibers -/

/-- One actual complete-key representative for every realized lower-target
and root pair. -/
def slabCanonicalExteriorTargetRootRepresentatives
    (D : SlabPhysicalData) (threshold : Nat) :
    List (SlabCanonicalExteriorSourceEntry D threshold) :=
  keyRepresentatives slabCanonicalExteriorTargetRootKey
    (slabCanonicalExteriorRepresentatives D threshold)

/-- Complete-key representatives having the same lower target and root as one
coarser representative. -/
def slabCanonicalExteriorTargetRootFiberEntries
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    List (SlabCanonicalExteriorSourceEntry D threshold) :=
  representativeFiber (slabCanonicalExteriorRepresentatives D threshold)
    slabCanonicalExteriorTargetRootKey representative

/-- Membership in a target/root fiber gives equality of its coarser key. -/
theorem slabCanonicalExteriorTargetRootFiberEntry_key_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (representative entry : SlabCanonicalExteriorSourceEntry D threshold)
    (hentry : entry ∈
      slabCanonicalExteriorTargetRootFiberEntries representative) :
    slabCanonicalExteriorTargetRootKey representative =
      slabCanonicalExteriorTargetRootKey entry :=
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

/-- Complete exterior representatives have pairwise distinct complete
removal keys. -/
theorem slabCanonicalExteriorRepresentatives_removalKeys_nodup
    (D : SlabPhysicalData) (threshold : Nat) :
    ((slabCanonicalExteriorRepresentatives D threshold).map
      SlabCanonicalExteriorSourceEntry.removalKey).Nodup := by
  unfold slabCanonicalExteriorRepresentatives
  exact keyRepresentatives_keys_nodup
    SlabCanonicalExteriorSourceEntry.removalKey
      (slabCanonicalExteriorSourceEntries D threshold)

/-- A target/root fiber is a duplicate-free list of actual complete-key
representatives. -/
theorem slabCanonicalExteriorTargetRootFiberEntries_nodup
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    (slabCanonicalExteriorTargetRootFiberEntries representative).Nodup := by
  apply List.Sublist.nodup List.filter_sublist
  exact nodup_of_map_nodup SlabCanonicalExteriorSourceEntry.removalKey _
    (slabCanonicalExteriorRepresentatives_removalKeys_nodup D threshold)

/-! ## 3. Distinct positive sizes inject into the geometric tail -/

/-- Every selected exterior component has positive serialized size. -/
theorem slabCanonicalExteriorPeelSize_pos
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    0 < entry.peelSize := by
  rw [entry.peelSize_eq]
  exact SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos
    entry.component.seed

/-- Every selected exterior component lies below the explicit physical strand
ceiling. -/
theorem slabCanonicalExteriorPeelSize_le_removalMaxSize
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    entry.peelSize <= slabObservableRemovalMaxSize D := by
  rw [entry.peelSize_eq]
  exact SlabFusionWitnessFaceStrandSeed.peelFaces_length_le_cutoff
    entry.component.seed entry.source_bounded

/-- Every expanded source weight is nonnegative at arbitrary nonnegative
coupling. -/
theorem slabExpandedFineSourceWeight_nonnegative
    (D : SlabPhysicalData)
    (source : SlabLabelling × SlabFusionWitnessAssignment) :
    (0 : Q') <= slabExpandedFineSourceWeight D source := by
  cases D with
  | mk coupling coupling_nonnegative cutoff half =>
      exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        coupling_nonnegative cutoff half source.1 source.2

/-- **One fixed target/root has no component-size congestion.**  The realized
complete-key rates inject into the finite positive geometric tail and cost at
most `8/17` times the common lower-target weight. -/
theorem slabCanonicalExteriorTargetRootFiber_rate_weight_le
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    listQSum
        (fun entry =>
          componentAdaptiveEntropyAnchorRatio ^ entry.peelSize *
            slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorTargetRootFiberEntries representative) <=
      Q'.mkPos 8 17 (by decide) *
        slabExpandedFineSourceWeight D representative.target := by
  let items := slabCanonicalExteriorTargetRootFiberEntries representative
  let targetWeight := slabExpandedFineSourceWeight D representative.target
  have hcompleteKeys :=
    slabCanonicalExteriorRepresentatives_removalKeys_nodup D threshold
  have hinjected :
      listQSum
          (fun entry =>
            componentAdaptiveEntropyAnchorRatio ^ entry.peelSize *
              slabExpandedFineSourceWeight D entry.target)
          items <=
        listQSum
          (fun index =>
            targetWeight *
              componentAdaptiveEntropyAnchorRatio ^ (index + 1))
          (List.range (slabObservableRemovalMaxSize D)) := by
    apply listQSum_le_of_injective
      items (List.range (slabObservableRemovalMaxSize D))
      (fun entry =>
        componentAdaptiveEntropyAnchorRatio ^ entry.peelSize *
          slabExpandedFineSourceWeight D entry.target)
      (fun index =>
        targetWeight * componentAdaptiveEntropyAnchorRatio ^ (index + 1))
      (fun entry => entry.peelSize - 1)
    · exact slabCanonicalExteriorTargetRootFiberEntries_nodup representative
    · intro entry hentry
      apply List.mem_range.mpr
      have hpos := slabCanonicalExteriorPeelSize_pos entry
      have hle := slabCanonicalExteriorPeelSize_le_removalMaxSize entry
      omega
    · intro left hleft right hright hindex
      have hleftPos := slabCanonicalExteriorPeelSize_pos left
      have hrightPos := slabCanonicalExteriorPeelSize_pos right
      have hsize : left.peelSize = right.peelSize := by omega
      have hleftKey := slabCanonicalExteriorTargetRootFiberEntry_key_eq
        representative left hleft
      have hrightKey := slabCanonicalExteriorTargetRootFiberEntry_key_eq
        representative right hright
      have htargetRoot : slabCanonicalExteriorTargetRootKey left =
          slabCanonicalExteriorTargetRootKey right :=
        hleftKey.symm.trans hrightKey
      have hremoval :=
        slabCanonicalExteriorRemovalKey_eq_of_targetRootKey_eq_of_peelSize_eq
          left right htargetRoot hsize
      apply map_injective_on_of_map_nodup
        SlabCanonicalExteriorSourceEntry.removalKey
        (slabCanonicalExteriorRepresentatives D threshold) hcompleteKeys
      · exact (List.mem_filter.mp hleft).1
      · exact (List.mem_filter.mp hright).1
      · exact hremoval
    · intro entry hentry
      have hkey := slabCanonicalExteriorTargetRootFiberEntry_key_eq
        representative entry hentry
      have htarget := slabCanonicalExteriorTarget_eq_of_targetRootKey_eq
        entry representative hkey.symm
      have hpos := slabCanonicalExteriorPeelSize_pos entry
      have hsize : entry.peelSize = entry.peelSize - 1 + 1 := by omega
      rw [htarget, hsize]
      exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
    · intro index _
      exact Q'.mul_nonneg _ _
        (slabExpandedFineSourceWeight_nonnegative D representative.target)
        (Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio (by decide) _)
  have hfactor :
      listQSum
          (fun index =>
            targetWeight *
              componentAdaptiveEntropyAnchorRatio ^ (index + 1))
          (List.range (slabObservableRemovalMaxSize D)) ≈
        targetWeight *
          listQSum
            (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
            (List.range (slabObservableRemovalMaxSize D)) :=
    listQSum_mul_left targetWeight
      (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
      (List.range (slabObservableRemovalMaxSize D))
  have htail := componentAdaptiveEntropyAnchorRatio_positiveTail_le
    (slabObservableRemovalMaxSize D)
  have htargetWeight : (0 : Q') <= targetWeight :=
    slabExpandedFineSourceWeight_nonnegative D representative.target
  have hscaled :
      targetWeight *
          listQSum
            (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
            (List.range (slabObservableRemovalMaxSize D)) <=
        targetWeight * Q'.mkPos 8 17 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htail htargetWeight
  exact Q'.le_trans' _ _ _ hinjected
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-! ## 4. Exact regrouping and global removal of size congestion -/

/-- Repartitioning complete representatives by target/root recovers their
complete weighted-rate sum exactly. -/
theorem slabCanonicalExteriorTargetRootFibers_rate_weight_total
    (D : SlabPhysicalData) (threshold : Nat) :
    listQSum
        (fun representative =>
          listQSum
            (fun entry =>
              componentAdaptiveEntropyAnchorRatio ^ entry.peelSize *
                slabExpandedFineSourceWeight D entry.target)
            (slabCanonicalExteriorTargetRootFiberEntries representative))
        (slabCanonicalExteriorTargetRootRepresentatives D threshold) ≈
      listQSum
        (fun entry =>
          componentAdaptiveEntropyAnchorRatio ^ entry.peelSize *
            slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorRepresentatives D threshold) := by
  exact keyRepresentativeFibers_weight_total
    (slabCanonicalExteriorRepresentatives D threshold)
    (fun entry =>
      componentAdaptiveEntropyAnchorRatio ^ entry.peelSize *
        slabExpandedFineSourceWeight D entry.target)
    slabCanonicalExteriorTargetRootKey

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

/-- **Global exterior contraction with only root/target congestion left.**
All complete exterior fibers and all realized positive component sizes cost
at most `8/17` times the sum of one concrete lower-target weight for every
realized `(lower target, root)` pair. -/
theorem slabCanonicalExteriorSources_weight_sum_le_target_root_congestion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) :
    let D := couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half
    let threshold := anchorPaidExteriorThreshold w
    listQSum (slabExpandedFineSourceWeight D)
        (slabCanonicalExteriorSources D threshold) <=
      Q'.mkPos 8 17 (by decide) *
        listQSum
          (fun representative =>
            slabExpandedFineSourceWeight D representative.target)
          (slabCanonicalExteriorTargetRootRepresentatives D threshold) := by
  dsimp only
  let D := couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half
  let threshold := anchorPaidExteriorThreshold w
  have hexterior := slabCanonicalExteriorSources_weight_sum_le_target_congestion
    hw0 hw1 cutoff half
  have hpartition :=
    slabCanonicalExteriorTargetRootFibers_rate_weight_total D threshold
  have hgroups := listQSum_le_termwise_local
    (fun representative =>
      listQSum
        (fun entry =>
          componentAdaptiveEntropyAnchorRatio ^ entry.peelSize *
            slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorTargetRootFiberEntries representative))
    (fun representative =>
      Q'.mkPos 8 17 (by decide) *
        slabExpandedFineSourceWeight D representative.target)
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)
    (fun representative _ =>
      slabCanonicalExteriorTargetRootFiber_rate_weight_le representative)
  have hfactor := listQSum_mul_left (Q'.mkPos 8 17 (by decide))
    (fun representative : SlabCanonicalExteriorSourceEntry D threshold =>
      slabExpandedFineSourceWeight D representative.target)
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)
  exact Q'.le_trans' _ _ _ hexterior
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hgroups (Q'.le_of_eqv hfactor)))

#print axioms SlabCanonicalExteriorTargetRootKey
#print axioms slabCanonicalExteriorTargetRootKey
#print axioms slabCanonicalExteriorTarget_eq_of_targetRootKey_eq
#print axioms slabCanonicalExteriorRootFaceId_eq_of_targetRootKey_eq
#print axioms slabCanonicalExteriorRemovalKey_eq_of_targetRootKey_eq_of_peelSize_eq
#print axioms slabCanonicalExteriorTargetRootRepresentatives
#print axioms slabCanonicalExteriorTargetRootFiberEntries
#print axioms slabCanonicalExteriorTargetRootFiberEntry_key_eq
#print axioms slabCanonicalExteriorRepresentatives_removalKeys_nodup
#print axioms slabCanonicalExteriorTargetRootFiberEntries_nodup
#print axioms slabCanonicalExteriorPeelSize_pos
#print axioms slabCanonicalExteriorPeelSize_le_removalMaxSize
#print axioms slabExpandedFineSourceWeight_nonnegative
#print axioms slabCanonicalExteriorTargetRootFiber_rate_weight_le
#print axioms slabCanonicalExteriorTargetRootFibers_rate_weight_total
#print axioms slabCanonicalExteriorSources_weight_sum_le_target_root_congestion

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion
