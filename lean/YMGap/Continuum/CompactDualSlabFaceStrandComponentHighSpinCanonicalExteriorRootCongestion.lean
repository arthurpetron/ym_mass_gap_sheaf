/-
# Expose the residual root congestion of canonical exterior peeling

After component-size summation, the canonical exterior estimate retains one
lower-target charge for each realized `(target, root)` pair.  This module
groups those pairs by target.  Their roots are distinct physical faces, hence
there are at most as many as the displayed corrected-slab faces.

The resulting finite-volume bound is exact about the obstruction:

```text
exterior source weight
  <= (8/17) * (# physical faces) * physical partition.
```

This is not a uniform estimate.  It proves that the present global
"first exterior component" classifier has removed size/cutoff congestion but
still pays an explicit volume-growing root factor.  A later uniform argument
must localize or charge that root to the observable/target geometry rather
than erase the factor by assertion.

Constructive contract: finite realized-key partitions, duplicate-free root
injection, and nonnegative rational summation only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorRootCongestion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorPartition
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Repartition target/root representatives by target alone -/

/-- Exact decidable lower-target key, forgetting the selected root. -/
def slabCanonicalExteriorTargetKey
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    SlabExpandedFineTargetKey :=
  slabExpandedFineTargetKey D entry.target.1 entry.target.2

/-- Equal target keys recover equal concrete lower target pairs. -/
theorem slabCanonicalExteriorTarget_eq_of_targetKey_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (left right : SlabCanonicalExteriorSourceEntry D threshold)
    (hkey : slabCanonicalExteriorTargetKey left =
      slabCanonicalExteriorTargetKey right) :
    left.target = right.target :=
  slabExpandedFineTargetKey_eq_source_eq D left.target_mem right.target_mem hkey

/-- One actual target/root representative for every realized lower target. -/
def slabCanonicalExteriorTargetRepresentatives
    (D : SlabPhysicalData) (threshold : Nat) :
    List (SlabCanonicalExteriorSourceEntry D threshold) :=
  keyRepresentatives slabCanonicalExteriorTargetKey
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)

/-- The realized target/root pairs landing on one concrete lower target. -/
def slabCanonicalExteriorTargetFiberEntries
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    List (SlabCanonicalExteriorSourceEntry D threshold) :=
  representativeFiber
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)
    slabCanonicalExteriorTargetKey representative

/-- Membership in a target fiber gives equality of its exact target key. -/
theorem slabCanonicalExteriorTargetFiberEntry_key_eq
    {D : SlabPhysicalData} {threshold : Nat}
    (representative entry : SlabCanonicalExteriorSourceEntry D threshold)
    (hentry : entry ∈ slabCanonicalExteriorTargetFiberEntries representative) :
    slabCanonicalExteriorTargetKey representative =
      slabCanonicalExteriorTargetKey entry :=
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

/-- Target/root representatives have pairwise distinct target/root keys. -/
theorem slabCanonicalExteriorTargetRootRepresentatives_keys_nodup
    (D : SlabPhysicalData) (threshold : Nat) :
    ((slabCanonicalExteriorTargetRootRepresentatives D threshold).map
      slabCanonicalExteriorTargetRootKey).Nodup := by
  unfold slabCanonicalExteriorTargetRootRepresentatives
  exact keyRepresentatives_keys_nodup slabCanonicalExteriorTargetRootKey
    (slabCanonicalExteriorRepresentatives D threshold)

/-- A target fiber is a duplicate-free sublist of the realized target/root
representatives. -/
theorem slabCanonicalExteriorTargetFiberEntries_nodup
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    (slabCanonicalExteriorTargetFiberEntries representative).Nodup := by
  apply List.Sublist.nodup List.filter_sublist
  exact nodup_of_map_nodup slabCanonicalExteriorTargetRootKey _
    (slabCanonicalExteriorTargetRootRepresentatives_keys_nodup D threshold)

/-! ## 2. Distinct roots inject into the physical face list -/

/-- The selected canonical component root is an actual corrected-slab
physical face. -/
theorem slabCanonicalExteriorRootFaceId_mem_physical
    {D : SlabPhysicalData} {threshold : Nat}
    (entry : SlabCanonicalExteriorSourceEntry D threshold) :
    entry.rootFaceId ∈ D.faceEdges := by
  rw [entry.rootFaceId_eq]
  apply SlabFusionWitnessFaceStrandSeed.component_faceId_physical
    entry.component.seed entry.component.seed.root
  unfold SlabFaceStrandSeed.component
  exact root_mem_rootComponent _ entry.component.seed.root_mem

/-- Within one lower-target fiber, the realized selected roots are
duplicate-free. -/
theorem slabCanonicalExteriorTargetFiber_rootFaceIds_nodup
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    ((slabCanonicalExteriorTargetFiberEntries representative).map
      SlabCanonicalExteriorSourceEntry.rootFaceId).Nodup := by
  let items := slabCanonicalExteriorTargetFiberEntries representative
  have hitems : items.Nodup :=
    slabCanonicalExteriorTargetFiberEntries_nodup representative
  apply nodup_map_of_injOn SlabCanonicalExteriorSourceEntry.rootFaceId
    items hitems
  intro left hleft right hright hroot
  have hleftTarget := slabCanonicalExteriorTargetFiberEntry_key_eq
    representative left hleft
  have hrightTarget := slabCanonicalExteriorTargetFiberEntry_key_eq
    representative right hright
  have htarget : slabCanonicalExteriorTargetKey left =
      slabCanonicalExteriorTargetKey right :=
    hleftTarget.symm.trans hrightTarget
  have htargetRoot : slabCanonicalExteriorTargetRootKey left =
      slabCanonicalExteriorTargetRootKey right := by
    change
      ({ rootFaceId := left.rootFaceId
         targetKey := slabCanonicalExteriorTargetKey left } :
        SlabCanonicalExteriorTargetRootKey) =
      { rootFaceId := right.rootFaceId
        targetKey := slabCanonicalExteriorTargetKey right }
    rw [hroot, htarget]
  apply map_injective_on_of_map_nodup slabCanonicalExteriorTargetRootKey
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)
    (slabCanonicalExteriorTargetRootRepresentatives_keys_nodup D threshold)
  · exact (List.mem_filter.mp hleft).1
  · exact (List.mem_filter.mp hright).1
  · exact htargetRoot

/-- One lower target receives at most one charge per physical face. -/
theorem slabCanonicalExteriorTargetFiberEntries_length_le_faces
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    (slabCanonicalExteriorTargetFiberEntries representative).length <=
      D.faceEdges.length := by
  let items := slabCanonicalExteriorTargetFiberEntries representative
  have hbound := nodup_subset_length_le
    (items.map SlabCanonicalExteriorSourceEntry.rootFaceId) D.faceEdges
    (slabCanonicalExteriorTargetFiber_rootFaceIds_nodup representative)
    (fun root hroot => by
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hroot
      exact slabCanonicalExteriorRootFaceId_mem_physical entry)
  simpa only [List.length_map] using hbound

/-- The repeated common target weight in one target fiber costs at most the
number of physical faces times that target weight. -/
theorem slabCanonicalExteriorTargetFiber_weight_le_faces
    {D : SlabPhysicalData} {threshold : Nat}
    (representative : SlabCanonicalExteriorSourceEntry D threshold) :
    listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorTargetFiberEntries representative) <=
      Q'.ofNat D.faceEdges.length *
        slabExpandedFineSourceWeight D representative.target := by
  let items := slabCanonicalExteriorTargetFiberEntries representative
  let targetWeight := slabExpandedFineSourceWeight D representative.target
  have htargetNonnegative : (0 : Q') <= targetWeight :=
    slabExpandedFineSourceWeight_nonnegative D representative.target
  have hsum := listQSum_le_length_mul
    (fun entry => slabExpandedFineSourceWeight D entry.target)
    htargetNonnegative items
    (fun entry hentry => by
      have hkey := slabCanonicalExteriorTargetFiberEntry_key_eq
        representative entry hentry
      have htarget := slabCanonicalExteriorTarget_eq_of_targetKey_eq
        representative entry hkey
      dsimp only [targetWeight]
      rw [← htarget]
      exact Q'.le_refl' _)
  have hlengthQ : Q'.ofNat items.length <= Q'.ofNat D.faceEdges.length :=
    Q'.ofNat_le_ofNat
      (slabCanonicalExteriorTargetFiberEntries_length_le_faces representative)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.mul_le_mul_of_nonneg_right _ _ targetWeight hlengthQ
      htargetNonnegative)

/-! ## 3. Exact target regrouping and the finite-volume obstruction -/

/-- Regrouping target/root representatives by target recovers their total
target-weight charge exactly. -/
theorem slabCanonicalExteriorTargetFibers_weight_total
    (D : SlabPhysicalData) (threshold : Nat) :
    listQSum
        (fun representative =>
          listQSum
            (fun entry => slabExpandedFineSourceWeight D entry.target)
            (slabCanonicalExteriorTargetFiberEntries representative))
        (slabCanonicalExteriorTargetRepresentatives D threshold) ≈
      listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorTargetRootRepresentatives D threshold) := by
  exact keyRepresentativeFibers_weight_total
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)
    (fun entry => slabExpandedFineSourceWeight D entry.target)
    slabCanonicalExteriorTargetKey

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

/-- The complete target/root charge is at most the physical-face count times
one charge per realized lower target. -/
theorem slabCanonicalExteriorTargetRootWeights_le_faces_mul_targetWeights
    (D : SlabPhysicalData) (threshold : Nat) :
    listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorTargetRootRepresentatives D threshold) <=
      Q'.ofNat D.faceEdges.length *
        listQSum
          (fun entry => slabExpandedFineSourceWeight D entry.target)
          (slabCanonicalExteriorTargetRepresentatives D threshold) := by
  have hpartition := slabCanonicalExteriorTargetFibers_weight_total
    D threshold
  have hgroups := listQSum_le_termwise_local
    (fun representative =>
      listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorTargetFiberEntries representative))
    (fun representative =>
      Q'.ofNat D.faceEdges.length *
        slabExpandedFineSourceWeight D representative.target)
    (slabCanonicalExteriorTargetRepresentatives D threshold)
    (fun representative _ =>
      slabCanonicalExteriorTargetFiber_weight_le_faces representative)
  have hfactor := listQSum_mul_left (Q'.ofNat D.faceEdges.length)
    (fun entry : SlabCanonicalExteriorSourceEntry D threshold =>
      slabExpandedFineSourceWeight D entry.target)
    (slabCanonicalExteriorTargetRepresentatives D threshold)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpartition)
    (Q'.le_trans' _ _ _ hgroups (Q'.le_of_eqv hfactor))

/-- Target representatives have pairwise distinct exact target keys. -/
theorem slabCanonicalExteriorTargetRepresentatives_keys_nodup
    (D : SlabPhysicalData) (threshold : Nat) :
    ((slabCanonicalExteriorTargetRepresentatives D threshold).map
      slabCanonicalExteriorTargetKey).Nodup := by
  unfold slabCanonicalExteriorTargetRepresentatives
  exact keyRepresentatives_keys_nodup slabCanonicalExteriorTargetKey
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)

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
theorem slabCanonicalExteriorTargetRepresentatives_weight_le_partition
    (D : SlabPhysicalData) (threshold : Nat) :
    listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.target)
        (slabCanonicalExteriorTargetRepresentatives D threshold) <=
      D.physicalPartition := by
  let representatives := slabCanonicalExteriorTargetRepresentatives D threshold
  have hrepresentatives : representatives.Nodup :=
    nodup_of_map_nodup slabCanonicalExteriorTargetKey representatives
      (slabCanonicalExteriorTargetRepresentatives_keys_nodup D threshold)
  have hsum :
      listQSum
          (fun entry => slabExpandedFineSourceWeight D entry.target)
          representatives <=
        listQSum
          (fiberWeight (slabExpandedFineSources D)
            (slabExpandedFineSourceWeight D)
            (fun source => slabExpandedFineTargetKey D source.1 source.2))
          (slabExpandedFineTargetKeys D) := by
    apply listQSum_le_of_injective
      representatives (slabExpandedFineTargetKeys D)
      (fun entry => slabExpandedFineSourceWeight D entry.target)
      (fiberWeight (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (fun source => slabExpandedFineTargetKey D source.1 source.2))
      slabCanonicalExteriorTargetKey
    · exact hrepresentatives
    · intro entry _
      unfold slabCanonicalExteriorTargetKey slabExpandedFineTargetKeys
      exact List.mem_map.mpr ⟨entry.target, entry.target_mem, rfl⟩
    · intro left hleft right hright hkey
      exact map_injective_on_of_map_nodup slabCanonicalExteriorTargetKey
        representatives
        (slabCanonicalExteriorTargetRepresentatives_keys_nodup D threshold)
        left hleft right hright hkey
    · intro entry _
      apply listQSum_member_le_nonnegative_local
        (slabExpandedFineSourceWeight D)
        (slabExpandedFineSourceWeight_nonnegative D)
      apply List.mem_filter.mpr
      refine ⟨entry.target_mem, ?_⟩
      apply decide_eq_true
      rfl
    · intro key _
      exact fiberWeight_nonnegative
        (slabExpandedFineSources D) (slabExpandedFineSourceWeight D)
        (fun source => slabExpandedFineTargetKey D source.1 source.2) key
        (fun source _ => slabExpandedFineSourceWeight_nonnegative D source)
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

/-- **Finite-volume diagnosis of the residual global root congestion.**  The
canonical exterior compiler is cutoff-independent after size summation, but
its present global root choice leaves the explicit number of slab faces. -/
theorem slabCanonicalExteriorSources_weight_sum_le_volume_factor_partition
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) :
    let D := couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half
    let threshold := anchorPaidExteriorThreshold w
    listQSum (slabExpandedFineSourceWeight D)
        (slabCanonicalExteriorSources D threshold) <=
      Q'.mkPos 8 17 (by decide) *
        (Q'.ofNat D.faceEdges.length * D.physicalPartition) := by
  dsimp only
  let D := couplingSlabPhysicalData w (Q'.le_of_lt hw0) cutoff half
  let threshold := anchorPaidExteriorThreshold w
  let rootWeight := listQSum
    (fun entry => slabExpandedFineSourceWeight D entry.target)
    (slabCanonicalExteriorTargetRootRepresentatives D threshold)
  let targetWeight := listQSum
    (fun entry => slabExpandedFineSourceWeight D entry.target)
    (slabCanonicalExteriorTargetRepresentatives D threshold)
  have hexterior :=
    slabCanonicalExteriorSources_weight_sum_le_target_root_congestion
      hw0 hw1 cutoff half
  have hroot :=
    slabCanonicalExteriorTargetRootWeights_le_faces_mul_targetWeights
      D threshold
  have htarget :=
    slabCanonicalExteriorTargetRepresentatives_weight_le_partition D threshold
  have hfaceNonnegative : (0 : Q') <= Q'.ofNat D.faceEdges.length :=
    Q'.ofNat_nonneg _
  have htargetScaled :
      Q'.ofNat D.faceEdges.length * targetWeight <=
        Q'.ofNat D.faceEdges.length * D.physicalPartition :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htarget hfaceNonnegative
  have hrootTotal : rootWeight <=
      Q'.ofNat D.faceEdges.length * D.physicalPartition :=
    Q'.le_trans' _ _ _ hroot htargetScaled
  have hratioNonnegative :
      (0 : Q') <= Q'.mkPos 8 17 (by decide) := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 8 17 (by decide)) hrootTotal hratioNonnegative
  exact Q'.le_trans' _ _ _ hexterior hscaled

#print axioms slabCanonicalExteriorTargetKey
#print axioms slabCanonicalExteriorTarget_eq_of_targetKey_eq
#print axioms slabCanonicalExteriorTargetRepresentatives
#print axioms slabCanonicalExteriorTargetFiberEntries
#print axioms slabCanonicalExteriorTargetFiberEntry_key_eq
#print axioms slabCanonicalExteriorTargetRootRepresentatives_keys_nodup
#print axioms slabCanonicalExteriorTargetFiberEntries_nodup
#print axioms slabCanonicalExteriorRootFaceId_mem_physical
#print axioms slabCanonicalExteriorTargetFiber_rootFaceIds_nodup
#print axioms slabCanonicalExteriorTargetFiberEntries_length_le_faces
#print axioms slabCanonicalExteriorTargetFiber_weight_le_faces
#print axioms slabCanonicalExteriorTargetFibers_weight_total
#print axioms slabCanonicalExteriorTargetRootWeights_le_faces_mul_targetWeights
#print axioms slabCanonicalExteriorTargetRepresentatives_keys_nodup
#print axioms slabCanonicalExteriorTargetRepresentatives_weight_le_partition
#print axioms slabCanonicalExteriorSources_weight_sum_le_volume_factor_partition

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorRootCongestion
