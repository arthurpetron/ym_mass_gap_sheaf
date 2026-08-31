/-
# Aggregate retained floor for the guarded reflected-bent row family

One representative of every accepted guarded row was selected and its full
accepted-background fiber was paid into a scaled successful connected row.
This module completes the remaining finite composition.  The representative
rows are flattened, partitioned by their actual final observable target, and
bounded target by target by the already proved guarded provenance-code column
capacity.  Exact preservation of the two-replica Gibbs weight then gives one
aggregate lower bound against the complete opposite determinant cell.

Each representative target fiber is compared by the identity injection with
the already compiled actual guarded source-choice column.  Completeness is
used only to prove list membership, so no proposition-only witness is ever
selected into `Type`.

Constructive contract: finite structural lists, explicit proof-carrying target
preimages, exact `Q'` weights, and previously proved receiver capacity only.
No `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedRowPartition

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateRetainedFloor

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedDecoderColumnCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedRowPartition
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedCodeFiberCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedRowCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private def expandedEntryDecidableEq
    (D : SlabPhysicalData) : DecidableEq (SlabExpandedFineSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (SlabExpandedFineSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey
        (congrArg SlabExpandedFineSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (SlabExpandedFineSourceEntry D) :=
  expandedEntryDecidableEq D

local instance aggregateTargetPairDecidableEq
    (D : SlabPhysicalData) :
    DecidableEq (SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D reflectedBentRootFaceId

private theorem nodup_map_of_map_key_nodup_local
    {A B Key : Type} (value : A → B) (key : A → Key)
    (hreflect : ∀ left right, value left = value right →
      key left = key right) :
    ∀ items : List A, (items.map key).Nodup →
      (items.map value).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hkeys => by
      have hparts := List.nodup_cons.mp hkeys
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        apply hparts.1
        exact List.mem_map.mpr
          ⟨item, hitem, (hreflect head item heq.symm).symm⟩
      · exact nodup_map_of_map_key_nodup_local
          value key hreflect tail hparts.2

private theorem nodup_flatMap_of_disjoint_blocks_local {A B : Type}
    (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks_local block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := heq ▸ htail
      obtain ⟨item, hitem, hvalueItem⟩ := List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item
            (List.mem_cons_of_mem head hitem)))

private theorem anchorDataExtentFive (cutoff : Nat) :
    (anchorSlabPhysicalData cutoff 2).extent = 5 := rfl

/-! ## 1. A duplicate-free carrier of all representative row choices -/

/-- The concrete connected source row generated by one selected background. -/
def reflectedBentGuardRepresentativeConnectedSources
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    List (SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId) :=
  (reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff).map
    (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff))

private theorem reflectedBentGuardAcceptedRowKey_eq_of_connectedSource_eq
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (left right : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2))
    (hsource :
      reflectedBentGuardGraftConnectedStrandSourceAtCutoff
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) left =
        reflectedBentGuardGraftConnectedStrandSourceAtCutoff
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) right) :
    reflectedBentGuardAcceptedRowKey cutoff hcutoff left =
      reflectedBentGuardAcceptedRowKey cutoff hcutoff right := by
  have hpair :
      reflectedBentGuardGraftObservableSourcePairAtCutoff
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) left =
        reflectedBentGuardGraftObservableSourcePairAtCutoff
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) right := by
    simpa only [reflectedBentGuardGraftConnectedStrandSourceAtCutoff] using
      congrArg Subtype.val hsource
  unfold reflectedBentGuardAcceptedRowKey
  apply Prod.ext
  · apply Subtype.ext
    rw [reflectedBentGuardGraftAcceptedStateOfOneLE_leftSource,
      reflectedBentGuardGraftAcceptedStateOfOneLE_leftSource]
    apply Prod.ext
    · simpa only [reflectedBentGuardGraftObservableSourcePairAtCutoff,
          reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical] using
        congrArg (fun pair => pair.1.1.1) hpair
    · simpa only [reflectedBentGuardGraftObservableSourcePairAtCutoff,
          reflectedBentGuardGraftLeftPositiveEntryAtCutoff_assignment] using
        congrArg (fun pair => pair.1.1.2) hpair
  · apply Subtype.ext
    rw [reflectedBentGuardGraftAcceptedStateOfOneLE_rightSource,
      reflectedBentGuardGraftAcceptedStateOfOneLE_rightSource]
    apply Prod.ext
    · simpa only [reflectedBentGuardGraftObservableSourcePairAtCutoff,
          reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical] using
        congrArg (fun pair => pair.2.1.1) hpair
    · simpa only [reflectedBentGuardGraftObservableSourcePairAtCutoff,
          reflectedBentGuardGraftRightExpandedEntryAtCutoff_assignment] using
        congrArg (fun pair => pair.2.1.2) hpair

theorem reflectedBentGuardRepresentativeConnectedSources_nodup
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    (reflectedBentGuardRepresentativeConnectedSources
      cutoff hcutoff).Nodup := by
  unfold reflectedBentGuardRepresentativeConnectedSources
  exact nodup_map_of_map_key_nodup_local
    (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff))
    (reflectedBentGuardAcceptedRowKey cutoff hcutoff)
    (reflectedBentGuardAcceptedRowKey_eq_of_connectedSource_eq
      cutoff hcutoff)
    (reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff)
    (keyRepresentatives_keys_nodup
      (reflectedBentGuardAcceptedRowKey cutoff hcutoff)
      (slabAcceptedTwoReplicaStates
        (anchorSlabPhysicalData cutoff 2)))

/-- Flatten the successful local choices over any concrete connected-source
family.  Keeping this compiler generic avoids exposing an enormous
anchor-specialized dependent equality. -/
def reflectedBentGuardConnectedSourceChoiceFamily
    (D : SlabPhysicalData)
    (sources : List (SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId)) :
    List (SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :=
  sources.flatMap
    (slabObservablePairedConnectedStrandSourceChoiceBlock
      D reflectedBentRootFaceId reflectedBentTargetFaceId)

theorem reflectedBentGuardRepresentativeSourceChoices_nodup
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    (reflectedBentGuardConnectedSourceChoiceFamily
      (anchorSlabPhysicalData cutoff 2)
      (reflectedBentGuardRepresentativeConnectedSources
        cutoff hcutoff)).Nodup := by
  unfold reflectedBentGuardConnectedSourceChoiceFamily
  apply nodup_flatMap_of_disjoint_blocks_local
  · exact reflectedBentGuardRepresentativeConnectedSources_nodup
      cutoff hcutoff
  · intro source _
    exact slabObservablePairedConnectedStrandSourceChoiceBlock_nodup
      (anchorSlabPhysicalData cutoff 2)
      reflectedBentRootFaceId reflectedBentTargetFaceId source
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftChoice, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightChoice, _, heq⟩ := List.mem_map.mp hright
    exact hne (congrArg
      (fun item : SlabObservablePairedConnectedStrandSourceChoice
        (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentTargetFaceId => item.1)
      heq.symm)

/-- The source Gibbs weight times the scaled local edge weight. -/
def reflectedBentGuardScaledPhysicalChoiceWeight
    (D : SlabPhysicalData)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) : Q' :=
  slabObservableTwoReplicaPairWeight D item.1.1 *
    (reflectedBentGuardConnectedRowScale *
      slabObservablePairedConnectedStrandSourceChoiceWeight
        D reflectedBentRootFaceId reflectedBentTargetFaceId item)

/-- The same scaled physical mass before flattening one connected row. -/
def reflectedBentGuardConnectedSourceScaledRowWeight
    (D : SlabPhysicalData)
    (source : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId) : Q' :=
  slabObservableTwoReplicaPairWeight D source.1 *
    (reflectedBentGuardConnectedRowScale *
      listQSum
        (slabObservablePairedConnectedStrandWeight
          D reflectedBentRootFaceId reflectedBentTargetFaceId source)
        (slabObservablePairedConnectedStrandChoices
          D reflectedBentRootFaceId reflectedBentTargetFaceId source))

/-- Flattening a connected source family preserves its total scaled physical
row mass exactly. -/
theorem reflectedBentGuardConnectedSourceChoiceFamily_sum_eqv_rows
    (D : SlabPhysicalData)
    (sources : List (SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId)) :
    listQSum (reflectedBentGuardScaledPhysicalChoiceWeight D)
        (reflectedBentGuardConnectedSourceChoiceFamily D sources) ≈
      listQSum (reflectedBentGuardConnectedSourceScaledRowWeight D)
        sources := by
  unfold reflectedBentGuardConnectedSourceChoiceFamily
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (reflectedBentGuardScaledPhysicalChoiceWeight D)
      (slabObservablePairedConnectedStrandSourceChoiceBlock
        D reflectedBentRootFaceId reflectedBentTargetFaceId)
      sources) ?_
  apply listQSum_congr
  intro source
  unfold slabObservablePairedConnectedStrandSourceChoiceBlock
    reflectedBentGuardScaledPhysicalChoiceWeight
    reflectedBentGuardConnectedSourceScaledRowWeight
    slabObservablePairedConnectedStrandSourceChoiceWeight
  rw [listQSum_map]
  exact Q'.eqv_trans _ _ _
    (listQSum_mul_left
      (slabObservableTwoReplicaPairWeight D source.1)
      (fun choice => reflectedBentGuardConnectedRowScale *
        slabObservablePairedConnectedStrandWeight
          D reflectedBentRootFaceId reflectedBentTargetFaceId source choice)
      (slabObservablePairedConnectedStrandChoices
        D reflectedBentRootFaceId reflectedBentTargetFaceId source))
    (Q'.mul_eqv_congr_left
      (slabObservableTwoReplicaPairWeight D source.1) _ _
      (listQSum_mul_left reflectedBentGuardConnectedRowScale
        (slabObservablePairedConnectedStrandWeight
          D reflectedBentRootFaceId reflectedBentTargetFaceId source)
        (slabObservablePairedConnectedStrandChoices
          D reflectedBentRootFaceId reflectedBentTargetFaceId source)))

/-! ## 2. Fixed-target compilation through the representative scan -/

/-- The members of any concrete source-choice family realizing one final
observable target. -/
def reflectedBentGuardFamilyTargetSourceChoices
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (items : List (SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId))
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    List (SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :=
  items.filter
    fun item => decide (target =
      slabObservablePairedConnectedStrandSourceChoiceRealize
        D reflectedBentRootFaceId reflectedBentTargetFaceId
          (reflectedBentGuardConnectedTargetFace_mem D hextent) item)

theorem reflectedBentGuardRepresentativeTargetSourceChoices_nodup
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (target : SlabObservableTwoReplicaPair
      (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId) :
    (reflectedBentGuardFamilyTargetSourceChoices
      (anchorSlabPhysicalData cutoff 2) (anchorDataExtentFive cutoff)
      (reflectedBentGuardConnectedSourceChoiceFamily
        (anchorSlabPhysicalData cutoff 2)
        (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff))
      target).Nodup := by
  unfold reflectedBentGuardFamilyTargetSourceChoices
  exact List.filter_sublist.nodup
    (reflectedBentGuardRepresentativeSourceChoices_nodup cutoff hcutoff)

/-! ## 3. The representative family lies inside the actual guarded carrier -/

theorem reflectedBentGuardRepresentativeSourceChoice_mem_global
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hitem : item ∈ reflectedBentGuardConnectedSourceChoiceFamily
      (anchorSlabPhysicalData cutoff 2)
      (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff)) :
    item ∈ slabObservablePairedConnectedStrandSourceChoices
      (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId := by
  unfold reflectedBentGuardConnectedSourceChoiceFamily at hitem
  obtain ⟨source, hsource, hblock⟩ := List.mem_flatMap.mp hitem
  obtain ⟨state, _, hsourceEq⟩ := List.mem_map.mp hsource
  obtain ⟨choice, hchoice, hitemEq⟩ := List.mem_map.mp hblock
  subst source
  subst item
  exact reflectedBentGuardGraftConnectedSourceChoice_mem_global
    (anchorSlabPhysicalData cutoff 2) hcutoff
      (anchorDataExtentFive cutoff) state choice hchoice

theorem reflectedBentGuardRepresentativeSourceChoice_has_state_match
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hitem : item ∈ reflectedBentGuardConnectedSourceChoiceFamily
      (anchorSlabPhysicalData cutoff 2)
      (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff)) :
    ∃ state,
      state ∈ reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff ∧
      reflectedBentGuardConnectedSourceChoiceMatchesStateB
        (anchorSlabPhysicalData cutoff 2) (anchorDataExtentFive cutoff)
          item state = true := by
  unfold reflectedBentGuardConnectedSourceChoiceFamily at hitem
  obtain ⟨source, hsource, hblock⟩ := List.mem_flatMap.mp hitem
  obtain ⟨state, hstate, hsourceEq⟩ := List.mem_map.mp hsource
  obtain ⟨choice, _, hitemEq⟩ := List.mem_map.mp hblock
  subst source
  subst item
  refine ⟨state, hstate, ?_⟩
  apply (reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
    (anchorSlabPhysicalData cutoff 2) hcutoff
      (anchorDataExtentFive cutoff) _ state).mpr
  constructor
  · simp only [reflectedBentGuardGraftConnectedStrandSourceAtCutoff,
      reflectedBentGuardGraftObservableSourcePairAtCutoff,
      reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical]
  · simp only [reflectedBentGuardGraftConnectedStrandSourceAtCutoff,
      reflectedBentGuardGraftObservableSourcePairAtCutoff,
      reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical]

theorem reflectedBentGuardRepresentativeSourceChoice_mem_guarded
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hitem : item ∈ reflectedBentGuardConnectedSourceChoiceFamily
      (anchorSlabPhysicalData cutoff 2)
      (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff)) :
    item ∈ reflectedBentGuardConnectedSourceChoices
      (anchorSlabPhysicalData cutoff 2) (anchorDataExtentFive cutoff) := by
  obtain ⟨state, _, hmatch⟩ :=
    reflectedBentGuardRepresentativeSourceChoice_has_state_match
      cutoff hcutoff item hitem
  apply (mem_reflectedBentGuardConnectedSourceChoices_iff
    (anchorSlabPhysicalData cutoff 2) hcutoff
      (anchorDataExtentFive cutoff) item).mpr
  refine ⟨reflectedBentGuardRepresentativeSourceChoice_mem_global
    cutoff hcutoff item hitem, state, ?_⟩
  exact (reflectedBentGuardConnectedSourceChoiceMatchesStateB_eq_true_iff
    (anchorSlabPhysicalData cutoff 2) hcutoff
      (anchorDataExtentFive cutoff) item state).mp hmatch

/-! ## 4. Representative target fibers inject into the actual columns -/

theorem reflectedBentGuardRepresentativeTargetSourceChoice_mem_actual
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (target : SlabObservableTwoReplicaPair
      (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hitem : item ∈ reflectedBentGuardFamilyTargetSourceChoices
      (anchorSlabPhysicalData cutoff 2) (anchorDataExtentFive cutoff)
      (reflectedBentGuardConnectedSourceChoiceFamily
        (anchorSlabPhysicalData cutoff 2)
        (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff))
      target) :
    item ∈ reflectedBentGuardConnectedTargetSourceChoices
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff) target := by
  have hparts := List.mem_filter.mp hitem
  have hguarded :=
    reflectedBentGuardRepresentativeSourceChoice_mem_guarded
      cutoff hcutoff item hparts.1
  have htarget := of_decide_eq_true hparts.2
  obtain ⟨output, houtput, hval⟩ :=
    reflectedBentGuardConnectedTargetPreimages_complete
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff) target item hguarded htarget
  unfold reflectedBentGuardConnectedTargetSourceChoices
  exact List.mem_map.mpr ⟨output, houtput, hval⟩

theorem reflectedBentGuardScaledPhysicalChoiceWeight_nonnegative
    (D : SlabPhysicalData)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    (0 : Q') ≤ reflectedBentGuardScaledPhysicalChoiceWeight D item := by
  unfold reflectedBentGuardScaledPhysicalChoiceWeight
  exact Q'.mul_nonneg _ _
    (slabObservableTwoReplicaPairWeight_nonnegative
      D reflectedBentRootFaceId item.1.1)
    (Q'.mul_nonneg _ _
      (Q'.invSucc_nonneg reflectedBentGuardProvenanceCodeSpace.length)
      (slabObservablePairedConnectedStrandWeight_nonnegative
        D reflectedBentRootFaceId reflectedBentTargetFaceId item.1 item.2))

/-- A representative fixed-target fiber is literally a duplicate-free
subfamily of the actual guarded target source-choice column. -/
theorem reflectedBentGuardRepresentativeTargetSourceChoices_sum_le_actual
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (target : SlabObservableTwoReplicaPair
      (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId) :
    listQSum
        (reflectedBentGuardScaledPhysicalChoiceWeight
          (anchorSlabPhysicalData cutoff 2))
        (reflectedBentGuardFamilyTargetSourceChoices
          (anchorSlabPhysicalData cutoff 2) (anchorDataExtentFive cutoff)
          (reflectedBentGuardConnectedSourceChoiceFamily
            (anchorSlabPhysicalData cutoff 2)
            (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff))
          target) ≤
      listQSum
        (reflectedBentGuardScaledPhysicalChoiceWeight
          (anchorSlabPhysicalData cutoff 2))
        (reflectedBentGuardConnectedTargetSourceChoices
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) target) := by
  apply listQSum_le_of_injective_nodup
    (reflectedBentGuardFamilyTargetSourceChoices
      (anchorSlabPhysicalData cutoff 2) (anchorDataExtentFive cutoff)
      (reflectedBentGuardConnectedSourceChoiceFamily
        (anchorSlabPhysicalData cutoff 2)
        (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff))
      target)
    (reflectedBentGuardConnectedTargetSourceChoices
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff) target)
    (reflectedBentGuardScaledPhysicalChoiceWeight
      (anchorSlabPhysicalData cutoff 2))
    (reflectedBentGuardScaledPhysicalChoiceWeight
      (anchorSlabPhysicalData cutoff 2)) id
  · exact reflectedBentGuardRepresentativeTargetSourceChoices_nodup
      cutoff hcutoff target
  · exact reflectedBentGuardConnectedTargetSourceChoices_nodup
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff) target
  · intro item hitem
    exact reflectedBentGuardRepresentativeTargetSourceChoice_mem_actual
      cutoff hcutoff target item hitem
  · intro left _ right _ heq
    exact heq
  · intro item _
    exact Q'.le_refl' _
  · intro item _
    exact reflectedBentGuardScaledPhysicalChoiceWeight_nonnegative
      (anchorSlabPhysicalData cutoff 2) item

/-- The already compiled actual target column has the same source-choice
weighted sum as its proof-carrying preimages, hence obeys physical Gibbs
capacity. -/
theorem reflectedBentGuardConnectedActualTargetSourceChoices_sum_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    listQSum (reflectedBentGuardScaledPhysicalChoiceWeight D)
        (reflectedBentGuardConnectedTargetSourceChoices
          D hcutoff hextent target) ≤
      slabObservableTwoReplicaPairWeight D target := by
  simpa only [reflectedBentGuardConnectedTargetSourceChoices,
      listQSum_map, reflectedBentGuardScaledPhysicalChoiceWeight,
      reflectedBentGuardConnectedTargetPreimageSourceWeight,
      reflectedBentGuardConnectedTargetPreimageWeight] using
    (reflectedBentGuardConnectedActualTargetPreimages_scaled_physical_sum_le
      D hcutoff hextent target)

/-- Every representative target fiber respects the physical Gibbs capacity
of that final target. -/
theorem reflectedBentGuardRepresentativeTargetSourceChoices_sum_le
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (target : SlabObservableTwoReplicaPair
      (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId) :
    listQSum
        (reflectedBentGuardScaledPhysicalChoiceWeight
          (anchorSlabPhysicalData cutoff 2))
        (reflectedBentGuardFamilyTargetSourceChoices
          (anchorSlabPhysicalData cutoff 2) (anchorDataExtentFive cutoff)
          (reflectedBentGuardConnectedSourceChoiceFamily
            (anchorSlabPhysicalData cutoff 2)
            (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff))
          target) ≤
      slabObservableTwoReplicaPairWeight
        (anchorSlabPhysicalData cutoff 2) target :=
  Q'.le_trans' _ _ _
    (reflectedBentGuardRepresentativeTargetSourceChoices_sum_le_actual
      cutoff hcutoff target)
    (reflectedBentGuardConnectedActualTargetSourceChoices_sum_le
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff) target)

/-! ## 5. Sum all final targets and recover the accepted-state floor -/

/-- The representative source-choice carrier is bounded by the total Gibbs
mass of the complete opposite observable determinant cell. -/
theorem reflectedBentGuardRepresentativeSourceChoices_sum_le_targetCell
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    listQSum
        (reflectedBentGuardScaledPhysicalChoiceWeight
          (anchorSlabPhysicalData cutoff 2))
        (reflectedBentGuardConnectedSourceChoiceFamily
          (anchorSlabPhysicalData cutoff 2)
          (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff)) ≤
      listQSum
        (slabObservableTwoReplicaPairWeight
          (anchorSlabPhysicalData cutoff 2))
        (slabObservableFourCellTargetPairs
          (anchorSlabPhysicalData cutoff 2)
            reflectedBentRootFaceId reflectedBentTargetFaceId) := by
  let D := anchorSlabPhysicalData cutoff 2
  let items := reflectedBentGuardConnectedSourceChoiceFamily D
    (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff)
  let weight := reflectedBentGuardScaledPhysicalChoiceWeight D
  let realize := slabObservablePairedConnectedStrandSourceChoiceRealize
    D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardConnectedTargetFace_mem D
        (anchorDataExtentFive cutoff))
  let targets := slabObservableFourCellTargetPairs
    D reflectedBentRootFaceId reflectedBentTargetFaceId
  have hpartition :
      listQSum (fiberWeight items weight realize) targets ≈
        listQSum weight items := by
    exact fiberWeight_total items weight realize targets
      (slabObservableFourCellTargetPairs_nodup
        D reflectedBentRootFaceId reflectedBentTargetFaceId)
      (fun item _ =>
        slabObservablePairedConnectedStrandRealize_mem
          D reflectedBentRootFaceId reflectedBentTargetFaceId
            (reflectedBentGuardConnectedTargetFace_mem D
              (anchorDataExtentFive cutoff)) item.1 item.2)
  have hcolumns :
      listQSum (fiberWeight items weight realize) targets ≤
        listQSum (slabObservableTwoReplicaPairWeight D) targets := by
    apply listQSum_le_termwise_local
    intro target _
    simpa only [fiberWeight, items, weight, realize, D,
        reflectedBentGuardFamilyTargetSourceChoices] using
      (reflectedBentGuardRepresentativeTargetSourceChoices_sum_le
        cutoff hcutoff target)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition)) hcolumns

/-- The accepted-row sum is exactly the flattened representative source-choice
mass used by the target-column estimate. -/
theorem reflectedBentGuardRepresentativeRows_eqv_sourceChoices
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    listQSum
        (fun representative =>
          slabObservableTwoReplicaPairWeight
              (anchorSlabPhysicalData cutoff 2)
              (reflectedBentGuardGraftObservableSourcePairAtCutoff
                (anchorSlabPhysicalData cutoff 2) hcutoff
                  (anchorDataExtentFive cutoff) representative) *
            reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
              (anchorSlabPhysicalData cutoff 2) hcutoff
                (anchorDataExtentFive cutoff) representative)
        (reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff) ≈
      listQSum
        (reflectedBentGuardScaledPhysicalChoiceWeight
          (anchorSlabPhysicalData cutoff 2))
        (reflectedBentGuardConnectedSourceChoiceFamily
          (anchorSlabPhysicalData cutoff 2)
          (reflectedBentGuardRepresentativeConnectedSources
            cutoff hcutoff)) := by
  have hflatten :=
    reflectedBentGuardConnectedSourceChoiceFamily_sum_eqv_rows
      (anchorSlabPhysicalData cutoff 2)
      (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff)
  have hrows :
      listQSum
          (reflectedBentGuardConnectedSourceScaledRowWeight
            (anchorSlabPhysicalData cutoff 2))
          (reflectedBentGuardRepresentativeConnectedSources cutoff hcutoff) ≈
        listQSum
          (fun representative =>
            slabObservableTwoReplicaPairWeight
                (anchorSlabPhysicalData cutoff 2)
                (reflectedBentGuardGraftObservableSourcePairAtCutoff
                  (anchorSlabPhysicalData cutoff 2) hcutoff
                    (anchorDataExtentFive cutoff) representative) *
              reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
                (anchorSlabPhysicalData cutoff 2) hcutoff
                  (anchorDataExtentFive cutoff) representative)
          (reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff) := by
    unfold reflectedBentGuardRepresentativeConnectedSources
    rw [listQSum_map]
    apply listQSum_congr
    intro representative
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hrows) (Q'.eqv_symm hflatten)

/-- **Finite aggregate retained floor.**  One fixed positive rate, independent
of the representation cutoff, times the square of the corrected-slab physical
partition is bounded by the complete opposite observable cell. -/
theorem reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_targetCell
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    reflectedBentGuardScaledSeparatedTransitionRate *
        ((anchorSlabPhysicalData cutoff 2).physicalPartition *
          (anchorSlabPhysicalData cutoff 2).physicalPartition) ≤
      listQSum
        (slabObservableTwoReplicaPairWeight
          (anchorSlabPhysicalData cutoff 2))
        (slabObservableFourCellTargetPairs
          (anchorSlabPhysicalData cutoff 2)
            reflectedBentRootFaceId reflectedBentTargetFaceId) := by
  exact Q'.le_trans' _ _ _
    (reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_rows
      cutoff hcutoff)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (reflectedBentGuardRepresentativeRows_eqv_sourceChoices
          cutoff hcutoff))
      (reflectedBentGuardRepresentativeSourceChoices_sum_le_targetCell
        cutoff hcutoff))

#print axioms reflectedBentGuardRepresentativeConnectedSources_nodup
#print axioms reflectedBentGuardRepresentativeSourceChoices_nodup
#print axioms reflectedBentGuardRepresentativeTargetSourceChoices_sum_le
#print axioms reflectedBentGuardRepresentativeSourceChoices_sum_le_targetCell
#print axioms reflectedBentGuardRepresentativeRows_eqv_sourceChoices
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_targetCell

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateRetainedFloor
