/-
# Decoder-controlled unthinned connected column capacity

The connected successful strand row already has a pointwise realization in
the opposite observable cell, but the paired-face component switch can merge
different intermediate recoupling columns.  First-source thinning repairs
that merge at the cost of possibly erasing whole rows.

This module isolates the exact alternative.  Given the explicit face-switch
decoder certificate, equality of two final targets recovers equality of their
intermediate recoupled pairs.  All preimages of one final target can therefore
be transported into one common column of one physical-pair bistochastic
matrix.  Their source rows are distinct, so column normalization proves the
unthinned connected column bound.

No decoder certificate is inhabited here.  Thus the result closes all finite
matrix bookkeeping downstream of that certificate but does not assert a
uniform retained fraction, operator gap, scaling limit, continuum theory, or
Clay result.

Constructive contract: finite dependent lists, equality transport, an
explicit Type-level decoder certificate, and exact `Q'` only; no
`Classical.*`, choice, `native_decide`, `sorry`, new axiom,
`noncomputable`, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup

namespace YMGap.Continuum.CompactDualSlabObservablePairedConnectedDecoderColumnCapacity

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance connectedDecoderPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. Flatten the dependent connected successful row -/

abbrev SlabObservablePairedConnectedStrandSourceChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :=
  Sigma fun source : SlabObservablePairedConnectedStrandSource
    D rootFaceId targetFaceId =>
      SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId source

def slabObservablePairedConnectedStrandSourceChoiceBlock
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    List (SlabObservablePairedConnectedStrandSourceChoice
      D rootFaceId targetFaceId) :=
  (slabObservablePairedConnectedStrandChoices
    D rootFaceId targetFaceId source).map fun choice =>
      ⟨source, choice⟩

def slabObservablePairedConnectedStrandSourceChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservablePairedConnectedStrandSourceChoice
      D rootFaceId targetFaceId) :=
  (slabObservablePairedConnectedStrandSources
    D rootFaceId targetFaceId).flatMap fun source =>
      slabObservablePairedConnectedStrandSourceChoiceBlock
        D rootFaceId targetFaceId source

private theorem nodup_map_of_injective_local {A B : Type}
    (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective_local map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

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
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

theorem slabObservablePairedConnectedStrandChoices_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId source).Nodup := by
  unfold slabObservablePairedConnectedStrandChoices
    slabObservablePairedStrandSuccessfulChoices
    slabObservablePairedStrandSuccessfulRecouplingChoices
    slabObservablePairedStrandRecouplingChoices
  exact List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (List.filter_sublist.nodup
        (slabPhysicalPairRecouplingKernel_targets_nodup
          D.extent source.1.1.1.1 source.1.2.1.1)))

theorem slabObservablePairedConnectedStrandSourceChoiceBlock_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    (slabObservablePairedConnectedStrandSourceChoiceBlock
      D rootFaceId targetFaceId source).Nodup := by
  unfold slabObservablePairedConnectedStrandSourceChoiceBlock
  apply nodup_map_of_injective_local
  · intro left right heq
    apply eq_of_heq
    cases heq
    rfl
  · exact slabObservablePairedConnectedStrandChoices_nodup
      D rootFaceId targetFaceId source

theorem slabObservablePairedConnectedStrandSourceChoices_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservablePairedConnectedStrandSourceChoices
      D rootFaceId targetFaceId).Nodup := by
  unfold slabObservablePairedConnectedStrandSourceChoices
  apply nodup_flatMap_of_disjoint_blocks_local
  · exact slabObservablePairedConnectedStrandSources_nodup
      D rootFaceId targetFaceId
  · intro source _
    exact slabObservablePairedConnectedStrandSourceChoiceBlock_nodup
      D rootFaceId targetFaceId source
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftChoice, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightChoice, _, heq⟩ := List.mem_map.mp hright
    exact hne (congrArg
      (fun item : SlabObservablePairedConnectedStrandSourceChoice
        D rootFaceId targetFaceId => item.1) heq.symm)

def slabObservablePairedConnectedStrandSourceChoiceWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D rootFaceId targetFaceId) : Q' :=
  slabObservablePairedConnectedStrandWeight
    D rootFaceId targetFaceId item.1 item.2

def slabObservablePairedConnectedStrandSourceChoiceRealize
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D rootFaceId targetFaceId) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  slabObservablePairedConnectedStrandRealize
    D rootFaceId targetFaceId htarget item.1 item.2

theorem slabObservablePairedConnectedDependentPushforward_eqv_flattened
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    kernelPushforwardWeight
        (slabObservablePairedConnectedStrandSourceChoices
          D rootFaceId targetFaceId)
        (slabObservablePairedConnectedStrandSourceChoiceWeight
          D rootFaceId targetFaceId)
        (slabObservablePairedConnectedStrandSourceChoiceRealize
          D rootFaceId targetFaceId htarget)
        target ≈
      listQSum
        (fun source => dependentKernelPushforwardWeight
          (SlabObservablePairedConnectedStrandChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandWeight
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandRealize
            D rootFaceId targetFaceId htarget)
          source target)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) := by
  unfold kernelPushforwardWeight
    slabObservablePairedConnectedStrandSourceChoices
  refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
  apply listQSum_congr
  intro source
  unfold slabObservablePairedConnectedStrandSourceChoiceBlock
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-! ## 2. The literal preimage of one final connected target -/

def slabObservablePairedConnectedStrandTargetPreimages
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabObservablePairedConnectedStrandSourceChoice
      D rootFaceId targetFaceId) :=
  (slabObservablePairedConnectedStrandSourceChoices
    D rootFaceId targetFaceId).filter fun item =>
      decide (target =
        slabObservablePairedConnectedStrandSourceChoiceRealize
          D rootFaceId targetFaceId htarget item)

theorem mem_slabObservablePairedConnectedStrandTargetPreimages_iff
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (item : SlabObservablePairedConnectedStrandSourceChoice
      D rootFaceId targetFaceId) :
    item ∈ slabObservablePairedConnectedStrandTargetPreimages
        D rootFaceId targetFaceId htarget target ↔
      item ∈ slabObservablePairedConnectedStrandSourceChoices
          D rootFaceId targetFaceId ∧
        target = slabObservablePairedConnectedStrandSourceChoiceRealize
          D rootFaceId targetFaceId htarget item := by
  unfold slabObservablePairedConnectedStrandTargetPreimages
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem slabObservablePairedConnectedStrandTargetPreimages_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    (slabObservablePairedConnectedStrandTargetPreimages
      D rootFaceId targetFaceId htarget target).Nodup := by
  unfold slabObservablePairedConnectedStrandTargetPreimages
  exact List.filter_sublist.nodup
    (slabObservablePairedConnectedStrandSourceChoices_nodup
      D rootFaceId targetFaceId)

theorem slabObservablePairedConnectedDependentPushforward_eqv_preimage_sum
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    listQSum
        (fun source => dependentKernelPushforwardWeight
          (SlabObservablePairedConnectedStrandChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandWeight
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandRealize
            D rootFaceId targetFaceId htarget)
          source target)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) ≈
      listQSum
        (slabObservablePairedConnectedStrandSourceChoiceWeight
          D rootFaceId targetFaceId)
        (slabObservablePairedConnectedStrandTargetPreimages
          D rootFaceId targetFaceId htarget target) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (slabObservablePairedConnectedDependentPushforward_eqv_flattened
        D rootFaceId targetFaceId htarget target))
    (kernelPushforwardWeight_eqv_fiberWeight
      (slabObservablePairedConnectedStrandSourceChoiceWeight
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandSourceChoiceRealize
        D rootFaceId targetFaceId htarget)
      target
      (slabObservablePairedConnectedStrandSourceChoices
        D rootFaceId targetFaceId))

/-! ## 3. Common physical source rows -/

/-- One connected source transported into a fixed physical-pair recoupling
matrix.  The equalities are data, so every later transport is constructive. -/
structure SlabObservablePairedConnectedContributorAt
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling) : Type where
  source : SlabObservablePairedConnectedStrandSource
    D rootFaceId targetFaceId
  leftPhysical_eq : source.1.1.1.1 = leftPhysical
  rightPhysical_eq : source.1.2.1.1 = rightPhysical

def SlabObservablePairedConnectedContributorAt.leftAssignment
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (contributor : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    SlabFusionWitnessAssignment :=
  contributor.source.1.1.1.2

def SlabObservablePairedConnectedContributorAt.rightAssignment
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (contributor : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    SlabFusionWitnessAssignment :=
  contributor.source.1.2.1.2

theorem SlabObservablePairedConnectedContributorAt.leftAssignment_mem
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (contributor : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    contributor.leftAssignment ∈
      slabFineFusionWitnesses D leftPhysical := by
  exact Eq.mp
    (congrArg
      (fun physical => contributor.leftAssignment ∈
        slabFineFusionWitnesses D physical)
      contributor.leftPhysical_eq)
    contributor.source.1.1.assignment_mem

theorem SlabObservablePairedConnectedContributorAt.rightAssignment_mem
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (contributor : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    contributor.rightAssignment ∈
      slabFineFusionWitnesses D rightPhysical := by
  exact Eq.mp
    (congrArg
      (fun physical => contributor.rightAssignment ∈
        slabFineFusionWitnesses D physical)
      contributor.rightPhysical_eq)
    (slabExpandedFineSourceEntryAssignment_mem contributor.source.1.2)

def slabObservablePairedConnectedContributorProductionRow
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (contributor : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    SlabPhysicalPairRecouplingSourceAssignment
      D.extent leftPhysical rightPhysical :=
  slabPhysicalPairRecouplingProductionSource
    D.cutoff D.extent leftPhysical rightPhysical
    contributor.leftAssignment contributor.rightAssignment
    contributor.leftAssignment_mem contributor.rightAssignment_mem

theorem slabObservablePairedConnectedContributorProductionRow_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (contributor : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    slabObservablePairedConnectedContributorProductionRow
        D rootFaceId targetFaceId leftPhysical rightPhysical contributor ∈
      (slabPhysicalPairRecouplingKernel
        D.extent leftPhysical rightPhysical).sources :=
  slabPhysicalPairRecouplingProductionSource_global_mem
    D.cutoff D.extent leftPhysical rightPhysical
    contributor.leftAssignment contributor.rightAssignment
    contributor.leftAssignment_mem contributor.rightAssignment_mem

theorem slabObservablePairedConnectedContributorProductionRow_injective
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (left right : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical)
    (heq : slabObservablePairedConnectedContributorProductionRow
        D rootFaceId targetFaceId leftPhysical rightPhysical left =
      slabObservablePairedConnectedContributorProductionRow
        D rootFaceId targetFaceId leftPhysical rightPhysical right) :
    left = right := by
  have hassignments :=
    slabPhysicalPairRecouplingProductionSource_assignments_injective
      D.cutoff D.extent leftPhysical rightPhysical
      left.leftAssignment left.rightAssignment
      right.leftAssignment right.rightAssignment
      left.leftAssignment_mem left.rightAssignment_mem
      right.leftAssignment_mem right.rightAssignment_mem heq
  have hsources : left.source = right.source := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext
        (left.leftPhysical_eq.trans right.leftPhysical_eq.symm)
        hassignments.1
    · apply Subtype.ext
      exact Prod.ext
        (left.rightPhysical_eq.trans right.rightPhysical_eq.symm)
        hassignments.2
  cases left
  cases right
  cases hsources
  congr

def slabObservablePairedConnectedContributorColumnWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (contributor : SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) : Q' :=
  (slabPhysicalPairRecouplingKernel
    D.extent leftPhysical rightPhysical).weight
    (slabObservablePairedConnectedContributorProductionRow
      D rootFaceId targetFaceId leftPhysical rightPhysical contributor)
    target

/-- Transport one connected source-row entry into a propositionally equal
common physical matrix and target column. -/
theorem slabObservablePairedConnectedStrandWeight_transport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source)
    (leftPhysical rightPhysical : SlabLabelling)
    (targetColumn : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (hleft : source.1.1.1.1 = leftPhysical)
    (hright : source.1.2.1.1 = rightPhysical)
    (hchoice : transportSlabPhysicalPairRecouplingTargetAssignment
        hleft hright choice.1 = targetColumn) :
    slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId source choice ≈
      slabObservablePairedConnectedContributorColumnWeight
        D rootFaceId targetFaceId leftPhysical rightPhysical targetColumn
        { source := source
          leftPhysical_eq := hleft
          rightPhysical_eq := hright } := by
  cases hleft
  cases hright
  rw [transportSlabPhysicalPairRecouplingTargetAssignment_rfl] at hchoice
  subst targetColumn
  exact Q'.eqv_refl _

theorem slabObservablePairedConnectedContributorColumnWeight_sum_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (contributors : List (SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical))
    (hcontributors : contributors.Nodup) :
    listQSum
        (slabObservablePairedConnectedContributorColumnWeight
          D rootFaceId targetFaceId leftPhysical rightPhysical target)
        contributors ≤ 1 := by
  letI : DecidableEq
      (SlabPhysicalPairRecouplingSourceAssignment
        D.extent leftPhysical rightPhysical) :=
    slabPhysicalPairRecouplingSourceAssignmentDecidableEq
      D.extent leftPhysical rightPhysical
  exact Q'.le_trans' _ _ _
    (listQSum_le_of_injective
      contributors
      (slabPhysicalPairRecouplingKernel
        D.extent leftPhysical rightPhysical).sources
      (slabObservablePairedConnectedContributorColumnWeight
        D rootFaceId targetFaceId leftPhysical rightPhysical target)
      (fun source =>
        (slabPhysicalPairRecouplingKernel
          D.extent leftPhysical rightPhysical).weight source target)
      (slabObservablePairedConnectedContributorProductionRow
        D rootFaceId targetFaceId leftPhysical rightPhysical)
      hcontributors
      (fun contributor _ =>
        slabObservablePairedConnectedContributorProductionRow_mem
          D rootFaceId targetFaceId leftPhysical rightPhysical contributor)
      (fun left _ right _ heq =>
        slabObservablePairedConnectedContributorProductionRow_injective
          D rootFaceId targetFaceId leftPhysical rightPhysical
          left right heq)
      (fun contributor _ => Q'.le_refl' _)
      (fun source _ =>
        (slabPhysicalPairRecouplingKernel
          D.extent leftPhysical rightPhysical).weight_nonnegative
            source target))
    (Q'.le_of_eqv
      (slabPhysicalPairRecouplingKernel_column_normalized
        D.extent leftPhysical rightPhysical target))

/-! ## 4. A decoder identifies every target preimage with one column -/

abbrev SlabObservablePairedConnectedStrandTargetPreimage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :=
  {item // item ∈ slabObservablePairedConnectedStrandTargetPreimages
    D rootFaceId targetFaceId htarget target}

theorem SlabObservablePairedConnectedStrandTargetPreimage.target_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    target = slabObservablePairedConnectedStrandSourceChoiceRealize
      D rootFaceId targetFaceId htarget item.1 :=
  (mem_slabObservablePairedConnectedStrandTargetPreimages_iff
    D rootFaceId targetFaceId htarget target item.1).mp item.2 |>.2

def slabObservablePairedConnectedPreimageContributor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId
      anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 := by
  let hpairs := certificate.recoupledPair_eq_of_targetPair_eq
    item.1.1.toRecouplingSource item.1.2
    anchor.1.1.toRecouplingSource anchor.1.2
    (item.target_eq.symm.trans anchor.target_eq)
  have hleft : item.1.1.1.1.1.1 = anchor.1.1.1.1.1.1 := by
    simpa only [slabObservablePairedStrandRecoupledPair_leftPhysical] using
      congrArg
        (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.1.1.1)
        hpairs
  have hright : item.1.1.1.2.1.1 = anchor.1.1.1.2.1.1 := by
    simpa only [slabObservablePairedStrandRecoupledPair_rightPhysical] using
      congrArg
        (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.2.1.1)
        hpairs
  exact
    { source := item.1.1
      leftPhysical_eq := hleft
      rightPhysical_eq := hright }

theorem slabObservablePairedConnectedPreimageChoice_transport_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    transportSlabPhysicalPairRecouplingTargetAssignment
        (slabObservablePairedConnectedPreimageContributor
          D rootFaceId targetFaceId htarget target certificate
          anchor item).leftPhysical_eq
        (slabObservablePairedConnectedPreimageContributor
          D rootFaceId targetFaceId htarget target certificate
          anchor item).rightPhysical_eq
        item.1.2.1 = anchor.1.2.1 := by
  let hpairs := certificate.recoupledPair_eq_of_targetPair_eq
    item.1.1.toRecouplingSource item.1.2
    anchor.1.1.toRecouplingSource anchor.1.2
    (item.target_eq.symm.trans anchor.target_eq)
  apply item.1.1.toRecouplingSource.anchor.target_eq_of_realizations_eq
    anchor.1.1.toRecouplingSource.anchor
  · exact congrArg
      (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.1.1.2)
      hpairs
  · exact congrArg
      (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.2.1.2)
      hpairs

theorem slabObservablePairedConnectedPreimageWeight_eqv_commonColumnWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    slabObservablePairedConnectedStrandSourceChoiceWeight
        D rootFaceId targetFaceId item.1 ≈
      slabObservablePairedConnectedContributorColumnWeight
        D rootFaceId targetFaceId
        anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1
        (slabObservablePairedConnectedPreimageContributor
          D rootFaceId targetFaceId htarget target certificate
          anchor item) := by
  let contributor := slabObservablePairedConnectedPreimageContributor
    D rootFaceId targetFaceId htarget target certificate anchor item
  have hchoice := slabObservablePairedConnectedPreimageChoice_transport_eq
    D rootFaceId targetFaceId htarget target certificate anchor item
  simpa only [slabObservablePairedConnectedStrandSourceChoiceWeight,
      contributor] using
    (slabObservablePairedConnectedStrandWeight_transport
      D rootFaceId targetFaceId item.1.1 item.1.2
      anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1
      contributor.leftPhysical_eq contributor.rightPhysical_eq hchoice)

def slabObservablePairedConnectedPreimageContributors
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    List (SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId
      anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1) :=
  (slabObservablePairedConnectedStrandTargetPreimages
    D rootFaceId targetFaceId htarget target).attach.map fun item =>
      slabObservablePairedConnectedPreimageContributor
        D rootFaceId targetFaceId htarget target certificate anchor item

theorem slabObservablePairedConnectedPreimageContributors_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    (slabObservablePairedConnectedPreimageContributors
      D rootFaceId targetFaceId htarget target certificate anchor).Nodup := by
  unfold slabObservablePairedConnectedPreimageContributors
  apply nodup_map_of_injective_local
  · intro left right heq
    apply Subtype.ext
    have hsources : left.1.1 = right.1.1 := congrArg
      (fun contributor : SlabObservablePairedConnectedContributorAt
        D rootFaceId targetFaceId
        anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 => contributor.source) heq
    cases left with
    | mk leftItem leftMem =>
      cases right with
      | mk rightItem rightMem =>
        cases leftItem with
        | mk leftSource leftChoice =>
          cases rightItem with
          | mk rightSource rightChoice =>
            dsimp only at hsources
            subst rightSource
            have htargets :
                slabObservablePairedConnectedStrandRealize
                    D rootFaceId targetFaceId htarget leftSource leftChoice =
                  slabObservablePairedConnectedStrandRealize
                    D rootFaceId targetFaceId htarget leftSource rightChoice :=
              (SlabObservablePairedConnectedStrandTargetPreimage.target_eq
                ⟨⟨leftSource, leftChoice⟩, leftMem⟩).symm.trans
                (SlabObservablePairedConnectedStrandTargetPreimage.target_eq
                  ⟨⟨leftSource, rightChoice⟩, rightMem⟩)
            have hchoices :=
              certificate.successfulChoice_eq_of_fixed_source_targetPair_eq
                leftSource.toRecouplingSource leftChoice rightChoice htargets
            subst rightChoice
            rfl
  · exact attach_nodup_of_nodup _
      (slabObservablePairedConnectedStrandTargetPreimages_nodup
        D rootFaceId targetFaceId htarget target)

theorem slabObservablePairedConnectedPreimageSum_eqv_commonColumnSum
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    listQSum
        (slabObservablePairedConnectedStrandSourceChoiceWeight
          D rootFaceId targetFaceId)
        (slabObservablePairedConnectedStrandTargetPreimages
          D rootFaceId targetFaceId htarget target) ≈
      listQSum
        (slabObservablePairedConnectedContributorColumnWeight
          D rootFaceId targetFaceId
          anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1)
        (slabObservablePairedConnectedPreimageContributors
          D rootFaceId targetFaceId htarget target certificate anchor) := by
  rw [← listQSum_attach]
  unfold slabObservablePairedConnectedPreimageContributors
  rw [listQSum_map]
  apply listQSum_congr
  intro item
  exact slabObservablePairedConnectedPreimageWeight_eqv_commonColumnWeight
    D rootFaceId targetFaceId htarget target certificate anchor item

/-! ## 5. Unthinned column capacity -/

/-- **Decoder-controlled unthinned column capacity.**  The entire positive
successful connected row can be retained when the face switch has the stated
left inverse. -/
theorem slabObservablePairedConnectedStrandColumn_le_one_of_decoder
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    listQSum
        (fun source => dependentKernelPushforwardWeight
          (SlabObservablePairedConnectedStrandChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandWeight
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandRealize
            D rootFaceId targetFaceId htarget)
          source target)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) ≤ 1 := by
  have hflatten :=
    slabObservablePairedConnectedDependentPushforward_eqv_preimage_sum
      D rootFaceId targetFaceId htarget target
  cases hpreimages : slabObservablePairedConnectedStrandTargetPreimages
      D rootFaceId targetFaceId htarget target with
  | nil =>
      rw [hpreimages] at hflatten
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hflatten)
        Q'.zero_le_one
  | cons head tail =>
      let anchor : SlabObservablePairedConnectedStrandTargetPreimage
          D rootFaceId targetFaceId htarget target :=
        ⟨head, by rw [hpreimages]; exact List.mem_cons_self⟩
      have hcommon :=
        slabObservablePairedConnectedPreimageSum_eqv_commonColumnSum
          D rootFaceId targetFaceId htarget target certificate anchor
      have hcolumn :=
        slabObservablePairedConnectedContributorColumnWeight_sum_le_one
          D rootFaceId targetFaceId
          anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1
          (slabObservablePairedConnectedPreimageContributors
            D rootFaceId targetFaceId htarget target certificate anchor)
          (slabObservablePairedConnectedPreimageContributors_nodup
            D rootFaceId targetFaceId htarget target certificate anchor)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hflatten)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcommon) hcolumn)

/-- The decoder-controlled unthinned column also satisfies the physical
Gibbs-weight capacity bound. -/
theorem slabObservablePairedConnectedStrandWeightedColumn_le_of_decoder
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1 *
          dependentKernelPushforwardWeight
            (SlabObservablePairedConnectedStrandChoice
              D rootFaceId targetFaceId)
            (slabObservablePairedConnectedStrandChoices
              D rootFaceId targetFaceId)
            (slabObservablePairedConnectedStrandWeight
              D rootFaceId targetFaceId)
            (slabObservablePairedConnectedStrandRealize
              D rootFaceId targetFaceId htarget)
            source target)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) ≤
      slabObservableTwoReplicaPairWeight D target := by
  apply weightedColumn_le_of_columnCapacity
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (slabObservableTwoReplicaPairWeight D)
    (SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandRealize
      D rootFaceId targetFaceId htarget)
    target
  · exact slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId target
  · intro source _ choice heq
    subst target
    exact Q'.eqv_symm
      (slabObservablePairedStrandRecoupledTargetPair_weight_preserved
        D rootFaceId targetFaceId htarget
        source.toRecouplingSource choice)
  · exact slabObservablePairedConnectedStrandColumn_le_one_of_decoder
      D rootFaceId targetFaceId htarget certificate target

#print axioms slabObservablePairedConnectedStrandColumn_le_one_of_decoder
#print axioms slabObservablePairedConnectedStrandWeightedColumn_le_of_decoder

end YMGap.Continuum.CompactDualSlabObservablePairedConnectedDecoderColumnCapacity
