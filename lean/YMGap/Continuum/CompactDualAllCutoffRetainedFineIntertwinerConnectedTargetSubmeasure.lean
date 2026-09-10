/-
# The connected source contribution as an enriched target submeasure

The full expanded-source joint law has product enriched blocked law as its
target marginal.  This module embeds the literal support-connected observable
source pairs into that full expanded source square, retaining their exact
fine-intertwiner labels.  At each pair of enriched targets, summing only those
sources defines a nonnegative connected contribution.

A constructive finite subset-sum theorem then proves that this contribution
is bounded pointwise by the full product blocked mass.  Thus source
connectivity now determines an honest target submeasure rather than merely a
global scalar bound.

The total mass and corridor decay of this target submeasure are proved in the
next layer.  No target observable, reflection lift, strict form bound,
continuum limit, or Clay theorem is claimed here.

## Axiom gate

Finite-support keys, duplicate-free list maps, nonnegative finite sums, and
the exact expanded marginal only.  No classical choice, placeholder, trusted
external computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerExpandedMarginal
import YMGap.Continuum.CompactDualSlabExpandedTargetKey

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerExpandedMarginal
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Attach finite-support identity to the grouped expanded carrier -/

theorem mem_allCutoffExpandedSources_iff
    {D : SlabPhysicalData} {source : AllCutoffExpandedSource D} :
    source ∈ allCutoffExpandedSources D ↔
      source.1 ∈ slabPhysicalSourceEntries D ∧
        source.2 ∈ slabFineFusionWitnesses D source.1.1 := by
  unfold allCutoffExpandedSources
  constructor
  · intro hsource
    obtain ⟨physicalSource, hphysicalSource, hblock⟩ :=
      List.mem_flatMap.mp hsource
    unfold allCutoffExpandedSourceBlock at hblock
    obtain ⟨witness, hwitness, heq⟩ := List.mem_map.mp hblock
    have hphysical : physicalSource = source.1 := by
      exact congrArg Prod.fst heq
    have hwitnessEq : witness = source.2 := by
      exact congrArg Prod.snd heq
    exact ⟨hphysical ▸ hphysicalSource,
      hphysical ▸ hwitnessEq ▸ hwitness⟩
  · intro hsource
    apply List.mem_flatMap.mpr
    refine ⟨source.1, hsource.1, ?_⟩
    unfold allCutoffExpandedSourceBlock
    exact List.mem_map.mpr ⟨source.2, hsource.2, rfl⟩

abbrev AllCutoffExpandedSourceEntry (D : SlabPhysicalData) :=
  {source : AllCutoffExpandedSource D //
    source ∈ allCutoffExpandedSources D}

def allCutoffExpandedSourceEntries (D : SlabPhysicalData) :
    List (AllCutoffExpandedSourceEntry D) :=
  (allCutoffExpandedSources D).attach

def AllCutoffExpandedSourceEntry.key
    {D : SlabPhysicalData} (source : AllCutoffExpandedSourceEntry D) :
    SlabExpandedFineTargetKey :=
  slabExpandedFineTargetKey D source.1.1.1 source.1.2

theorem AllCutoffExpandedSourceEntry.eq_of_key_eq
    {D : SlabPhysicalData}
    {left right : AllCutoffExpandedSourceEntry D}
    (hkey : left.key = right.key) : left = right := by
  have hleftParts := mem_allCutoffExpandedSources_iff.mp left.2
  have hrightParts := mem_allCutoffExpandedSources_iff.mp right.2
  have hleftRaw : (left.1.1.1, left.1.2) ∈
      slabExpandedFineSources D :=
    mem_slabExpandedFineSources_iff.mpr
      ⟨left.1.1.2, hleftParts.2⟩
  have hrightRaw : (right.1.1.1, right.1.2) ∈
      slabExpandedFineSources D :=
    mem_slabExpandedFineSources_iff.mpr
      ⟨right.1.1.2, hrightParts.2⟩
  have hraw := slabExpandedFineTargetKey_eq_source_eq
    D hleftRaw hrightRaw hkey
  have hphysical : left.1.1 = right.1.1 :=
    Subtype.ext (congrArg Prod.fst hraw)
  have hwitness : left.1.2 = right.1.2 :=
    congrArg
      (fun source : SlabLabelling × SlabFusionWitnessAssignment =>
        source.2) hraw
  have hgrouped : left.1 = right.1 :=
    Prod.ext hphysical hwitness
  exact Subtype.ext hgrouped

private def allCutoffExpandedSourceEntryDecidableEq
    (D : SlabPhysicalData) :
    DecidableEq (AllCutoffExpandedSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (AllCutoffExpandedSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey
        (congrArg AllCutoffExpandedSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (AllCutoffExpandedSourceEntry D) :=
  allCutoffExpandedSourceEntryDecidableEq D

/-! ## 2. Embed the observable connected carrier -/

def slabObservablePairLeftExpandedSourceEntry
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    AllCutoffExpandedSourceEntry D :=
  ⟨(slabObservablePairLeftPhysicalSource D pair, pair.1.1.2),
    mem_allCutoffExpandedSources_iff.mpr
      ⟨by
        unfold slabPhysicalSourceEntries
        exact List.mem_attach D.physicalLabellings
          (slabObservablePairLeftPhysicalSource D pair),
       (mem_slabExpandedFineSources_iff.mp
          pair.1.source_mem_expanded).2⟩⟩

def slabObservablePairRightExpandedSourceEntry
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    AllCutoffExpandedSourceEntry D :=
  ⟨(slabObservablePairRightPhysicalSource D pair, pair.2.1.2),
    mem_allCutoffExpandedSources_iff.mpr
      ⟨by
        unfold slabPhysicalSourceEntries
        exact List.mem_attach D.physicalLabellings
          (slabObservablePairRightPhysicalSource D pair),
       (mem_slabExpandedFineSources_iff.mp pair.2.2).2⟩⟩

def slabObservablePairExpandedSourceEntries
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    AllCutoffExpandedSourceEntry D × AllCutoffExpandedSourceEntry D :=
  (slabObservablePairLeftExpandedSourceEntry D pair,
    slabObservablePairRightExpandedSourceEntry D pair)

theorem slabObservablePairExpandedSourceEntries_injective
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    Function.Injective
      (slabObservablePairExpandedSourceEntries D
        (rootFaceId := rootFaceId)) := by
  intro left right heq
  have hleftEntry := congrArg Prod.fst heq
  have hrightEntry := congrArg Prod.snd heq
  have hleftRaw : left.1.1 = right.1.1 := by
    exact congrArg
      (fun entry : AllCutoffExpandedSourceEntry D =>
        (entry.1.1.1, entry.1.2)) hleftEntry
  have hrightRaw : left.2.1 = right.2.1 := by
    exact congrArg
      (fun entry : AllCutoffExpandedSourceEntry D =>
        (entry.1.1.1, entry.1.2)) hrightEntry
  exact Prod.ext (Subtype.ext hleftRaw) (Subtype.ext hrightRaw)

/-- The support-connected observable pairs, embedded in the full attached
expanded-source square. -/
def allCutoffConnectedExpandedSourceEntryPairs
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) :
    List (AllCutoffExpandedSourceEntry S.fine ×
      AllCutoffExpandedSourceEntry S.fine) :=
  (slabObservablePairedSupportConnectedFourCellSourcePairs
    S.fine rootFaceId targetFaceId).map
      (slabObservablePairExpandedSourceEntries S.fine)

/-- The connected embedded list has no duplicates. -/
theorem allCutoffConnectedExpandedSourceEntryPairs_nodup
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) :
    (allCutoffConnectedExpandedSourceEntryPairs
      S rootFaceId targetFaceId).Nodup := by
  unfold allCutoffConnectedExpandedSourceEntryPairs
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
  · exact List.filter_sublist.nodup
      (slabObservableFourCellSourcePairs_nodup
        S.fine rootFaceId targetFaceId)
  · intro left _ right _ heq
    exact slabObservablePairExpandedSourceEntries_injective
      S.fine rootFaceId heq

/-- Complete attached expanded-source pair carrier. -/
def allCutoffExpandedSourceEntryPairs (S : SlabScalePair) :
    List (AllCutoffExpandedSourceEntry S.fine ×
      AllCutoffExpandedSourceEntry S.fine) :=
  cartesian (allCutoffExpandedSourceEntries S.fine)
    (allCutoffExpandedSourceEntries S.fine)

theorem allCutoffConnectedExpandedSourceEntryPairs_subset
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) :
    ∀ sourcePair,
      sourcePair ∈ allCutoffConnectedExpandedSourceEntryPairs
          S rootFaceId targetFaceId →
        sourcePair ∈ allCutoffExpandedSourceEntryPairs S := by
  intro sourcePair hsourcePair
  obtain ⟨source, _, heq⟩ := List.mem_map.mp hsourcePair
  rw [← heq]
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · unfold allCutoffExpandedSourceEntries
    exact List.mem_attach (allCutoffExpandedSources S.fine)
      (slabObservablePairLeftExpandedSourceEntry S.fine source)
  · unfold allCutoffExpandedSourceEntries
    exact List.mem_attach (allCutoffExpandedSources S.fine)
      (slabObservablePairRightExpandedSourceEntry S.fine source)

/-! ## 3. Targetwise connected and full marginals -/

def allCutoffExpandedSourceEntryPairTargetWeight
    (S : SlabScalePair)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget)
    (sources : AllCutoffExpandedSourceEntry S.fine ×
      AllCutoffExpandedSourceEntry S.fine) : Q' :=
  allCutoffExpandedSourceJointWeight S target.1 sources.1.1 *
    allCutoffExpandedSourceJointWeight S target.2 sources.2.1

/-- The targetwise contribution from support-connected expanded source
pairs. -/
def allCutoffConnectedExpandedTargetContribution
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) : Q' :=
  listQSum (allCutoffExpandedSourceEntryPairTargetWeight S target)
    (allCutoffConnectedExpandedSourceEntryPairs
      S rootFaceId targetFaceId)

/-- The complete attached expanded-source target marginal. -/
def allCutoffFullExpandedTargetMass
    (S : SlabScalePair)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) : Q' :=
  listQSum (allCutoffExpandedSourceEntryPairTargetWeight S target)
    (allCutoffExpandedSourceEntryPairs S)

private theorem listQSum_subset_le_of_nodup_nonnegative
    {A : Type} [DecidableEq A] (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ (selected : List A), selected.Nodup →
      ∀ ambient : List A,
        (∀ item, item ∈ selected → item ∈ ambient) →
          listQSum weight selected ≤ listQSum weight ambient
  | [], _, ambient, _ =>
      listQSum_nonnegative_on weight ambient
        (fun item _ => hweight item)
  | head :: tail, hnodup, ambient, hsubset => by
      have hparts := List.nodup_cons.mp hnodup
      have hhead := hsubset head List.mem_cons_self
      have htailSubset : ∀ item, item ∈ tail →
          item ∈ ambient.erase head := by
        intro item hitem
        apply mem_erase_of_mem_of_ne
        · intro heq
          subst item
          exact hparts.1 hitem
        · exact hsubset item (List.mem_cons_of_mem head hitem)
      have htail := listQSum_subset_le_of_nodup_nonnegative
        weight hweight tail hparts.2 (ambient.erase head) htailSubset
      have hadd := Q'.add_le_add
        (Q'.le_refl' (weight head)) htail
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (listQSum_erase_decompose weight ambient head hhead)))

theorem allCutoffExpandedSourceJointWeight_nonnegative
    (S : SlabScalePair) (target : AllCutoffRetainedTarget)
    (source : AllCutoffExpandedSource S.fine) :
    (0 : Q') ≤ allCutoffExpandedSourceJointWeight S target source := by
  unfold allCutoffExpandedSourceJointWeight
    allCutoffExpandedSourceNormalizedMass
    allCutoffExpandedSourceWeight Q'.divPos
    allCutoffExpandedSourceKernel
  apply Q'.mul_nonneg
  · exact Q'.mul_nonneg _ _
      (retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.half
          source.1.1 source.2)
      (Q'.le_of_lt
        (Q'.recipPos_pos S.fine.physicalPartition
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative
            S.fine.cutoff S.fine.extent)))
  · exact allCutoffRetainedFineIntertwinerKernel_nonnegative
      S source.1 target

theorem allCutoffExpandedSourceEntryPairTargetWeight_nonnegative
    (S : SlabScalePair)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget)
    (sources : AllCutoffExpandedSourceEntry S.fine ×
      AllCutoffExpandedSourceEntry S.fine) :
    (0 : Q') ≤
      allCutoffExpandedSourceEntryPairTargetWeight S target sources := by
  exact Q'.mul_nonneg _ _
    (allCutoffExpandedSourceJointWeight_nonnegative
      S target.1 sources.1.1)
    (allCutoffExpandedSourceJointWeight_nonnegative
      S target.2 sources.2.1)

/-- Attaching the grouped expanded source carrier does not change the full
target marginal, which is the actual product enriched blocked law. -/
theorem allCutoffFullExpandedTargetMass_eqv_blockedProduct
    (S : SlabScalePair)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    allCutoffFullExpandedTargetMass S target ≈
      allCutoffRetainedFineIntertwinerBlockedMass S target.1 *
        allCutoffRetainedFineIntertwinerBlockedMass S target.2 := by
  refine Q'.eqv_trans _
    (allCutoffExpandedSourceBlockedMass S target.1 *
      allCutoffExpandedSourceBlockedMass S target.2) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
          (fun source : AllCutoffExpandedSourceEntry S.fine =>
            allCutoffExpandedSourceJointWeight S target.1 source.1)
          (allCutoffExpandedSourceEntries S.fine) *
        listQSum
          (fun source : AllCutoffExpandedSourceEntry S.fine =>
            allCutoffExpandedSourceJointWeight S target.2 source.1)
          (allCutoffExpandedSourceEntries S.fine)) _ ?_ ?_
    · exact listQSum_cartesian_product
        (fun source : AllCutoffExpandedSourceEntry S.fine =>
          allCutoffExpandedSourceJointWeight S target.1 source.1)
        (fun source : AllCutoffExpandedSourceEntry S.fine =>
          allCutoffExpandedSourceJointWeight S target.2 source.1)
        (allCutoffExpandedSourceEntries S.fine)
        (allCutoffExpandedSourceEntries S.fine)
    · apply Q'.eqv_of_eq
      rw [show listQSum
          (fun source : AllCutoffExpandedSourceEntry S.fine =>
            allCutoffExpandedSourceJointWeight S target.1 source.1)
          (allCutoffExpandedSourceEntries S.fine) =
        allCutoffExpandedSourceBlockedMass S target.1 by
          unfold allCutoffExpandedSourceEntries
            allCutoffExpandedSourceBlockedMass
          exact listQSum_attach
            (allCutoffExpandedSourceJointWeight S target.1)
            (allCutoffExpandedSources S.fine)]
      rw [show listQSum
          (fun source : AllCutoffExpandedSourceEntry S.fine =>
            allCutoffExpandedSourceJointWeight S target.2 source.1)
          (allCutoffExpandedSourceEntries S.fine) =
        allCutoffExpandedSourceBlockedMass S target.2 by
          unfold allCutoffExpandedSourceEntries
            allCutoffExpandedSourceBlockedMass
          exact listQSum_attach
            (allCutoffExpandedSourceJointWeight S target.2)
            (allCutoffExpandedSources S.fine)]
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (allCutoffExpandedSourceBlockedMass_eqv_blockedMass
          S target.1))
      (Q'.mul_eqv_congr_left _ _ _
        (allCutoffExpandedSourceBlockedMass_eqv_blockedMass
          S target.2))

/-- **Targetwise submeasure theorem.**  The connected source contribution is
nonnegative and no larger than the genuine product enriched blocked mass. -/
theorem allCutoffConnectedExpandedTargetContribution_interval
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    (0 : Q') ≤
        allCutoffConnectedExpandedTargetContribution
          S rootFaceId targetFaceId target ∧
      allCutoffConnectedExpandedTargetContribution
          S rootFaceId targetFaceId target ≤
        allCutoffRetainedFineIntertwinerBlockedMass S target.1 *
          allCutoffRetainedFineIntertwinerBlockedMass S target.2 := by
  constructor
  · unfold allCutoffConnectedExpandedTargetContribution
    apply listQSum_nonnegative_on
    intro sources _
    exact allCutoffExpandedSourceEntryPairTargetWeight_nonnegative
      S target sources
  · refine Q'.le_trans' _ _ _
      (listQSum_subset_le_of_nodup_nonnegative
        (allCutoffExpandedSourceEntryPairTargetWeight S target)
        (allCutoffExpandedSourceEntryPairTargetWeight_nonnegative S target)
        (allCutoffConnectedExpandedSourceEntryPairs
          S rootFaceId targetFaceId)
        (allCutoffConnectedExpandedSourceEntryPairs_nodup
          S rootFaceId targetFaceId)
        (allCutoffExpandedSourceEntryPairs S)
        (allCutoffConnectedExpandedSourceEntryPairs_subset
          S rootFaceId targetFaceId)) ?_
    exact Q'.le_of_eqv
      (allCutoffFullExpandedTargetMass_eqv_blockedProduct S target)

/-! ## Axiom audit -/

#print axioms AllCutoffExpandedSourceEntry.eq_of_key_eq
#print axioms allCutoffConnectedExpandedSourceEntryPairs_subset
#print axioms allCutoffFullExpandedTargetMass_eqv_blockedProduct
#print axioms allCutoffConnectedExpandedTargetContribution_interval

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure
