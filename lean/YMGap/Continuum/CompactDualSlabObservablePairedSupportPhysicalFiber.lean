/-
# Finite physical fibers for the paired-support recoupling switch

The two switched physical labellings are functions on face identifiers, but
every production labelling vanishes off the datum's finite face list.  Their
two ordered finite words therefore form a decidable and faithful physical
fiber key.  Filtering the disconnected source four-cell by the key of one
target pair gives a literal duplicate-free list of proof-carrying
contributors, ready for the common-column no-overload theorem.

Constructive contract: finite words, Boolean filters, and structural list
proofs only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabExpandedTargetKey
import YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The disconnected paired-support source list -/

def slabObservablePairedSupportSeparatedFourCellSourcePairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId).filter fun pair =>
      !(slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair)

abbrev SlabObservablePairedSupportSeparatedSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :=
  {pair // pair ∈ slabObservablePairedSupportSeparatedFourCellSourcePairs
    D rootFaceId targetFaceId}

def slabObservablePairedSupportSeparatedSources
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :=
  (slabObservablePairedSupportSeparatedFourCellSourcePairs
    D rootFaceId targetFaceId).attach

theorem SlabObservablePairedSupportSeparatedSource.pair_mem_fourCell
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    source.1 ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId :=
  (List.mem_filter.mp source.2).1

theorem SlabObservablePairedSupportSeparatedSource.disconnected
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source.1 = false := by
  have hseparated := (List.mem_filter.mp source.2).2
  cases hconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source.1 with
  | false => rfl
  | true =>
      simp only [hconnected, Bool.not_true,
        Bool.false_eq_true] at hseparated

theorem slabObservablePairedSupportSeparatedFourCellSourcePairs_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservablePairedSupportSeparatedFourCellSourcePairs
      D rootFaceId targetFaceId).Nodup :=
  List.filter_sublist.nodup
    (slabObservableFourCellSourcePairs_nodup
      D rootFaceId targetFaceId)

theorem slabObservablePairedSupportSeparatedSources_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservablePairedSupportSeparatedSources
      D rootFaceId targetFaceId).Nodup :=
  attach_nodup_of_nodup _
    (slabObservablePairedSupportSeparatedFourCellSourcePairs_nodup
      D rootFaceId targetFaceId)

/-! ## 2. A faithful finite physical key -/

structure SlabObservablePairedSupportPhysicalKey where
  leftWord : List Nat
  rightWord : List Nat
  deriving DecidableEq

def slabObservablePhysicalPairKey
    (D : SlabPhysicalData)
    (leftPhysical rightPhysical : SlabLabelling) :
    SlabObservablePairedSupportPhysicalKey where
  leftWord := finiteEdgeLabellingWord D.faceEdges leftPhysical
  rightWord := finiteEdgeLabellingWord D.faceEdges rightPhysical

def slabObservablePairedSupportSourcePhysicalKey
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SlabObservablePairedSupportPhysicalKey :=
  slabObservablePhysicalPairKey D
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId pair)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId pair)

def slabObservablePairPhysicalKey
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SlabObservablePairedSupportPhysicalKey :=
  slabObservablePhysicalPairKey D pair.1.1.1 pair.2.1.1

theorem slabObservablePairLeftPhysical_supported
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    ∀ faceId, faceId ∉ D.faceEdges → pair.1.1.1 faceId = 0 :=
  (boundedEdgeLabellings_sound D.cutoff D.faceEdges
    pair.1.1.1 pair.1.physical_mem).2

theorem slabObservablePairRightPhysical_supported
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    ∀ faceId, faceId ∉ D.faceEdges → pair.2.1.1 faceId = 0 :=
  (boundedEdgeLabellings_sound D.cutoff D.faceEdges
    pair.2.1.1
    (mem_slabExpandedFineSources_iff.mp pair.2.2).1).2

theorem slabObservablePairSupportSwitchedLeftPhysical_supported
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    ∀ faceId, faceId ∉ D.faceEdges →
      slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId pair faceId = 0 := by
  intro faceId hface
  cases hmask : slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId faceId with
  | false =>
      simpa [slabObservablePairSupportSwitchedLeftPhysical,
        twoReplicaFaceSwapLeft, hmask] using
        slabObservablePairLeftPhysical_supported D pair faceId hface
  | true =>
      simpa [slabObservablePairSupportSwitchedLeftPhysical,
        twoReplicaFaceSwapLeft, hmask] using
        slabObservablePairRightPhysical_supported D pair faceId hface

theorem slabObservablePairSupportSwitchedRightPhysical_supported
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    ∀ faceId, faceId ∉ D.faceEdges →
      slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId pair faceId = 0 := by
  intro faceId hface
  cases hmask : slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId faceId with
  | false =>
      simpa [slabObservablePairSupportSwitchedRightPhysical,
        twoReplicaFaceSwapRight, hmask] using
        slabObservablePairRightPhysical_supported D pair faceId hface
  | true =>
      simpa [slabObservablePairSupportSwitchedRightPhysical,
        twoReplicaFaceSwapRight, hmask] using
        slabObservablePairLeftPhysical_supported D pair faceId hface

/-- Equality of finite physical keys identifies both switched fields with
the corresponding fields of the target pair. -/
theorem slabObservablePairedSupportPhysicalKey_eq_target_fields
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (source target : SlabObservableTwoReplicaPair D rootFaceId)
    (hkey : slabObservablePairedSupportSourcePhysicalKey
        D targetFaceId source =
      slabObservablePairPhysicalKey D target) :
    slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId source = target.1.1.1 ∧
      slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId source = target.2.1.1 := by
  constructor
  · apply edgeLabelling_eq_of_word_eq_of_supported D.faceEdges
    · exact slabObservablePairSupportSwitchedLeftPhysical_supported
        D targetFaceId source
    · exact slabObservablePairLeftPhysical_supported D target
    · exact congrArg SlabObservablePairedSupportPhysicalKey.leftWord hkey
  · apply edgeLabelling_eq_of_word_eq_of_supported D.faceEdges
    · exact slabObservablePairSupportSwitchedRightPhysical_supported
        D targetFaceId source
    · exact slabObservablePairRightPhysical_supported D target
    · exact congrArg SlabObservablePairedSupportPhysicalKey.rightWord hkey

/-! ## 3. The literal fiber over one target physical pair -/

def slabObservablePairedSupportTargetFiberSourceList
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :=
  (slabObservablePairedSupportSeparatedSources
    D rootFaceId targetFaceId).filter fun source =>
      decide (slabObservablePairedSupportSourcePhysicalKey
          D targetFaceId source.1 =
        slabObservablePairPhysicalKey D target)

abbrev SlabObservablePairedSupportTargetFiberSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :=
  {source // source ∈ slabObservablePairedSupportTargetFiberSourceList
    D rootFaceId targetFaceId target}

def slabObservablePairedSupportTargetFiberSources
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabObservablePairedSupportTargetFiberSource
      D rootFaceId targetFaceId target) :=
  (slabObservablePairedSupportTargetFiberSourceList
    D rootFaceId targetFaceId target).attach

theorem SlabObservablePairedSupportTargetFiberSource.key_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (source : SlabObservablePairedSupportTargetFiberSource
      D rootFaceId targetFaceId target) :
    slabObservablePairedSupportSourcePhysicalKey
        D targetFaceId source.1.1 =
      slabObservablePairPhysicalKey D target := by
  exact of_decide_eq_true (List.mem_filter.mp source.2).2

def SlabObservablePairedSupportTargetFiberSource.toContributor
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (source : SlabObservablePairedSupportTargetFiberSource
      D rootFaceId targetFaceId target) :
    SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId target.1.1.1 target.2.1.1 :=
  let hfields := slabObservablePairedSupportPhysicalKey_eq_target_fields
    D targetFaceId source.1.1 target source.key_eq
  { pair := source.1.1
    pair_mem := source.1.pair_mem_fourCell
    disconnected := source.1.disconnected
    leftPhysical_eq := hfields.1
    rightPhysical_eq := hfields.2 }

def slabObservablePairedSupportTargetFiberContributors
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId target.1.1.1 target.2.1.1) :=
  (slabObservablePairedSupportTargetFiberSources
    D rootFaceId targetFaceId target).map
      SlabObservablePairedSupportTargetFiberSource.toContributor

private theorem nodup_map_of_injective {A B : Type}
    (map : A → B) (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | item :: items, hitems => by
      have hparts := List.nodup_cons.mp hitems
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
        exact hparts.1 (hinjective item other heq.symm ▸ hother)
      · exact nodup_map_of_injective map hinjective hparts.2

theorem slabObservablePairedSupportTargetFiberContributors_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    (slabObservablePairedSupportTargetFiberContributors
      D rootFaceId targetFaceId target).Nodup := by
  apply nodup_map_of_injective
    SlabObservablePairedSupportTargetFiberSource.toContributor
  · intro left right heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun contributor : SlabObservablePairedSupportContributorAt
          D rootFaceId targetFaceId target.1.1.1 target.2.1.1 =>
        contributor.pair)
      heq
  · exact attach_nodup_of_nodup _
      (List.filter_sublist.nodup
        (slabObservablePairedSupportSeparatedSources_nodup
          D rootFaceId targetFaceId))

/-! ## 4. Every concrete target physical fiber obeys column capacity -/

theorem slabObservablePairedSupportTargetFiberColumnWeight_sum_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetPair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetColumn : SlabPhysicalPairRecouplingTargetAssignment
      D.extent targetPair.1.1.1 targetPair.2.1.1) :
    listQSum
        (slabObservablePairedSupportContributorColumnWeight
          D rootFaceId targetFaceId
          targetPair.1.1.1 targetPair.2.1.1
          htarget targetColumn)
        (slabObservablePairedSupportTargetFiberContributors
          D rootFaceId targetFaceId targetPair) ≤ 1 :=
  slabObservablePairedSupportContributorColumnWeight_sum_le_one
    D rootFaceId targetFaceId
    targetPair.1.1.1 targetPair.2.1.1
    htarget targetColumn
    (slabObservablePairedSupportTargetFiberContributors
      D rootFaceId targetFaceId targetPair)
    (slabObservablePairedSupportTargetFiberContributors_nodup
      D rootFaceId targetFaceId targetPair)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber.slabObservablePairedSupportSeparatedSources_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber.slabObservablePairedSupportPhysicalKey_eq_target_fields
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber.slabObservablePairedSupportTargetFiberContributors_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber.slabObservablePairedSupportTargetFiberColumnWeight_sum_le_one
