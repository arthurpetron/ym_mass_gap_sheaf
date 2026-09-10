/-
# One typed carrier for the global connected cross-scale sum

The global bound of the preceding module is written as a nested finite sum:
first over positive fine-source pairs, then over the connected coarse-target
pairs belonging to that source pair.  This module flattens those dependent
fibers into one proof-carrying carrier.

Every entry retains its literal source pair, literal target pair, proof of
connected-carrier membership, canonical observable-to-source path, and
target support component.  Both the normalized joint mass and the refined
distance/residual/ground-normalized mass are proved to be sums on this same
carrier.  This is the exact input needed for a later component/terminal
fiber map; no entropy or strictness estimate is asserted here.

Constructive contract: finite `List.flatMap`, attached membership proofs,
and rational sum equalities only; no classical choice, proof hole, trusted
external computation, noncomputable declaration, enlarged heartbeat budget,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier

namespace YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The dependent connected entry type -/

/-- One global cross-scale connected entry.  The target-membership proof is
indexed by the literal positive fine-source pair carried by the same entry. -/
structure FinePacketGlobalConnectedEntry
    (S : SlabScalePair) (observableFaceId : Nat) : Type where
  sources : PositivePhysicalSourcePair S
  targets : EdgeLabelling × EdgeLabelling
  target_mem : targets ∈ finePacketFaceResponseConnectedActivePairs
    S sources.1.1 sources.2.1 observableFaceId

def finePacketGlobalConnectedEntryOfTarget
    (S : SlabScalePair) (observableFaceId : Nat)
    (sources : PositivePhysicalSourcePair S)
    (target : {pair // pair ∈ finePacketFaceResponseConnectedActivePairs
      S sources.1.1 sources.2.1 observableFaceId}) :
    FinePacketGlobalConnectedEntry S observableFaceId :=
  { sources := sources
    targets := target.1
    target_mem := target.2 }

def finePacketGlobalConnectedSourceBlock
    (S : SlabScalePair) (observableFaceId : Nat)
    (sources : PositivePhysicalSourcePair S) :
    List (FinePacketGlobalConnectedEntry S observableFaceId) :=
  (finePacketFaceResponseConnectedActivePairs
    S sources.1.1 sources.2.1 observableFaceId).attach.map
      (finePacketGlobalConnectedEntryOfTarget S observableFaceId sources)

/-- The global connected carrier is the dependent disjoint union of the
connected target fiber over every positive fine-source pair. -/
def finePacketGlobalConnectedEntries
    (S : SlabScalePair) (observableFaceId : Nat) :
    List (FinePacketGlobalConnectedEntry S observableFaceId) :=
  (positivePhysicalSourcePairs S).flatMap
    (finePacketGlobalConnectedSourceBlock S observableFaceId)

private theorem nodup_map_of_injective_local {A B : Type}
    (map : A → B) (hinjective : Function.Injective map) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective_local map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective heq.symm) ▸ hitem)

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

theorem finePacketGlobalConnectedSourceBlock_nodup
    (S : SlabScalePair) (observableFaceId : Nat)
    (sources : PositivePhysicalSourcePair S) :
    (finePacketGlobalConnectedSourceBlock
      S observableFaceId sources).Nodup := by
  unfold finePacketGlobalConnectedSourceBlock
  apply nodup_map_of_injective_local
  · intro left right heq
    apply Subtype.ext
    exact congrArg
      (fun entry : FinePacketGlobalConnectedEntry S observableFaceId =>
        entry.targets) heq
  · exact attach_nodup_of_nodup _
      (finePacketFaceResponseConnectedActivePairs_nodup
        S sources.1.1 sources.2.1 observableFaceId)

theorem finePacketGlobalConnectedEntries_nodup
    (S : SlabScalePair) (observableFaceId : Nat) :
    (finePacketGlobalConnectedEntries S observableFaceId).Nodup := by
  unfold finePacketGlobalConnectedEntries
  apply nodup_flatMap_of_disjoint_blocks_local
  · exact positivePhysicalSourcePairs_nodup S
  · intro sources _
    exact finePacketGlobalConnectedSourceBlock_nodup
      S observableFaceId sources
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftTarget, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightTarget, _, heq⟩ := List.mem_map.mp hright
    exact hne (congrArg
      (fun entry : FinePacketGlobalConnectedEntry S observableFaceId =>
        entry.sources) heq.symm)

/-! ## 2. Canonical component data retained by an entry -/

def finePacketGlobalConnectedEntryPath
    (S : SlabScalePair) (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) :
    FinePacketObservableConnectedDisagreementPath
      S entry.sources.1.1 entry.sources.2.1 observableFaceId entry.targets :=
  finePacketFaceResponseConnectedActivePairPath
    S entry.sources.1.1 entry.sources.2.1 observableFaceId hobservableFace
      entry.targets entry.target_mem

def finePacketGlobalConnectedEntryTargetComponent
    (S : SlabScalePair) (observableFaceId : Nat)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) : List Nat :=
  slabTwoReplicaTargetSupportComponent S.coarse.extent
    entry.targets.1 entry.targets.2 observableFaceId

theorem finePacketGlobalConnectedEntry_source_mem_targetComponent
    (S : SlabScalePair) (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) :
    (finePacketGlobalConnectedEntryPath
      S observableFaceId hobservableFace entry).sourceFaceId ∈
      finePacketGlobalConnectedEntryTargetComponent
        S observableFaceId entry :=
  (finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry).source_mem_targetComponent

theorem finePacketGlobalConnectedEntry_observable_mem_targetComponent
    (S : SlabScalePair) (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) :
    observableFaceId ∈ finePacketGlobalConnectedEntryTargetComponent
      S observableFaceId entry :=
  (finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry).observable_mem_targetComponent

/-! ## 3. The two weights on the same carrier -/

def finePacketGlobalConnectedEntryNormalizedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) : Q' :=
  finePacketOrientedNormalizedJointPairWeight
    S hfineCutoff hcoarseCoupling orientation
      entry.sources.1 entry.sources.2 entry.targets

def finePacketGlobalConnectedEntryRefinedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) : Q' :=
  finePacketOrientedConnectedDistanceResidualGroundCongestion
    S hfineCutoff hcoarseCoupling rate orientation
      entry.sources.1 entry.sources.2 observableFaceId hobservableFace
      ⟨entry.targets, entry.target_mem⟩

/-! ## 4. Exact flattening of both nested global sums -/

theorem finePacketGlobalNormalizedConnectedJointMass_eqv_entrySum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≈
      listQSum
        (finePacketGlobalConnectedEntryNormalizedWeight
          S hfineCutoff hcoarseCoupling orientation observableFaceId)
        (finePacketGlobalConnectedEntries S observableFaceId) := by
  unfold finePacketGlobalNormalizedConnectedJointMass
    finePacketOrientedNormalizedConnectedJointMass
    finePacketGlobalConnectedEntries
  refine Q'.eqv_trans _
    (listQSum
      (fun sources : PositivePhysicalSourcePair S =>
        listQSum
          (finePacketGlobalConnectedEntryNormalizedWeight
            S hfineCutoff hcoarseCoupling orientation observableFaceId)
          (finePacketGlobalConnectedSourceBlock
            S observableFaceId sources))
      (positivePhysicalSourcePairs S)) _ ?_ ?_
  · apply listQSum_congr
    intro sources
    unfold finePacketGlobalConnectedSourceBlock
    rw [listQSum_map]
    exact Q'.eqv_refl _
  · exact Q'.eqv_symm
      (listQSum_flatMap
        (finePacketGlobalConnectedEntryNormalizedWeight
          S hfineCutoff hcoarseCoupling orientation observableFaceId)
        (finePacketGlobalConnectedSourceBlock S observableFaceId)
        (positivePhysicalSourcePairs S))

theorem finePacketGlobalDistanceResidualGroundCongestionMass_eqv_entrySum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalDistanceResidualGroundCongestionMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≈
      listQSum
        (finePacketGlobalConnectedEntryRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalConnectedEntries S observableFaceId) := by
  unfold finePacketGlobalDistanceResidualGroundCongestionMass
    finePacketOrientedConnectedDistanceResidualGroundCongestionMass
    finePacketGlobalConnectedEntries
  refine Q'.eqv_trans _
    (listQSum
      (fun sources : PositivePhysicalSourcePair S =>
        listQSum
          (finePacketGlobalConnectedEntryRefinedWeight
            S hfineCutoff hcoarseCoupling rate orientation observableFaceId
              hobservableFace)
          (finePacketGlobalConnectedSourceBlock
            S observableFaceId sources))
      (positivePhysicalSourcePairs S)) _ ?_ ?_
  · apply listQSum_congr
    intro sources
    unfold finePacketGlobalConnectedSourceBlock
    rw [listQSum_map]
    exact Q'.eqv_refl _
  · exact Q'.eqv_symm
      (listQSum_flatMap
        (finePacketGlobalConnectedEntryRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalConnectedSourceBlock S observableFaceId)
        (positivePhysicalSourcePairs S))

/-- The preceding global comparison now lives on one literal typed carrier,
ready for component/terminal regrouping. -/
theorem finePacketGlobalConnectedEntryNormalizedSum_le_refinedSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketGlobalConnectedEntryNormalizedWeight
          S hfineCutoff hcoarseCoupling orientation observableFaceId)
        (finePacketGlobalConnectedEntries S observableFaceId) ≤
      listQSum
        (finePacketGlobalConnectedEntryRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalConnectedEntries S observableFaceId) := by
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (finePacketGlobalNormalizedConnectedJointMass_eqv_entrySum
        S hfineCutoff hcoarseCoupling orientation observableFaceId))
    (Q'.le_trans' _ _ _
      (finePacketGlobalNormalizedConnectedJointMass_le_refinedCarrier
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate
          orientation observableFaceId hobservableFace)
      (Q'.le_of_eqv
        (finePacketGlobalDistanceResidualGroundCongestionMass_eqv_entrySum
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)))

/-! ## 5. Axiom audit -/

#print axioms FinePacketGlobalConnectedEntry
#print axioms finePacketGlobalConnectedEntryOfTarget
#print axioms finePacketGlobalConnectedSourceBlock
#print axioms finePacketGlobalConnectedEntries
#print axioms finePacketGlobalConnectedSourceBlock_nodup
#print axioms finePacketGlobalConnectedEntries_nodup
#print axioms finePacketGlobalConnectedEntryPath
#print axioms finePacketGlobalConnectedEntryTargetComponent
#print axioms finePacketGlobalConnectedEntry_source_mem_targetComponent
#print axioms finePacketGlobalConnectedEntry_observable_mem_targetComponent
#print axioms finePacketGlobalConnectedEntryNormalizedWeight
#print axioms finePacketGlobalConnectedEntryRefinedWeight
#print axioms finePacketGlobalNormalizedConnectedJointMass_eqv_entrySum
#print axioms finePacketGlobalDistanceResidualGroundCongestionMass_eqv_entrySum
#print axioms finePacketGlobalConnectedEntryNormalizedSum_le_refinedSum

end YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
