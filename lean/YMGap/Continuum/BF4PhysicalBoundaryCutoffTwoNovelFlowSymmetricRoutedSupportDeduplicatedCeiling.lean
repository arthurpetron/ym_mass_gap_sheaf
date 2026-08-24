/-
# Deduplicate the finite routed-support ceiling

The routed support is assembled from one directed-edge list per endpoint-pair
path, so it can contain many repeated edges.  Repetitions do not change a
maximum.  This module erases them, proves both finite maxima bound each other,
and reconstructs the same routed-prefix ceiling data from the distinct list.

This contracts redundant finite data only.  It proves no payment, cofinal
estimate, thermodynamic/continuum construction, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum

/-! ## 1. Distinct literal routed support -/

def cutoffTwoNovelRoutedDistinctDirectedEdges (later : Nat) :
    List (Nat × Nat) :=
  (cutoffTwoNovelRoutedDirectedEdges later).eraseDups

theorem cutoffTwoNovelRoutedDistinctDirectedEdges_mem_iff
    {later : Nat} {edge : Nat × Nat} :
    edge ∈ cutoffTwoNovelRoutedDistinctDirectedEdges later ↔
      edge ∈ cutoffTwoNovelRoutedDirectedEdges later := by
  unfold cutoffTwoNovelRoutedDistinctDirectedEdges
  exact List.mem_eraseDups

def cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling
    (later : Nat) : Q' :=
  listQMaxZero
    (fun edge => cutoffTwoConditionalReverseForwardRatio
      later edge.1 edge.2)
    (cutoffTwoNovelRoutedDistinctDirectedEdges later)

theorem cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling_nonnegative
    (later : Nat) :
    (0 : Q') ≤
      cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later := by
  unfold cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling
  apply listQMaxZero_nonnegative
  intro edge
  exact cutoffTwoConditionalReverseForwardRatio_nonnegative
    later edge.1 edge.2

private theorem listQMaxZero_le_of_bound_local
    {State : Type} (value : State → Q') (bound : Q')
    (hbound : (0 : Q') ≤ bound) :
    ∀ states : List State,
      (∀ state, state ∈ states → value state ≤ bound) →
      listQMaxZero value states ≤ bound
  | [], _ => hbound
  | head :: tail, hvalue => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      exact ⟨hvalue head List.mem_cons_self,
        listQMaxZero_le_of_bound_local value bound hbound tail
          (fun state hstate =>
            hvalue state (List.mem_cons_of_mem head hstate))⟩

theorem cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling_le_routedFiniteCeiling
    (later : Nat) :
    cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later ≤
      cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later := by
  unfold cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling
  apply listQMaxZero_le_of_bound_local
    (fun edge : Nat × Nat =>
      cutoffTwoConditionalReverseForwardRatio later edge.1 edge.2)
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later)
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative later)
  intro edge hedge
  exact le_listQMaxZero_of_mem
    (fun routedEdge : Nat × Nat =>
      cutoffTwoConditionalReverseForwardRatio
        later routedEdge.1 routedEdge.2)
    (cutoffTwoNovelRoutedDirectedEdges later)
    (cutoffTwoNovelRoutedDistinctDirectedEdges_mem_iff.mp hedge)

theorem cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_distinctRoutedFiniteCeiling
    (later : Nat) :
    cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later ≤
      cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later := by
  unfold cutoffTwoConditionalReverseForwardRoutedFiniteCeiling
  apply listQMaxZero_le_of_bound_local
    (fun edge : Nat × Nat =>
      cutoffTwoConditionalReverseForwardRatio later edge.1 edge.2)
    (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later)
    (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling_nonnegative
      later)
  intro edge hedge
  unfold cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling
  exact le_listQMaxZero_of_mem
    (fun routedEdge : Nat × Nat =>
      cutoffTwoConditionalReverseForwardRatio
        later routedEdge.1 routedEdge.2)
    (cutoffTwoNovelRoutedDistinctDirectedEdges later)
    (cutoffTwoNovelRoutedDistinctDirectedEdges_mem_iff.mpr hedge)

/-! ## 2. The distinct maximum supplies the same prefix families -/

def cutoffTwoNovelDistinctRoutedSupportFiniteRatioCeilingData
    (later : Nat) :
    CutoffTwoNovelRoutedPrefixRatioCeilingAt later
      (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later) :=
  let original := cutoffTwoNovelRoutedSupportFiniteRatioCeilingData later
  { rho_nonnegative :=
      cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling_nonnegative
        later
    source_prefix_product_le := fun _pair hpair source target hedge => by
      exact Q'.le_trans' _ _ _
        (original.source_prefix_product_le
          _ hpair source target hedge)
        (qpow_base_mono
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later)
          (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later)
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative
            later)
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_distinctRoutedFiniteCeiling
            later) _)
    target_prefix_product_le := fun _pair hpair source target hedge => by
      exact Q'.le_trans' _ _ _
        (original.target_prefix_product_le
          _ hpair source target hedge)
        (qpow_base_mono
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later)
          (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later)
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative
            later)
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_distinctRoutedFiniteCeiling
            later) _) }

/-! ## 3. Deduplicated and repeated-list ceiling loads bound each other -/

def cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteRatioCeilingLoad
    (later source target : Nat) : Q' :=
  cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
    (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling later)
    later source target

theorem cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteCeilingLoad_le_routedSupportFiniteCeilingLoad
    (later source target : Nat) :
    cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteRatioCeilingLoad
        later source target ≤
      cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
        later source target := by
  unfold cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteRatioCeilingLoad
    BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
  exact cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_mono
    (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling_nonnegative
      later)
    (cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling_le_routedFiniteCeiling
      later)
    later source target

theorem cutoffTwoNovelSymmetricRoutedSupportFiniteCeilingLoad_le_distinctRoutedSupportFiniteCeilingLoad
    (later source target : Nat) :
    cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
        later source target ≤
      cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteRatioCeilingLoad
        later source target := by
  unfold cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteRatioCeilingLoad
    BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
  exact cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_mono
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative later)
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_distinctRoutedFiniteCeiling
      later)
    later source target

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.cutoffTwoNovelRoutedDistinctDirectedEdges_mem_iff
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling_le_routedFiniteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_distinctRoutedFiniteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.cutoffTwoNovelDistinctRoutedSupportFiniteRatioCeilingData
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteCeilingLoad_le_routedSupportFiniteCeilingLoad
