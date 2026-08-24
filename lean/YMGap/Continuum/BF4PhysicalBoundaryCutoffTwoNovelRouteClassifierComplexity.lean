/-
# Shell-polynomial complexity of the cutoff-two novel routes

The cutoff-two classifier recoding gives exactly `n^2 + 130 n` novel ordered
endpoint pairs, where `n` is the genuinely new shell length.  Every selected
route is loop-erased, so its literal directed-edge list has length at most the
full carrier length `65 + n`.  Composing these two facts bounds the complete
weighted occurrence list by

  `(n^2 + 130 n) * (65 + n)`.

The routed-edge projection has exactly the same length, and erasing duplicate
edges can only decrease it.  Hence both support lists used by the routed ratio
ceilings obey the same shell-only polynomial bound.

This controls finite enumeration complexity only.  It does not bound the
shell size, occurrence weights, edge loads, ratio ceilings, cofinal capacity,
thermodynamic/continuum construction, or the Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

/-! ## 1. One route and a bounded flat-map -/

theorem cutoffTwoSimpleWeightedPathOccurrences_length_le_carrier
    (later left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    (cutoffTwoSimpleWeightedPathOccurrences later left right).length ≤
      (cutoffTwoEdgeLoadFullStates later).length := by
  unfold cutoffTwoSimpleWeightedPathOccurrences
  rw [dif_pos hleft, dif_pos hright]
  simp only [List.length_map]
  rw [PositiveKernelChainIn.directedEdges_length_eq_edgeLength]
  exact centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le
    cutoffTwoHalfCoupling (by decide) later 0
    left right hleft hright

private theorem flatMap_length_le_mul_local
    {A B : Type} (bound : Nat) (block : A → List B) :
    ∀ items : List A,
      (∀ item, item ∈ items → (block item).length ≤ bound) →
      (items.flatMap block).length ≤ items.length * bound
  | [], _ => by simp
  | head :: tail, hblock => by
      have hhead : (block head).length ≤ bound :=
        hblock head List.mem_cons_self
      have htail : (tail.flatMap block).length ≤ tail.length * bound :=
        flatMap_length_le_mul_local bound block tail
          (fun item hitem => hblock item (List.mem_cons_of_mem head hitem))
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      calc
        (block head).length + (tail.flatMap block).length ≤
            bound + tail.length * bound := Nat.add_le_add hhead htail
        _ = (tail.length + 1) * bound := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_comm _ _

theorem cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_pair_mul_carrier
    (later : Nat) :
    (cutoffTwoNovelSimpleWeightedEdgeOccurrences later).length ≤
      (cutoffTwoNovelEndpointPairs later).length *
        (cutoffTwoEdgeLoadFullStates later).length := by
  unfold cutoffTwoNovelSimpleWeightedEdgeOccurrences
  apply flatMap_length_le_mul_local
  intro pair hpair
  have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
  exact cutoffTwoSimpleWeightedPathOccurrences_length_le_carrier
    later pair.1 pair.2 hfull.1 hfull.2

/-! ## 2. Eliminate the inherited carrier from the variable cost -/

theorem cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_shellPolynomial
    {later : Nat} (hcutoff : 2 ≤ later) :
    (cutoffTwoNovelSimpleWeightedEdgeOccurrences later).length ≤
      ((cutoffTwoEdgeLoadNewStates later).length *
          (cutoffTwoEdgeLoadNewStates later).length +
        130 * (cutoffTwoEdgeLoadNewStates later).length) *
      (65 + (cutoffTwoEdgeLoadNewStates later).length) := by
  calc
    (cutoffTwoNovelSimpleWeightedEdgeOccurrences later).length ≤
        (cutoffTwoNovelEndpointPairs later).length *
          (cutoffTwoEdgeLoadFullStates later).length :=
      cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_pair_mul_carrier
        later
    _ =
        ((cutoffTwoEdgeLoadNewStates later).length *
            (cutoffTwoEdgeLoadNewStates later).length +
          130 * (cutoffTwoEdgeLoadNewStates later).length) *
        (65 + (cutoffTwoEdgeLoadNewStates later).length) := by
      rw [cutoffTwoNovelEndpointPairs_length hcutoff,
        cutoffTwoEdgeLoadFullStates_length_eq_65_add_new hcutoff]

/-! ## 3. The routed and distinct supports inherit the same bound -/

theorem cutoffTwoNovelRoutedDirectedEdges_length_eq_occurrences
    (later : Nat) :
    (cutoffTwoNovelRoutedDirectedEdges later).length =
      (cutoffTwoNovelSimpleWeightedEdgeOccurrences later).length := by
  unfold cutoffTwoNovelRoutedDirectedEdges
  simp only [List.length_map]

private theorem eraseDups_length_le_local
    {A : Type} [BEq A] (items : List A) :
    items.eraseDups.length ≤ items.length := by
  cases items with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hfilter := List.length_filter_le
        (fun item : A => !item == head) tail
      have ih := eraseDups_length_le_local
        (tail.filter fun item => !item == head)
      omega
termination_by items.length
decreasing_by
  simp_wf
  omega

theorem cutoffTwoNovelRoutedDistinctDirectedEdges_length_le_occurrences
    (later : Nat) :
    (cutoffTwoNovelRoutedDistinctDirectedEdges later).length ≤
      (cutoffTwoNovelSimpleWeightedEdgeOccurrences later).length := by
  unfold cutoffTwoNovelRoutedDistinctDirectedEdges
  exact Nat.le_trans
    (eraseDups_length_le_local (cutoffTwoNovelRoutedDirectedEdges later))
    (Nat.le_of_eq
      (cutoffTwoNovelRoutedDirectedEdges_length_eq_occurrences later))

theorem cutoffTwoNovelRoutedDistinctDirectedEdges_length_le_shellPolynomial
    {later : Nat} (hcutoff : 2 ≤ later) :
    (cutoffTwoNovelRoutedDistinctDirectedEdges later).length ≤
      ((cutoffTwoEdgeLoadNewStates later).length *
          (cutoffTwoEdgeLoadNewStates later).length +
        130 * (cutoffTwoEdgeLoadNewStates later).length) *
      (65 + (cutoffTwoEdgeLoadNewStates later).length) := by
  exact Nat.le_trans
    (cutoffTwoNovelRoutedDistinctDirectedEdges_length_le_occurrences later)
    (cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_shellPolynomial
      hcutoff)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity.cutoffTwoSimpleWeightedPathOccurrences_length_le_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity.cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_pair_mul_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity.cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_shellPolynomial
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity.cutoffTwoNovelRoutedDirectedEdges_length_eq_occurrences
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity.cutoffTwoNovelRoutedDistinctDirectedEdges_length_le_occurrences
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity.cutoffTwoNovelRoutedDistinctDirectedEdges_length_le_shellPolynomial
