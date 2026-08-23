/-
# A finite ratio ceiling restricted to the actual novel routed support

The carrier-wide reverse/forward ratio maximum includes positive edges never
used by the chosen novel paths.  This module flattens the literal directed
edges of those paths, takes a located maximum only over that routed support,
and proves that it controls both prefix families used by the symmetric load.

Thus every cutoff has a routed-prefix ceiling constructively no larger than
the carrier-wide ceiling.  No
payment of its ceiling load, cofinal uniform bound, thermodynamic/continuum
construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Literal directed support of the novel routes -/

def cutoffTwoNovelRoutedDirectedEdges (later : Nat) : List (Nat × Nat) :=
  (cutoffTwoNovelSimpleWeightedEdgeOccurrences later).map
    (fun occurrence => occurrence.1)

theorem cutoffTwoNovelRoutedPath_edge_mem
    {later : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later)
    {edge : Nat × Nat}
    (hedge : edge ∈ PositiveKernelChainIn.directedEdges
      (cutoffTwoNovelRoutedPath hpair)) :
    edge ∈ cutoffTwoNovelRoutedDirectedEdges later := by
  have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
  let path := cutoffTwoNovelRoutedPath hpair
  let load :=
    (cutoffTwoEdgeLoadWeight later pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
  have hpathOccurrence : (edge, load) ∈
      cutoffTwoSimpleWeightedPathOccurrences
        later pair.1 pair.2 := by
    unfold cutoffTwoSimpleWeightedPathOccurrences
    rw [dif_pos hfull.1, dif_pos hfull.2]
    change (edge, load) ∈
      (PositiveKernelChainIn.directedEdges path).map
        (fun routedEdge => (routedEdge, load))
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  have hall : (edge, load) ∈
      cutoffTwoNovelSimpleWeightedEdgeOccurrences later := by
    unfold cutoffTwoNovelSimpleWeightedEdgeOccurrences
    exact List.mem_flatMap.mpr ⟨pair, hpair, hpathOccurrence⟩
  unfold cutoffTwoNovelRoutedDirectedEdges
  exact List.mem_map.mpr ⟨(edge, load), hall, rfl⟩

/-! ## 2. Located maximum only on routed directed edges -/

def cutoffTwoConditionalReverseForwardRoutedFiniteCeiling
    (later : Nat) : Q' :=
  listQMaxZero
    (fun edge => cutoffTwoConditionalReverseForwardRatio
      later edge.1 edge.2)
    (cutoffTwoNovelRoutedDirectedEdges later)

theorem cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative
    (later : Nat) :
    (0 : Q') ≤
      cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later := by
  unfold cutoffTwoConditionalReverseForwardRoutedFiniteCeiling
  apply listQMaxZero_nonnegative
  intro edge
  exact cutoffTwoConditionalReverseForwardRatio_nonnegative
    later edge.1 edge.2

/-- Restricting the located maximum to literal routed support cannot increase
the carrier-wide finite maximum. -/
theorem cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_finiteCeiling
    (later : Nat) :
    cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later ≤
      cutoffTwoConditionalReverseForwardFiniteCeiling later := by
  have hbound : ∀ edge,
      edge ∈ cutoffTwoNovelRoutedDirectedEdges later →
      cutoffTwoConditionalReverseForwardRatio later edge.1 edge.2 ≤
        cutoffTwoConditionalReverseForwardFiniteCeiling later := by
    intro edge hedge
    unfold cutoffTwoNovelRoutedDirectedEdges at hedge
    obtain ⟨occurrence, hoccurrence, hedgeEq⟩ :=
      List.mem_map.mp hedge
    subst edge
    have hfull := cutoffTwoNovelOccurrence_mem_full
      later occurrence hoccurrence
    unfold cutoffTwoConditionalReverseForwardFiniteCeiling
    exact le_listQMaxZero_of_mem
      (fun carrierEdge : Nat × Nat =>
        cutoffTwoConditionalReverseForwardRatio
          later carrierEdge.1 carrierEdge.2)
      (cartesian
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later))
      ((mem_cartesian_iff _ _ occurrence.1).2 hfull)
  have hlist : ∀ edges : List (Nat × Nat),
      (∀ edge, edge ∈ edges →
        cutoffTwoConditionalReverseForwardRatio later edge.1 edge.2 ≤
          cutoffTwoConditionalReverseForwardFiniteCeiling later) →
      listQMaxZero
          (fun edge => cutoffTwoConditionalReverseForwardRatio
            later edge.1 edge.2) edges ≤
        cutoffTwoConditionalReverseForwardFiniteCeiling later := by
    intro edges hedges
    induction edges with
    | nil =>
        exact cutoffTwoConditionalReverseForwardFiniteCeiling_nonnegative later
    | cons head tail inductionHypothesis =>
        unfold listQMaxZero
        apply (Q'.max'_le_iff' _ _ _).mpr
        exact ⟨hedges head List.mem_cons_self,
          inductionHypothesis (fun edge hedge =>
            hedges edge (List.mem_cons_of_mem head hedge))⟩
  unfold cutoffTwoConditionalReverseForwardRoutedFiniteCeiling
  exact hlist (cutoffTwoNovelRoutedDirectedEdges later) hbound

theorem cutoffTwoConditionalReverseForwardRatio_le_routedFiniteCeiling
    {later : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later)
    {edge : Nat × Nat}
    (hedge : edge ∈ PositiveKernelChainIn.directedEdges
      (cutoffTwoNovelRoutedPath hpair)) :
    Q'.divPos
        (cutoffTwoEdgeLoadConditionalKernel later edge.2 edge.1)
        (cutoffTwoEdgeLoadConditionalKernel later edge.1 edge.2)
        (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
          (PositiveKernelChainIn.directedEdges_mem_support
            (cutoffTwoNovelEndpointPair_mem_full hpair).1
            (cutoffTwoNovelRoutedPath hpair) edge hedge).1
          (PositiveKernelChainIn.directedEdges_kernel_pos
            (cutoffTwoNovelRoutedPath hpair) edge hedge)) ≤
      cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later := by
  have hsupport := PositiveKernelChainIn.directedEdges_mem_support
    (cutoffTwoNovelEndpointPair_mem_full hpair).1
    (cutoffTwoNovelRoutedPath hpair) edge hedge
  have hpositive := PositiveKernelChainIn.directedEdges_kernel_pos
    (cutoffTwoNovelRoutedPath hpair) edge hedge
  have hforward : (0 : Q') <
      cutoffTwoEdgeLoadKernel later edge.1 edge.2 :=
    hpositive
  have hmax := le_listQMaxZero_of_mem
    (fun routedEdge : Nat × Nat =>
      cutoffTwoConditionalReverseForwardRatio
        later routedEdge.1 routedEdge.2)
    (cutoffTwoNovelRoutedDirectedEdges later)
    (cutoffTwoNovelRoutedPath_edge_mem hpair hedge)
  change cutoffTwoConditionalReverseForwardRatio
      later edge.1 edge.2 ≤
    cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later at hmax
  unfold cutoffTwoConditionalReverseForwardRatio at hmax
  rw [dif_pos hsupport.1, dif_pos hsupport.2, dif_pos hforward] at hmax
  exact hmax

/-! ## 3. Prefix edges remain inside their parent route -/

theorem directedEdges_trans_eq_append
    {State : Type} {kernel : State → State → Q'} {support : List State} :
    {first middle last : State} →
    (left : PositiveKernelChainIn kernel support first middle) →
    (right : PositiveKernelChainIn kernel support middle last) →
    PositiveKernelChainIn.directedEdges
        (PositiveKernelChainIn.trans left right) =
      PositiveKernelChainIn.directedEdges left ++
        PositiveKernelChainIn.directedEdges right
  | _, _, _, PositiveKernelChainIn.refl _, right => rfl
  | _, _, _, PositiveKernelChainIn.step positive hnext rest, right => by
      simp only [PositiveKernelChainIn.trans,
        PositiveKernelChainIn.directedEdges, List.cons_append]
      exact congrArg (List.cons _)
        (directedEdges_trans_eq_append rest right)

theorem prefixAtDirectedEdge_directedEdges_subset
    {State : Type} [DecidableEq State]
    {kernel : State → State → Q'} {support : List State} :
    {first last : State} →
    (hfirst : first ∈ support) →
    (path : PositiveKernelChainIn kernel support first last) →
    (edge : State × State) →
    (hedge : edge ∈ PositiveKernelChainIn.directedEdges path) →
    ∀ prefixEdge,
      prefixEdge ∈ PositiveKernelChainIn.directedEdges
        (PositiveKernelChainIn.prefixAtDirectedEdge
          hfirst path edge hedge).pathPrefix →
      prefixEdge ∈ PositiveKernelChainIn.directedEdges path
  | _, _, _, PositiveKernelChainIn.refl _, _, hedge => by
      cases hedge
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) positive hnext rest,
      edge, hedge => by
      by_cases hhead : edge = (first, next)
      · subst edge
        intro prefixEdge hprefix
        simp [PositiveKernelChainIn.prefixAtDirectedEdge] at hprefix
        cases hprefix
      · have htail : edge ∈ PositiveKernelChainIn.directedEdges rest :=
          (List.mem_cons.mp hedge).resolve_left hhead
        intro prefixEdge hprefix
        change prefixEdge ∈
          (first, next) :: PositiveKernelChainIn.directedEdges rest
        simp only [PositiveKernelChainIn.prefixAtDirectedEdge, hhead] at hprefix
        rcases List.mem_cons.mp hprefix with hpHead | hpTail
        · exact List.mem_cons.mpr (Or.inl hpHead)
        · exact List.mem_cons.mpr (Or.inr
            (prefixAtDirectedEdge_directedEdges_subset
              hnext rest edge htail prefixEdge hpTail))

theorem throughEdge_directedEdges_subset
    {State : Type} [DecidableEq State]
    {kernel : State → State → Q'} {support : List State}
    {first last : State}
    (hfirst : first ∈ support)
    (path : PositiveKernelChainIn kernel support first last)
    (edge : State × State)
    (hedge : edge ∈ PositiveKernelChainIn.directedEdges path) :
    ∀ throughEdge,
      throughEdge ∈ PositiveKernelChainIn.directedEdges
        (positiveKernelPrefixThroughEdge
          (PositiveKernelChainIn.prefixAtDirectedEdge
            hfirst path edge hedge)) →
      throughEdge ∈ PositiveKernelChainIn.directedEdges path := by
  intro throughEdge hthrough
  unfold positiveKernelPrefixThroughEdge at hthrough
  rw [directedEdges_trans_eq_append] at hthrough
  rcases List.mem_append.mp hthrough with hprefix | hselected
  · exact prefixAtDirectedEdge_directedEdges_subset
      hfirst path edge hedge throughEdge hprefix
  · change throughEdge ∈ [edge] at hselected
    exact (List.mem_singleton.mp hselected) ▸ hedge

/-! ## 4. A path product controlled by a parent route's support maximum -/

theorem cutoffTwoNovelPathReverseForwardProduct_le_routedFiniteCeilingPow
    {later : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    {first last : Nat} →
    (hfirst : first ∈ cutoffTwoEdgeLoadFullStates later) →
    (path : PositiveKernelChainIn
      (cutoffTwoEdgeLoadKernel later)
      (cutoffTwoEdgeLoadFullStates later) first last) →
    (∀ edge, edge ∈ PositiveKernelChainIn.directedEdges path →
      edge ∈ PositiveKernelChainIn.directedEdges
        (cutoffTwoNovelRoutedPath hpair)) →
    cutoffTwoNovelPathReverseForwardProduct later hfirst path ≤
      cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later ^
        PositiveKernelChainIn.edgeLength path
  | _, _, _, PositiveKernelChainIn.refl _, _ => Q'.le_refl' 1
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) positive hnext rest,
      hsubset => by
      have hheadRoute := hsubset (first, next) List.mem_cons_self
      have hfactor :=
        cutoffTwoConditionalReverseForwardRatio_le_routedFiniteCeiling
          hpair hheadRoute
      have hrest :=
        cutoffTwoNovelPathReverseForwardProduct_le_routedFiniteCeilingPow
          hpair hnext rest
          (fun edge hedge =>
            hsubset edge (List.mem_cons_of_mem (first, next) hedge))
      have hrestNonnegative : (0 : Q') ≤
          cutoffTwoNovelPathReverseForwardProduct later hnext rest :=
        Q'.le_of_lt
          (cutoffTwoNovelPathReverseForwardProduct_pos later hnext rest)
      have hpowNonnegative : (0 : Q') ≤
          cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later ^
            PositiveKernelChainIn.edgeLength rest :=
        Q'.pow_nonneg _
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative
            later) _
      unfold cutoffTwoNovelPathReverseForwardProduct
        PositiveKernelChainIn.edgeLength
      rw [Q'.pow_succ]
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hfactor hrestNonnegative)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hrest
          (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative
            later))

/-! ## 5. The routed-support maximum supplies both prefix ceilings -/

def cutoffTwoNovelRoutedSupportFiniteRatioCeilingData
    (later : Nat) :
    CutoffTwoNovelRoutedPrefixRatioCeilingAt later
      (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later) where
  rho_nonnegative :=
    cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative later
  source_prefix_product_le := fun _pair hpair source target hedge =>
    cutoffTwoNovelPathReverseForwardProduct_le_routedFiniteCeilingPow
      hpair
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (cutoffTwoNovelRoutedPrefix hpair source target hedge).pathPrefix
      (fun edge hedgePrefix =>
        prefixAtDirectedEdge_directedEdges_subset
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          (cutoffTwoNovelRoutedPath hpair) (source, target) hedge
          edge hedgePrefix)
  target_prefix_product_le := fun _pair hpair source target hedge =>
    cutoffTwoNovelPathReverseForwardProduct_le_routedFiniteCeilingPow
      hpair
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (positiveKernelPrefixThroughEdge
        (cutoffTwoNovelRoutedPrefix hpair source target hedge))
      (fun edge hedgePrefix =>
        throughEdge_directedEdges_subset
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          (cutoffTwoNovelRoutedPath hpair) (source, target) hedge
          edge hedgePrefix)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling.cutoffTwoNovelRoutedPath_edge_mem
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling.cutoffTwoConditionalReverseForwardRatio_le_routedFiniteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling.cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_finiteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling.prefixAtDirectedEdge_directedEdges_subset
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling.cutoffTwoNovelPathReverseForwardProduct_le_routedFiniteCeilingPow
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling.cutoffTwoNovelRoutedSupportFiniteRatioCeilingData
