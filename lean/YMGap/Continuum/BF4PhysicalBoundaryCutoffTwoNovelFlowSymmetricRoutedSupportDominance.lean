/-
# Dominance of the routed-support finite ceiling

The routed-support maximum is no larger than the full-carrier maximum.  This
module propagates that inequality through every prefix power, weighted path
sum, and symmetric ceiling load.  Consequently every successful full-carrier
three-block check implies success of the routed-support check, while every
successful routed-support check implies success of the exact transition-
product check.

These are implications between finite decision procedures.  They do not prove
that any check succeeds, uniformly or otherwise, and assert no
thermodynamic/continuum or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

/-! ## 1. Monotonicity of powers and path-pair ceiling terms -/

theorem qpow_base_mono
    (lower upper : Q')
    (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) :
    ∀ exponent : Nat, lower ^ exponent ≤ upper ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hupper : (0 : Q') ≤ upper :=
        Q'.le_trans' _ _ _ hlower hle
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hle
          (Q'.pow_nonneg lower hlower exponent))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (qpow_base_mono lower upper hlower hle exponent) hupper)

theorem cutoffTwoNovelPathPairConditionalRatioCeilingTerm_mono
    {lower upper : Q'}
    (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    (later source target : Nat) (pair : Nat × Nat) :
    cutoffTwoNovelPathPairConditionalRatioCeilingTerm
        lower later source target pair ≤
      cutoffTwoNovelPathPairConditionalRatioCeilingTerm
        upper later source target pair := by
  unfold cutoffTwoNovelPathPairConditionalRatioCeilingTerm
  by_cases hpair : pair ∈ cutoffTwoNovelEndpointPairs later
  · rw [dif_pos hpair, dif_pos hpair]
    let path :=
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (cutoffTwoNovelEndpointPair_mem_full hpair).2
    change
      (if hedge : (source, target) ∈
          PositiveKernelChainIn.directedEdges path then
        let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          path (source, target) hedge
        (lower ^ PositiveKernelChainIn.edgeLength prefixData.pathPrefix *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0) ≤
      (if hedge : (source, target) ∈
          PositiveKernelChainIn.directedEdges path then
        let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          path (source, target) hedge
        (upper ^ PositiveKernelChainIn.edgeLength prefixData.pathPrefix *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0)
    by_cases hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [dif_pos hedge, dif_pos hedge]
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      have hpower := qpow_base_mono lower upper hlower hle
        (PositiveKernelChainIn.edgeLength prefixData.pathPrefix)
      have hweight : (0 : Q') ≤ cutoffTwoEdgeLoadWeight later pair.2 :=
        Q'.le_of_lt
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (w := cutoffTwoHalfCoupling) (hw := by decide)
            (cutoffTwoNovelEndpointPair_mem_full hpair).2)
      have hlength : (0 : Q') ≤
          Q'.ofNat (PositiveKernelChainIn.edgeLength path) :=
        ExpNeg.ofNat_nonneg' _
      exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hpower hweight)
        hlength
    · rw [dif_neg hedge, dif_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair, dif_neg hpair]
    exact Q'.le_refl' 0

theorem cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm_mono
    {lower upper : Q'}
    (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    (later source target : Nat) (pair : Nat × Nat) :
    cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm
        lower later source target pair ≤
      cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm
        upper later source target pair := by
  unfold cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm
  by_cases hpair : pair ∈ cutoffTwoNovelEndpointPairs later
  · rw [dif_pos hpair, dif_pos hpair]
    let path :=
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (cutoffTwoNovelEndpointPair_mem_full hpair).2
    change
      (if hedge : (source, target) ∈
          PositiveKernelChainIn.directedEdges path then
        let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          path (source, target) hedge
        (lower ^ PositiveKernelChainIn.edgeLength
              (positiveKernelPrefixThroughEdge prefixData) *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0) ≤
      (if hedge : (source, target) ∈
          PositiveKernelChainIn.directedEdges path then
        let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          path (source, target) hedge
        (upper ^ PositiveKernelChainIn.edgeLength
              (positiveKernelPrefixThroughEdge prefixData) *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0)
    by_cases hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [dif_pos hedge, dif_pos hedge]
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      have hpower := qpow_base_mono lower upper hlower hle
        (PositiveKernelChainIn.edgeLength
          (positiveKernelPrefixThroughEdge prefixData))
      have hweight : (0 : Q') ≤ cutoffTwoEdgeLoadWeight later pair.2 :=
        Q'.le_of_lt
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (w := cutoffTwoHalfCoupling) (hw := by decide)
            (cutoffTwoNovelEndpointPair_mem_full hpair).2)
      have hlength : (0 : Q') ≤
          Q'.ofNat (PositiveKernelChainIn.edgeLength path) :=
        ExpNeg.ofNat_nonneg' _
      exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hpower hweight)
        hlength
    · rw [dif_neg hedge, dif_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair, dif_neg hpair]
    exact Q'.le_refl' 0

/-! ## 2. Monotonicity of the summed and symmetric ceiling loads -/

theorem cutoffTwoNovelConditionalRatioCeilingLoad_mono
    {lower upper : Q'}
    (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    (later source target : Nat) :
    cutoffTwoNovelConditionalRatioCeilingLoad
        lower later source target ≤
      cutoffTwoNovelConditionalRatioCeilingLoad
        upper later source target := by
  unfold cutoffTwoNovelConditionalRatioCeilingLoad
  apply listQSum_mono
  intro pair _hpair
  exact cutoffTwoNovelPathPairConditionalRatioCeilingTerm_mono
    hlower hle later source target pair

theorem cutoffTwoNovelConditionalTargetRatioCeilingLoad_mono
    {lower upper : Q'}
    (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    (later source target : Nat) :
    cutoffTwoNovelConditionalTargetRatioCeilingLoad
        lower later source target ≤
      cutoffTwoNovelConditionalTargetRatioCeilingLoad
        upper later source target := by
  unfold cutoffTwoNovelConditionalTargetRatioCeilingLoad
  apply listQSum_mono
  intro pair _hpair
  exact cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm_mono
    hlower hle later source target pair

theorem cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_mono
    {lower upper : Q'}
    (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper)
    (later source target : Nat) :
    cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
        lower later source target ≤
      cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
        upper later source target := by
  unfold cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
    cutoffTwoNovelSymmetricCrossRatioCeilingLoad
  exact Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (cutoffTwoNovelConditionalRatioCeilingLoad_mono
        hlower hle later source target)
      HalfPow.half_nonneg)
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (cutoffTwoNovelConditionalTargetRatioCeilingLoad_mono
        hlower hle later target source)
      HalfPow.half_nonneg)

theorem cutoffTwoNovelSymmetricRoutedSupportFiniteCeilingLoad_le_fullFiniteCeilingLoad
    (later source target : Nat) :
    cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
        later source target ≤
      cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
        later source target := by
  unfold cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
    cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
    cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
  exact cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_mono
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_nonnegative later)
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_finiteCeiling
      later)
    later source target

/-! ## 3. The finite checker hierarchy -/

theorem cutoffTwoNovelSymmetricAllBlockFiniteCheck_implies_routedSupportCheck
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingCheck later = true) :
    cutoffTwoNovelSymmetricAllBlockRoutedSupportFiniteCeilingCheck later =
      true := by
  have houter := (Bool.and_eq_true _ _).mp hcheck
  have hinner := (Bool.and_eq_true _ _).mp houter.2
  have hold :
      cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck later =
        true := by
    unfold cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck
    apply List.all_eq_true.mpr
    intro pair hpair
    have hblocks := (mem_cartesian_iff _ _ pair).1 hpair
    apply decide_eq_true
    have hload :=
      cutoffTwoNovelSymmetricRoutedSupportFiniteCeilingLoad_le_fullFiniteCeilingLoad
        later pair.1 pair.2
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck_sound
        later houter.1 pair.1 hblocks.1 pair.2 hblocks.2)
  have hcross :
      cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck later =
        true := by
    unfold cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck
    apply List.all_eq_true.mpr
    intro pair hpair
    have hblocks := (mem_cartesian_iff _ _ pair).1 hpair
    apply decide_eq_true
    have hload :=
      cutoffTwoNovelSymmetricRoutedSupportFiniteCeilingLoad_le_fullFiniteCeilingLoad
        later pair.1 pair.2
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_sound
        later hinner.1 pair.1 hblocks.1 pair.2 hblocks.2)
  have hnew :
      cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck later =
        true := by
    unfold cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck
    apply List.all_eq_true.mpr
    intro pair hpair
    have hblocks := (mem_cartesian_iff _ _ pair).1 hpair
    apply decide_eq_true
    have hload :=
      cutoffTwoNovelSymmetricRoutedSupportFiniteCeilingLoad_le_fullFiniteCeilingLoad
        later pair.1 pair.2
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (cutoffTwoNovelSymmetricNewNewFiniteRatioCeilingCheck_sound
        later hinner.2 pair.1 hblocks.1 pair.2 hblocks.2)
  unfold cutoffTwoNovelSymmetricAllBlockRoutedSupportFiniteCeilingCheck
  exact (Bool.and_eq_true _ _).mpr
    ⟨hold, (Bool.and_eq_true _ _).mpr ⟨hcross, hnew⟩⟩

theorem cutoffTwoNovelSymmetricRoutedSupportCheck_implies_transitionProductCheck
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricAllBlockRoutedSupportFiniteCeilingCheck later =
        true) :
    cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck later =
      true := by
  exact cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck_complete
    (cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_routedSupportCheck
      later hcheck).toTransitionProductCapacityAt

theorem cutoffTwoNovelSymmetricAllBlockFiniteCheck_implies_transitionProductCheck
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingCheck later = true) :
    cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck later =
      true :=
  cutoffTwoNovelSymmetricRoutedSupportCheck_implies_transitionProductCheck
    later
    (cutoffTwoNovelSymmetricAllBlockFiniteCheck_implies_routedSupportCheck
      later hcheck)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance.qpow_base_mono
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance.cutoffTwoNovelPathPairConditionalRatioCeilingTerm_mono
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance.cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_mono
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance.cutoffTwoNovelSymmetricRoutedSupportFiniteCeilingLoad_le_fullFiniteCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance.cutoffTwoNovelSymmetricAllBlockFiniteCheck_implies_routedSupportCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance.cutoffTwoNovelSymmetricRoutedSupportCheck_implies_transitionProductCheck
