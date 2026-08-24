/-
# Exact finite-carrier recoding at cutoff two

The canonical cutoff-two vacuum component is defined by a root-component
search on opaque positive-carrier indices, whereas the production
calculation provides an explicit 65-state table.  The existing state-level
permutation implies the exact cardinality of the index component without
normalizing that search.  At equal base and target cutoffs the index map is
the identity, so the old block is the whole component and the new block is
empty.

Consequently the novel endpoint and routed-edge lists at the cutoff-two
anchor are empty.  This is an exact anchor recoding only.  It does not
provide any positive-cutoff increment estimate, cofinal capacity bound,
thermodynamic/continuum construction, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The opaque component has the certified cardinality -/

theorem cutoffTwoEdgeLoadFullStates_length :
    (cutoffTwoEdgeLoadFullStates 2).length = 65 := by
  have hlength :=
    cutoffTwoCanonicalVacuumSectorStates_perm.length_eq
  unfold centralPhysicalFiniteVacuumSectorStates at hlength
  simp only [List.length_map] at hlength
  rw [cutoffTwoCubeSectorStates_length] at hlength
  exact hlength

/-! ## 2. Equal-cutoff old/new blocks -/

private theorem map_eq_self_of_eq_on_local
    {A : Type} (map : A → A) :
    ∀ items : List A,
      (∀ item, item ∈ items → map item = item) →
      items.map map = items
  | [], _ => rfl
  | head :: tail, heq => by
      simp only [List.map]
      rw [heq head List.mem_cons_self]
      exact congrArg (List.cons head)
        (map_eq_self_of_eq_on_local map tail
          (fun item hitem =>
            heq item (List.mem_cons_of_mem head hitem)))

theorem centralPhysicalFiniteEmbeddedVacuumSectorIndices_self
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} :
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw cutoff cutoff half =
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half := by
  unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
  apply map_eq_self_of_eq_on_local
  intro index hindex
  exact centralPhysicalFiniteCutoffIndexMap_self hindex

theorem centralPhysicalFiniteVacuumSectorOldBlockIndices_self
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} :
    centralPhysicalFiniteVacuumSectorOldBlockIndices
        w hw cutoff cutoff half =
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorOldBlockIndices
  apply List.filter_eq_self.mpr
  intro index hindex
  unfold centralPhysicalFiniteEmbeddedVacuumSectorB
  rw [centralPhysicalFiniteEmbeddedVacuumSectorIndices_self]
  exact decide_eq_true hindex

private theorem filter_not_true_empty_local
    {A : Type} (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = true) →
      items.filter (fun item => !(test item)) = []
  | [], _ => rfl
  | head :: tail, htrue => by
      have hhead := htrue head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → test item = true :=
        fun item hitem =>
          htrue item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, hhead, Bool.not_true,
        Bool.false_eq_true, if_false]
      exact filter_not_true_empty_local test tail htail

theorem centralPhysicalFiniteVacuumSectorNewBlockIndices_self
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} :
    centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw cutoff cutoff half = [] := by
  unfold centralPhysicalFiniteVacuumSectorNewBlockIndices
  apply filter_not_true_empty_local
  intro index hindex
  unfold centralPhysicalFiniteEmbeddedVacuumSectorB
  rw [centralPhysicalFiniteEmbeddedVacuumSectorIndices_self]
  exact decide_eq_true hindex

theorem cutoffTwoEmbeddedVacuumSectorIndices_self :
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 2 0 =
      cutoffTwoEdgeLoadFullStates 2 := by
  unfold cutoffTwoEdgeLoadFullStates
  exact centralPhysicalFiniteEmbeddedVacuumSectorIndices_self

theorem cutoffTwoEdgeLoadOldStates_self :
    cutoffTwoEdgeLoadOldStates 2 = cutoffTwoEdgeLoadFullStates 2 := by
  unfold cutoffTwoEdgeLoadOldStates cutoffTwoEdgeLoadFullStates
  exact centralPhysicalFiniteVacuumSectorOldBlockIndices_self

theorem cutoffTwoEdgeLoadNewStates_self :
    cutoffTwoEdgeLoadNewStates 2 = [] := by
  unfold cutoffTwoEdgeLoadNewStates
  exact centralPhysicalFiniteVacuumSectorNewBlockIndices_self

theorem cutoffTwoEdgeLoadOldStates_length :
    (cutoffTwoEdgeLoadOldStates 2).length = 65 := by
  rw [cutoffTwoEdgeLoadOldStates_self]
  exact cutoffTwoEdgeLoadFullStates_length

theorem cutoffTwoEdgeLoadNewStates_length :
    (cutoffTwoEdgeLoadNewStates 2).length = 0 := by
  rw [cutoffTwoEdgeLoadNewStates_self]
  rfl

/-! ## 3. The anchor carries no genuinely novel traffic -/

private theorem cartesian_right_empty_local
    {A B : Type} : ∀ items : List A,
    YMGap.Continuum.FiniteWeightedCartesianInjection.cartesian
        items ([] : List B) = []
  | [] => rfl
  | _ :: tail => by
      unfold YMGap.Continuum.FiniteWeightedCartesianInjection.cartesian
      simp only [List.flatMap_cons, List.map_nil, List.nil_append]
      exact cartesian_right_empty_local tail

theorem cutoffTwoNovelEndpointPairs_self :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelEndpointPairs
        2 = [] := by
  unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelEndpointPairs
    cutoffTwoCanonicalCrossEndpointPairs
  rw [cutoffTwoEdgeLoadNewStates_self]
  simp only [cartesian_right_empty_local]
  rfl

theorem cutoffTwoNovelSimpleWeightedEdgeOccurrences_self :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelSimpleWeightedEdgeOccurrences
        2 = [] := by
  unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelSimpleWeightedEdgeOccurrences
  rw [cutoffTwoNovelEndpointPairs_self]
  rfl

theorem cutoffTwoNovelRoutedDirectedEdges_self :
    cutoffTwoNovelRoutedDirectedEdges 2 = [] := by
  unfold cutoffTwoNovelRoutedDirectedEdges
  rw [cutoffTwoNovelSimpleWeightedEdgeOccurrences_self]
  rfl

theorem cutoffTwoNovelRoutedDistinctDirectedEdges_self :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.cutoffTwoNovelRoutedDistinctDirectedEdges
        2 = [] := by
  unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.cutoffTwoNovelRoutedDistinctDirectedEdges
  rw [cutoffTwoNovelRoutedDirectedEdges_self]
  rfl

/-! ## 4. Symbolic discharge of the anchor capacity -/

theorem cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_self :
    cutoffTwoConditionalReverseForwardRoutedFiniteCeiling 2 = 0 := by
  unfold cutoffTwoConditionalReverseForwardRoutedFiniteCeiling
  rw [cutoffTwoNovelRoutedDirectedEdges_self]
  rfl

theorem cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_self_eqv_zero
    (rho : Q') (source target : Nat) :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
        rho 2 source target ≈ 0 := by
  unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.cutoffTwoNovelSymmetricCrossRatioCeilingLoad
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling.cutoffTwoNovelConditionalRatioCeilingLoad
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.cutoffTwoNovelConditionalTargetRatioCeilingLoad
  rw [cutoffTwoNovelEndpointPairs_self]
  exact Q'.eqv_trans _ (0 + 0) _
    (Q'.add_eqv_congr'
      (Q'.mul_zero_eqv HalfPow.half)
      (Q'.mul_zero_eqv HalfPow.half))
    (Q'.eqv_of_eq (Q'.zero_add' 0))

theorem cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad_self_eqv_zero
    (source target : Nat) :
    cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
        2 source target ≈ 0 := by
  unfold cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
  exact cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_self_eqv_zero
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling 2)
    source target

/-- The routed-ceiling capacity is inhabited at the exact cutoff-two anchor.
Its old--old field is non-vacuous, but the novel load it pays is zero because
there are no states outside the base image at equal cutoffs. -/
def cutoffTwoNovelSymmetricAnchorRoutedCeilingCapacity :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt
      2 where
  rho := cutoffTwoConditionalReverseForwardRoutedFiniteCeiling 2
  routed_ceiling := cutoffTwoNovelRoutedSupportFiniteRatioCeilingData 2
  old_old := fun source _hsource target _htarget => by
    have hleft :
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
              2 source target ≈ 0 :=
      Q'.eqv_trans _
        (cutoffTwoNovelSimpleFlowCoercivityFloor * 0) _
        (Q'.mul_eqv_congr_left
          cutoffTwoNovelSimpleFlowCoercivityFloor _ _
          (cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad_self_eqv_zero
            source target))
        (Q'.mul_zero_eqv cutoffTwoNovelSimpleFlowCoercivityFloor)
    exact Q'.le_trans' _ 0 _
      (Q'.le_of_eqv hleft)
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg
        (cutoffTwoEdgeLoadConditionalKernel_nonnegative 2 source target))
  old_new := fun _source _hsource _target htarget => by
    rw [cutoffTwoEdgeLoadNewStates_self] at htarget
    exact False.elim (List.not_mem_nil htarget)
  new_new := fun _source hsource _target _htarget => by
    rw [cutoffTwoEdgeLoadNewStates_self] at hsource
    exact False.elim (List.not_mem_nil hsource)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoEdgeLoadFullStates_length
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoEmbeddedVacuumSectorIndices_self
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoEdgeLoadOldStates_self
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoEdgeLoadNewStates_self
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoNovelEndpointPairs_self
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoNovelRoutedDistinctDirectedEdges_self
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad_self_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding.cutoffTwoNovelSymmetricAnchorRoutedCeilingCapacity
