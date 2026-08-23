/-
# One routed-prefix ceiling for all symmetric BF4 capacity blocks

The routed-prefix ceiling bounds source-prefix and through-edge target-prefix
products without using any old/new classification of the selected edge.  This
module applies that observation to the common all-block transition-product
load.  A single routed ceiling therefore majorizes traffic on old--old,
old-to-new, and new--new edges.

A three-field ceiling-payment certificate preserves the only block distinction:
old--old receives one half of the conditional transition, whereas the other
two oriented blocks receive the full transition.  The certificate contracts
to exact transition-product capacity and then to completed strict contraction.

No ceiling payment or cofinal family is inhabited here.  No uniform estimate,
thermodynamic/continuum construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProductDecision
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap

/-! ## 1. The routed ceiling is block-independent -/

def cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
    (rho : Q') (later source target : Nat) : Q' :=
  cutoffTwoNovelSymmetricCrossRatioCeilingLoad
    rho later source target

theorem cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoNovelRoutedPrefixRatioCeilingAt later rho)
    (source target : Nat) :
    cutoffTwoNovelSymmetricTransitionProductLoad
        later source target ≤
      cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
        rho later source target := by
  unfold cutoffTwoNovelSymmetricTransitionProductLoad
    cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
    cutoffTwoNovelSymmetricCrossRatioCeilingLoad
  exact Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (cutoffTwoNovelConditionalTransitionProductLoad_le_routedCeilingLoad
        ceiling source target)
      HalfPow.half_nonneg)
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (cutoffTwoNovelConditionalTargetTransitionProductLoad_le_routedCeilingLoad
        ceiling target source)
      HalfPow.half_nonneg)

/-! ## 2. Three ceiling payments compile to exact product capacity -/

structure CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt
    (later : Nat) : Type 1 where
  rho : Q'
  routed_ceiling : CutoffTwoNovelRoutedPrefixRatioCeilingAt later rho
  old_old : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
            rho later source target ≤
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later source target
  old_new : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
            rho later source target ≤
        cutoffTwoEdgeLoadConditionalKernel later source target
  new_new : ∀ source,
    source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
            rho later source target ≤
        cutoffTwoEdgeLoadConditionalKernel later source target

namespace CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt

def toTransitionProductCapacityAt
    {later : Nat}
    (capacity :
      CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt later) :
    CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt later where
  old_old := fun source hsource target htarget => by
    have hload :=
      cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad
        capacity.routed_ceiling source target
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      cutoffTwoNovelSimpleFlowCoercivityFloor hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (capacity.old_old source hsource target htarget)
  old_new := fun source hsource target htarget => by
    have hload :=
      cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad
        capacity.routed_ceiling source target
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      cutoffTwoNovelSimpleFlowCoercivityFloor hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (capacity.old_new source hsource target htarget)
  new_new := fun source hsource target htarget => by
    have hload :=
      cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad
        capacity.routed_ceiling source target
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      cutoffTwoNovelSimpleFlowCoercivityFloor hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (capacity.new_new source hsource target htarget)

def toOrientedCapacityAt
    {later : Nat}
    (capacity :
      CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt later) :=
  capacity.toTransitionProductCapacityAt.toOrientedCapacityAt

end CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt

/-! ## 3. Cofinal routed-ceiling payment reaches completion -/

structure CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity :
    Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  capacity : ∀ request,
    CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt
      (anchor request)

namespace CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity

def toCofinalNovelSymmetricOrientedCapacity
    (family :
      CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity) :
    CutoffTwoCofinalNovelSymmetricOrientedCapacity where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  capacity := fun request => (family.capacity request).toOrientedCapacityAt

def toCompletedStrictContractionData
    (family :
      CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelSymmetricOrientedCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt.toTransitionProductCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt.toOrientedCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity.toCompletedStrictContractionData
