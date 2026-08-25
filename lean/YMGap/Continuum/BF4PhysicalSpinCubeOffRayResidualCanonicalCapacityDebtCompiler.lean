/-
# Correlated canonical capacity-debt persistence for the BF4 residual flow

The support-proxy route separates routed-load variation from kernel
variation and then asks for a uniform positive kernel floor.  That separation
is sufficient but stronger than the actual edge-capacity inequality: a small
conditional-kernel entry is harmless when the exact routed load on the same
edge is comparably small.

This module keeps those two quantities correlated.  On each ordered pair it
forms the exact normalized capacity debt

  sharedFloor * routedLoad / (half * conditionalKernel),

using zero when the denominator is not positive.  On the literal vacuum
sector, positive routed load already implies positive conditional kernel, so
debt at most one proves the exact edge-capacity inequality.  The located
maximum over the exact pair carrier is therefore the single scalar stream
that must persist.

The canonical consecutive-pair maps are reused without change.  A summable
two-sided pointwise envelope for this one correlated observable, together
with a total budget and initial slack, compiles directly to the existing
cofinal adaptive transition product and completed fixed-anchor family.  No
analytic envelope, budget, or slack inhabitant is supplied here.

The fixed strong-coupling anchor is not the physical AF/grouped-BF4
trajectory.  No thermodynamic or continuum same-observable bridge, uniform
physical mass gap, continuum Yang--Mills theory, or Clay conclusion is
asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact correlated pairwise capacity debt -/

/-- Normalize the exact routed load by the half conditional-kernel capacity
on the same ordered pair.  The zero fallback only totalizes the ambient
function: on the literal carrier every positive load forces a positive
denominator. -/
def anchorRoutedCapacityDebtOnPair
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
      scale 0 pair.1 pair.2
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos
      (anchorAdaptiveSharedCoercivityFloor *
        anchorRoutedLoadOnPair routing scale pair)
      capacity hcapacity
  else
    0

theorem anchorRoutedCapacityDebtOnPair_nonnegative
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs scale) :
    (0 : Q') <= anchorRoutedCapacityDebtOnPair routing scale pair := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  have hload : (0 : Q') <=
      anchorRoutedLoadOnPair routing scale pair := by
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
        (routing scale) hmembers.1 pair.2
  unfold anchorRoutedCapacityDebtOnPair
  dsimp only
  by_cases hcapacity : (0 : Q') <
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
          scale 0 pair.1 pair.2
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt anchorAdaptiveSharedCoercivityFloor_pos) hload)
      (Q'.le_of_lt (Q'.recipPos_pos _ hcapacity))
  · rw [dif_neg hcapacity]
    exact Q'.le_refl' 0

/-- The correlated debt test is lossless on the literal pair carrier: debt
at most one is exactly sufficient for the physical edge-capacity inequality.
-/
theorem anchorRoutedCapacityDebtOnPair_le_one_implies_edge_capacity
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs scale)
    (hdebt : anchorRoutedCapacityDebtOnPair routing scale pair <= (1 : Q')) :
    anchorAdaptiveSharedCoercivityFloor *
        anchorRoutedLoadOnPair routing scale pair <=
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
          scale 0 pair.1 pair.2 := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  let load := anchorRoutedLoadOnPair routing scale pair
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
      scale 0 pair.1 pair.2
  have hloadNonnegative : (0 : Q') <= load := by
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
        (routing scale) hmembers.1 pair.2
  by_cases hload : (0 : Q') < load
  · have hkernel : (0 : Q') <
        centralPhysicalFiniteConditionalKernel
          anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
          scale 0 pair.1 pair.2 := by
      exact
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos
          (routing scale) hmembers.1 pair.2 hload
    have hcapacity : (0 : Q') < capacity :=
      Q'.mul_pos (by decide) hkernel
    have hdebt' : Q'.divPos
          (anchorAdaptiveSharedCoercivityFloor * load)
          capacity hcapacity <= (1 : Q') := by
      unfold anchorRoutedCapacityDebtOnPair at hdebt
      change (if h : (0 : Q') < capacity then
          Q'.divPos
            (anchorAdaptiveSharedCoercivityFloor * load)
            capacity h
        else 0) <= (1 : Q') at hdebt
      rw [dif_pos hcapacity] at hdebt
      exact hdebt
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ capacity
      hdebt' (Q'.le_of_lt hcapacity)
    change anchorAdaptiveSharedCoercivityFloor * load <= capacity
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (Q'.divPos_mul_eqv
          (anchorAdaptiveSharedCoercivityFloor * load)
          capacity hcapacity))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.one_mul_eqv capacity)))
  · have hloadNonpositive : load <= (0 : Q') := by
      show load.num * (1 : Int) <= (0 : Int) * (load.den : Int)
      rw [Int.mul_one, Int.zero_mul]
      apply Int.not_lt.mp
      intro hnum
      apply hload
      exact CReal.pos_of_num_pos hnum
    have hloadZero : load ≈ (0 : Q') :=
      Q'.eqv_of_le_le hloadNonpositive hloadNonnegative
    change anchorAdaptiveSharedCoercivityFloor * load <= capacity
    exact Q'.le_trans' _ (0 : Q') _
      (Q'.le_of_eqv
        (Q'.eqv_trans _
          (anchorAdaptiveSharedCoercivityFloor * 0) _
          (Q'.mul_eqv_congr_left
            anchorAdaptiveSharedCoercivityFloor load 0 hloadZero)
          (Q'.mul_zero_eqv anchorAdaptiveSharedCoercivityFloor)))
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg
        (centralPhysicalFiniteConditionalKernel_nonnegative
          anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
          scale 0 pair.1 pair.2))

/-- Located maximum of the literal correlated capacity debt over the exact
finite vacuum-sector pair carrier. -/
def anchorRoutedCapacityDebtMaximum
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) : Q' :=
  listQMaxZero
    (anchorRoutedCapacityDebtOnPair routing scale)
    (anchorVacuumSectorPairs scale)

theorem anchorRoutedCapacityDebtOnPair_le_maximum
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs scale) :
    anchorRoutedCapacityDebtOnPair routing scale pair <=
      anchorRoutedCapacityDebtMaximum routing scale := by
  unfold anchorRoutedCapacityDebtMaximum
  exact le_listQMaxZero_of_mem _ _ hpair

/-! ## 2. One canonical pointwise envelope replaces three separated lanes -/

/-- The sole dynamic analytic envelope on the correlated canonical path.
Both recodings are the already constructed physical consecutive-pair maps. -/
structure AnchorCanonicalCapacityDebtEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  current_le_next : forall scale pair,
    pair ∈ anchorVacuumSectorPairs scale ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence scale pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence
            (scale + 1) (anchorCurrentPairToNext scale pair) +
          variation scale
  next_le_current : forall scale pair,
    pair ∈ anchorVacuumSectorPairs (scale + 1) ->
      anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair <=
        anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNextPairToCurrent scale pair) + variation scale

def AnchorCanonicalCapacityDebtEnvelope.toMaximumVariation
    (data : AnchorCanonicalCapacityDebtEnvelope) :
    DynamicFiniteMaximumVariation
      (anchorRoutedCapacityDebtOnPair
        anchorCanonicalPositiveRoutingSequence)
      anchorVacuumSectorPairs where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  value_nonnegative :=
    anchorRoutedCapacityDebtOnPair_nonnegative
      anchorCanonicalPositiveRoutingSequence
  currentToNext := anchorCurrentPairToNext
  currentToNext_mem := anchorCurrentPairToNext_mem
  current_le_next := data.current_le_next
  nextToCurrent := anchorNextPairToCurrent
  nextToCurrent_mem := fun scale pair _ =>
    anchorNextPairToCurrent_mem scale pair
  next_le_current := data.next_le_current

/-- The fixed pair recodings compile the one pointwise envelope to summable
variation of the located maximum debt. -/
def anchorCanonicalCapacityDebtMaximumVariation
    (data : AnchorCanonicalCapacityDebtEnvelope) :
    SummableRationalStepVariation
      (anchorRoutedCapacityDebtMaximum
        anchorCanonicalPositiveRoutingSequence) := by
  change SummableRationalStepVariation
    (fun scale => listQMaxZero
      (anchorRoutedCapacityDebtOnPair
        anchorCanonicalPositiveRoutingSequence scale)
      (anchorVacuumSectorPairs scale))
  exact data.toMaximumVariation.toSummableRationalStepVariation

/-! ## 3. Budget closure reaches the existing completed physical family -/

/-- The minimal correlated persistence certificate: one observable-connected
envelope, one total variation budget, and the finite initial slack that pays
that budget. -/
structure AnchorCanonicalCapacityDebtPersistence : Type 1 where
  envelope : AnchorCanonicalCapacityDebtEnvelope
  budget : Q'
  budget_pos : (0 : Q') < budget
  budget_from_zero :
    (anchorCanonicalCapacityDebtMaximumVariation envelope).tailControl.tailRate
      budget = 0
  initial_closure :
    anchorRoutedCapacityDebtMaximum
        anchorCanonicalPositiveRoutingSequence 0 + budget <= (1 : Q')

namespace AnchorCanonicalCapacityDebtPersistence

theorem maximum_le_one
    (data : AnchorCanonicalCapacityDebtPersistence) (scale : Nat) :
    anchorRoutedCapacityDebtMaximum
        anchorCanonicalPositiveRoutingSequence scale <= (1 : Q') := by
  let variation :=
    anchorCanonicalCapacityDebtMaximumVariation data.envelope
  exact variation.le_of_initial_add_totalBudget_le
    data.budget_pos data.budget_from_zero data.initial_closure scale

/-- Contract maximum-debt persistence into the literal cofinal edge-capacity
field for the same canonical routing and physical kernel. -/
def toAdaptiveConditionalTransitionProduct
    (data : AnchorCanonicalCapacityDebtPersistence) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
      anchorCoupling_pos anchorCentralSpinCubeCofinalRayCapacity where
  routing := fun scale _hscale =>
    anchorCanonicalPositiveRoutingSequence scale
  product := fun scale hscale => {
    edge_capacity := fun source hsource target htarget => by
      have hpair : (source, target) ∈ anchorVacuumSectorPairs scale := by
        exact (mem_cartesian_iff _ _ (source, target)).mpr
          ⟨hsource, htarget⟩
      have hdebt : anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale (source, target) <=
          (1 : Q') :=
        Q'.le_trans' _ _ _
          (anchorRoutedCapacityDebtOnPair_le_maximum
            anchorCanonicalPositiveRoutingSequence scale
            (source, target) hpair)
          (data.maximum_le_one scale)
      change anchorAdaptiveSharedCoercivityFloor *
          anchorRoutedLoadOnPair
            anchorCanonicalPositiveRoutingSequence scale (source, target) <=
        HalfPow.half *
          centralPhysicalFiniteConditionalKernel
            anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
            scale 0 source target
      exact anchorRoutedCapacityDebtOnPair_le_one_implies_edge_capacity
        anchorCanonicalPositiveRoutingSequence scale
        (source, target) hpair hdebt
  }

/-- Reuse the same cofinal product at every geometric-spacing scale of the
fixed-anchor scalar trajectory. -/
def toAnchorGeometricExtension
    (data : AnchorCanonicalCapacityDebtPersistence) :
    AnchorGeometricAdaptiveTransitionProductExtension where
  transitionProduct := fun _scale =>
    data.toAdaptiveConditionalTransitionProduct

/-- The correlated persistence certificate therefore constructs the existing
completed carrier, transfer, and vacuum-sector family at the fixed anchor. -/
def toAnchorGeometricCompletedFamily
    (data : AnchorCanonicalCapacityDebtPersistence) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  data.toAnchorGeometricExtension.toCompletedFamily

end AnchorCanonicalCapacityDebtPersistence

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.anchorRoutedCapacityDebtOnPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.anchorRoutedCapacityDebtOnPair_le_one_implies_edge_capacity
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.AnchorCanonicalCapacityDebtEnvelope.toMaximumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.anchorCanonicalCapacityDebtMaximumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.AnchorCanonicalCapacityDebtPersistence.maximum_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.AnchorCanonicalCapacityDebtPersistence.toAdaptiveConditionalTransitionProduct
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.AnchorCanonicalCapacityDebtPersistence.toAnchorGeometricCompletedFamily
