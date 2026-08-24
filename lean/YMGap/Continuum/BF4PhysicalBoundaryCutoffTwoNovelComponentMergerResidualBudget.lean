/-
# Residual edge-floor budget for cutoff-two component-merger mass

The component-split scalar payment contains two independent stationary-mass
costs: the corrected-slab cutoff increment and component-merger mass.  This
file distributes the exact rational demand into those two terms and exposes a
division-free residual-budget certificate.

A certificate chooses a rational reserve, proves that increment demand plus
the reserve fits below the later edge-payment budget, and proves that merger
demand fits inside the reserve.  It then compiles to the existing finite
capacity and, if supplied cofinally, to completed strict contraction.

No reserve or cofinal family is inhabited here.  No merger-mass bound,
fixed-base decay, thermodynamic/continuum construction, or Clay mass gap is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact split of scalar payment demand -/

def cutoffTwoNovelComponentSplitPaymentDemand (later : Nat) : Q' :=
  cutoffTwoNovelSimpleFlowCoercivityFloor *
    (Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length) *
      (Q'.ofNat 2 *
        (slabParametricKCutoffIncrement
            cutoffTwoHalfCoupling 2 later (centralExtent 0) +
          cutoffTwoNewComponentMergerMass later)))

def cutoffTwoNovelIncrementPaymentDemand (later : Nat) : Q' :=
  cutoffTwoNovelSimpleFlowCoercivityFloor *
    (Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length) *
      (Q'.ofNat 2 *
        slabParametricKCutoffIncrement
          cutoffTwoHalfCoupling 2 later (centralExtent 0)))

def cutoffTwoNovelComponentMergerPaymentDemand (later : Nat) : Q' :=
  cutoffTwoNovelSimpleFlowCoercivityFloor *
    (Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length) *
      (Q'.ofNat 2 * cutoffTwoNewComponentMergerMass later))

def cutoffTwoNovelEdgePaymentBudget (later : Nat) : Q' :=
  HalfPow.half *
    centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0

theorem cutoffTwoNovelComponentSplitPaymentDemand_eqv_increment_add_merger
    (later : Nat) :
    cutoffTwoNovelComponentSplitPaymentDemand later ≈
      cutoffTwoNovelIncrementPaymentDemand later +
        cutoffTwoNovelComponentMergerPaymentDemand later := by
  let size := Q'.ofNat
    (65 + (cutoffTwoEdgeLoadNewStates later).length)
  let increment := slabParametricKCutoffIncrement
    cutoffTwoHalfCoupling 2 later (centralExtent 0)
  let merger := cutoffTwoNewComponentMergerMass later
  have htwo :
      Q'.ofNat 2 * (increment + merger) ≈
        Q'.ofNat 2 * increment + Q'.ofNat 2 * merger :=
    Q'.mul_add_eqv _ _ _
  have hsizeCongr :
      size * (Q'.ofNat 2 * (increment + merger)) ≈
        size * (Q'.ofNat 2 * increment + Q'.ofNat 2 * merger) :=
    Q'.mul_eqv_congr_left size _ _ htwo
  have hsizeDist :
      size * (Q'.ofNat 2 * increment + Q'.ofNat 2 * merger) ≈
        size * (Q'.ofNat 2 * increment) +
          size * (Q'.ofNat 2 * merger) :=
    Q'.mul_add_eqv _ _ _
  have hsize := Q'.eqv_trans _ _ _ hsizeCongr hsizeDist
  have hfloorCongr :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (size * (Q'.ofNat 2 * (increment + merger))) ≈
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          (size * (Q'.ofNat 2 * increment) +
            size * (Q'.ofNat 2 * merger)) :=
    Q'.mul_eqv_congr_left cutoffTwoNovelSimpleFlowCoercivityFloor _ _ hsize
  have hfloorDist :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (size * (Q'.ofNat 2 * increment) +
            size * (Q'.ofNat 2 * merger)) ≈
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            (size * (Q'.ofNat 2 * increment)) +
          cutoffTwoNovelSimpleFlowCoercivityFloor *
            (size * (Q'.ofNat 2 * merger)) :=
    Q'.mul_add_eqv _ _ _
  unfold cutoffTwoNovelComponentSplitPaymentDemand
    cutoffTwoNovelIncrementPaymentDemand
    cutoffTwoNovelComponentMergerPaymentDemand
  exact Q'.eqv_trans _ _ _ hfloorCongr hfloorDist

/-! ## 2. A division-free residual merger budget -/

structure CutoffTwoNovelComponentMergerResidualBudgetAt
    (later : Nat) : Type where
  reserve : Q'
  increment_plus_reserve_le_budget :
    cutoffTwoNovelIncrementPaymentDemand later + reserve ≤
      cutoffTwoNovelEdgePaymentBudget later
  merger_demand_le_reserve :
    cutoffTwoNovelComponentMergerPaymentDemand later ≤ reserve

theorem cutoffTwoNovelComponentMergerPaymentDemand_nonnegative
    (later : Nat) :
    (0 : Q') ≤ cutoffTwoNovelComponentMergerPaymentDemand later := by
  unfold cutoffTwoNovelComponentMergerPaymentDemand
  apply Q'.mul_nonneg
  · exact Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos
  · apply Q'.mul_nonneg
    · exact YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _
    · apply Q'.mul_nonneg
      · exact YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _
      · exact cutoffTwoNewComponentMergerMass_nonnegative later

theorem CutoffTwoNovelComponentMergerResidualBudgetAt.reserve_nonnegative
    {later : Nat}
    (certificate : CutoffTwoNovelComponentMergerResidualBudgetAt later) :
    (0 : Q') ≤ certificate.reserve :=
  Q'.le_trans' _ _ _
    (cutoffTwoNovelComponentMergerPaymentDemand_nonnegative later)
    certificate.merger_demand_le_reserve

theorem cutoffTwoComponentSplitPayment_of_mergerResidualBudget
    {later : Nat}
    (certificate : CutoffTwoNovelComponentMergerResidualBudgetAt later) :
    cutoffTwoNovelComponentSplitPaymentDemand later ≤
      cutoffTwoNovelEdgePaymentBudget later := by
  have hreplace :
      cutoffTwoNovelIncrementPaymentDemand later +
          cutoffTwoNovelComponentMergerPaymentDemand later ≤
        cutoffTwoNovelIncrementPaymentDemand later + certificate.reserve :=
    Q'.add_le_add_left _ _ _ certificate.merger_demand_le_reserve
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (cutoffTwoNovelComponentSplitPaymentDemand_eqv_increment_add_merger
        later))
    (Q'.le_trans' _ _ _ hreplace
      certificate.increment_plus_reserve_le_budget)

/-! ## 3. Compile a residual budget to finite and cofinal contraction -/

def cutoffTwoNovelSimpleFlowCapacityAt_of_mergerResidualBudget
    (later : Nat)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later)
    (certificate : CutoffTwoNovelComponentMergerResidualBudgetAt later) :
    CutoffTwoNovelSimpleFlowCapacityAt later := by
  apply cutoffTwoNovelSimpleFlowCapacityAt_of_componentSplitPayment
    later hlaterFloor hlaterMass
  exact cutoffTwoComponentSplitPayment_of_mergerResidualBudget certificate

structure CutoffTwoCofinalNovelComponentMergerResidualBudget : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  budget : ∀ request,
    CutoffTwoNovelComponentMergerResidualBudgetAt (anchor request)

namespace CutoffTwoCofinalNovelComponentMergerResidualBudget

def toCofinalNovelComponentSplitEdgeFloorPayment
    (family : CutoffTwoCofinalNovelComponentMergerResidualBudget) :
    CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  payment := fun request =>
    cutoffTwoComponentSplitPayment_of_mergerResidualBudget
      (family.budget request)

def toCofinalNovelSimpleFlowCapacity
    (family : CutoffTwoCofinalNovelComponentMergerResidualBudget) :
    CutoffTwoCofinalNovelSimpleFlowCapacity :=
  family.toCofinalNovelComponentSplitEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelComponentMergerResidualBudget) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelComponentMergerResidualBudget

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.cutoffTwoNovelComponentSplitPaymentDemand_eqv_increment_add_merger
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.cutoffTwoNovelComponentMergerPaymentDemand_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.CutoffTwoNovelComponentMergerResidualBudgetAt.reserve_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.cutoffTwoComponentSplitPayment_of_mergerResidualBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.cutoffTwoNovelSimpleFlowCapacityAt_of_mergerResidualBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.CutoffTwoCofinalNovelComponentMergerResidualBudget.toCofinalNovelComponentSplitEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.CutoffTwoCofinalNovelComponentMergerResidualBudget.toCofinalNovelSimpleFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.CutoffTwoCofinalNovelComponentMergerResidualBudget.toCompletedStrictContractionData
