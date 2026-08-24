/-
# Component-split scalar payment for the cutoff-two novel flow

The new-shell stationary mass is bounded by the corrected-slab increment plus
the mass of cutoff-two-positive states that join the vacuum component only at
a later cutoff.  Therefore the scalar inequality

  novelFloor *
    ((65 + newShellLength) * (2 * (cutoffIncrement + mergerMass)))
      <= half * finitePositiveEdgeFloor

implies the new-shell payment, all four novel-flow capacity blocks, and—when
supplied cofinally—the existing completed strict-contraction datum.

The cofinal payment remains an explicit field.  No component-merger bound,
cutoff-uniform comparison, thermodynamic/continuum construction, or Clay mass
gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The split bound pays the new-shell scalar inequality -/

theorem cutoffTwoNewShellMassEdgeFloorPayment_of_componentSplitPayment
    {later : Nat} (hcutoff : 2 ≤ later)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            (Q'.ofNat 2 *
              (slabParametricKCutoffIncrement
                  cutoffTwoHalfCoupling 2 later (centralExtent 0) +
                cutoffTwoNewComponentMergerMass later))) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 + (cutoffTwoEdgeLoadNewStates later).length) *
          (Q'.ofNat 2 * cutoffTwoNewMass later)) ≤
      HalfPow.half *
        centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 := by
  have hnew := cutoffTwoNewMass_le_increment_add_componentMerger hcutoff
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hnew
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat 2)
  have hsize := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length))
    htwo
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat
      (65 + (cutoffTwoEdgeLoadNewStates later).length))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    cutoffTwoNovelSimpleFlowCoercivityFloor hsize
    (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
  exact Q'.le_trans' _ _ _ hscaled hpayment

/-! ## 2. The component-split payment inhabits finite capacity -/

def cutoffTwoNovelSimpleFlowCapacityAt_of_componentSplitPayment
    (later : Nat)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            (Q'.ofNat 2 *
              (slabParametricKCutoffIncrement
                  cutoffTwoHalfCoupling 2 later (centralExtent 0) +
                cutoffTwoNewComponentMergerMass later))) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoNovelSimpleFlowCapacityAt later := by
  apply cutoffTwoNovelSimpleFlowCapacityAt_of_newShellMassEdgeFloorPayment
    later hlaterFloor hlaterMass
  exact cutoffTwoNewShellMassEdgeFloorPayment_of_componentSplitPayment
    (Nat.le_trans
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
      hlaterFloor)
    hpayment

/-! ## 3. A cofinal component-split payment reaches contraction -/

structure CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  payment : ∀ request,
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 +
              (cutoffTwoEdgeLoadNewStates (anchor request)).length) *
          (Q'.ofNat 2 *
            (slabParametricKCutoffIncrement cutoffTwoHalfCoupling 2
                (anchor request) (centralExtent 0) +
              cutoffTwoNewComponentMergerMass (anchor request)))) ≤
      HalfPow.half *
        centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment

def toCofinalNovelNewShellMassEdgeFloorPayment
    (family : CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment) :
    CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  payment := by
    intro request
    have hanchor := family.anchor_ge request
    exact cutoffTwoNewShellMassEdgeFloorPayment_of_componentSplitPayment
      (Nat.le_trans
        cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
        (Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_max_left _ _) hanchor)))
      (family.payment request)

def toCofinalNovelSimpleFlowCapacity
    (family : CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment) :
    CutoffTwoCofinalNovelSimpleFlowCapacity :=
  family.toCofinalNovelNewShellMassEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment.cutoffTwoNewShellMassEdgeFloorPayment_of_componentSplitPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment.cutoffTwoNovelSimpleFlowCapacityAt_of_componentSplitPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment.CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment.toCofinalNovelNewShellMassEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment.CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment.CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment.toCompletedStrictContractionData
