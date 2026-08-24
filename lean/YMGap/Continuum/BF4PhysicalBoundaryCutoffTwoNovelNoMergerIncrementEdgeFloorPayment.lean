/-
# No-merger, increment-only scalar payment for the cutoff-two novel flow

When the executable no-component-merger check succeeds, the merger mass is
zero and the new-shell stationary mass is bounded by the corrected-slab
cutoff increment alone.  This file proves that the scalar inequality

  novelFloor * ((65 + newShellLength) * (2 * cutoffIncrement))
    <= half * finitePositiveEdgeFloor

then implies all four finite novel-flow capacity blocks.  A cofinal family
carrying both the successful checks and these payments compiles to the
existing completed strict-contraction datum.

Both cofinal fields remain explicit and uninhabited.  In particular, a fixed
base cutoff-two increment is not asserted to decay with the later cutoff.
No uniform gap, thermodynamic/continuum construction, or Clay mass gap is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate
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

/-! ## 1. No merger reduces the component-split payment to the increment -/

theorem cutoffTwoComponentSplitPayment_of_noMergerIncrementPayment
    {later : Nat}
    (hcheck : cutoffTwoNoComponentMergerCheck later = true)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            (Q'.ofNat 2 *
              slabParametricKCutoffIncrement
                cutoffTwoHalfCoupling 2 later (centralExtent 0))) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 + (cutoffTwoEdgeLoadNewStates later).length) *
          (Q'.ofNat 2 *
            (slabParametricKCutoffIncrement
                cutoffTwoHalfCoupling 2 later (centralExtent 0) +
              cutoffTwoNewComponentMergerMass later))) ≤
      HalfPow.half *
        centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 := by
  let increment :=
    slabParametricKCutoffIncrement
      cutoffTwoHalfCoupling 2 later (centralExtent 0)
  have hzero := cutoffTwoNewComponentMergerMass_eqv_zero_of_check hcheck
  have hadd :
      increment + cutoffTwoNewComponentMergerMass later ≈ increment :=
    Q'.eqv_trans _ (increment + 0) _
      (Q'.add_eqv_congr_left increment _ 0 hzero)
      (Q'.eqv_of_eq (Q'.add_zero' increment))
  have htwo := Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hadd
  have hsize := Q'.mul_eqv_congr_left
    (Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length)) _ _ htwo
  have hscaled := Q'.mul_eqv_congr_left
    cutoffTwoNovelSimpleFlowCoercivityFloor _ _ hsize
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled) hpayment

/-! ## 2. The increment-only payment inhabits finite capacity -/

def cutoffTwoNovelSimpleFlowCapacityAt_of_noMergerIncrementPayment
    (later : Nat)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later)
    (hcheck : cutoffTwoNoComponentMergerCheck later = true)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            (Q'.ofNat 2 *
              slabParametricKCutoffIncrement
                cutoffTwoHalfCoupling 2 later (centralExtent 0))) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoNovelSimpleFlowCapacityAt later := by
  apply cutoffTwoNovelSimpleFlowCapacityAt_of_componentSplitPayment
    later hlaterFloor hlaterMass
  exact cutoffTwoComponentSplitPayment_of_noMergerIncrementPayment
    hcheck hpayment

/-! ## 3. A cofinal checked payment reaches contraction -/

structure CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  no_merger : ∀ request,
    cutoffTwoNoComponentMergerCheck (anchor request) = true
  payment : ∀ request,
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 +
              (cutoffTwoEdgeLoadNewStates (anchor request)).length) *
          (Q'.ofNat 2 *
            slabParametricKCutoffIncrement cutoffTwoHalfCoupling 2
              (anchor request) (centralExtent 0))) ≤
      HalfPow.half *
        centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment

def toCofinalNovelComponentSplitEdgeFloorPayment
    (family : CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment) :
    CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  payment := fun request =>
    cutoffTwoComponentSplitPayment_of_noMergerIncrementPayment
      (family.no_merger request) (family.payment request)

def toCofinalNovelSimpleFlowCapacity
    (family : CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment) :
    CutoffTwoCofinalNovelSimpleFlowCapacity :=
  family.toCofinalNovelComponentSplitEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment.cutoffTwoComponentSplitPayment_of_noMergerIncrementPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment.cutoffTwoNovelSimpleFlowCapacityAt_of_noMergerIncrementPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment.CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment.toCofinalNovelComponentSplitEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment.CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment.CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment.toCompletedStrictContractionData
