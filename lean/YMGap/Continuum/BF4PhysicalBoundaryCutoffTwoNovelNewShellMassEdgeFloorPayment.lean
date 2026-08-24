/-
# A new-shell stationary-mass edge-floor payment

The exact novel endpoint mass is at most twice the stationary mass of the
genuinely new shell.  Therefore the single scalar inequality

  novelFloor * (ofNat (65 + newShellLength) * (2 * newMass))
    <= half * finitePositiveEdgeFloor

implies the mass-refined payment, all four novel-flow capacity blocks, and—if
supplied cofinally—the existing completed strict-contraction datum.

The cofinal payment remains an explicit field.  No decay estimate for the
new-shell stationary mass, comparison with the positive-edge floor,
thermodynamic/continuum construction, or Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

/-! ## 1. New-shell mass pays the mass-refined scalar inequality -/

theorem cutoffTwoStationaryMassEdgeFloorPayment_of_newShellMassEdgeFloorPayment
    (later : Nat)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            (Q'.ofNat 2 * cutoffTwoNewMass later)) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 + (cutoffTwoEdgeLoadNewStates later).length) *
          cutoffTwoNovelEndpointWeightMass later) ≤
      HalfPow.half *
        centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 := by
  have hmass := cutoffTwoNovelEndpointWeightMass_le_two_mul_newMass later
  have hsize := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length))
    hmass
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat
      (65 + (cutoffTwoEdgeLoadNewStates later).length))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    cutoffTwoNovelSimpleFlowCoercivityFloor
    hsize
    (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
  exact Q'.le_trans' _ _ _ hscaled hpayment

/-! ## 2. The new-shell payment inhabits finite capacity -/

def cutoffTwoNovelSimpleFlowCapacityAt_of_newShellMassEdgeFloorPayment
    (later : Nat)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            (Q'.ofNat 2 * cutoffTwoNewMass later)) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoNovelSimpleFlowCapacityAt later :=
  cutoffTwoNovelSimpleFlowCapacityAt_of_stationaryMassEdgeFloorPayment
    later hlaterFloor hlaterMass
    (cutoffTwoStationaryMassEdgeFloorPayment_of_newShellMassEdgeFloorPayment
      later hpayment)

/-! ## 3. A cofinal new-shell payment reaches completed contraction -/

structure CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment : Type 1 where
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
          (Q'.ofNat 2 * cutoffTwoNewMass (anchor request))) ≤
      HalfPow.half *
        centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment

def toCofinalNovelStationaryMassEdgeFloorPayment
    (family : CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment) :
    CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  payment := by
    intro request
    exact
      cutoffTwoStationaryMassEdgeFloorPayment_of_newShellMassEdgeFloorPayment
        (family.anchor request) (family.payment request)

def toCofinalNovelSimpleFlowCapacity
    (family : CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment) :
    CutoffTwoCofinalNovelSimpleFlowCapacity :=
  family.toCofinalNovelStationaryMassEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment.cutoffTwoStationaryMassEdgeFloorPayment_of_newShellMassEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment.cutoffTwoNovelSimpleFlowCapacityAt_of_newShellMassEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment.CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment.toCofinalNovelStationaryMassEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment.CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment.CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment.toCompletedStrictContractionData
