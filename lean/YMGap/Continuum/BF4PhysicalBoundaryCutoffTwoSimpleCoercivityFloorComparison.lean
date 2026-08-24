/-
# Compile a cofinal simple-coercivity floor comparison to completed contraction

The exact new-block mass automatically satisfies the scalar edge-floor
payment at each later sector's own simple coercivity floor.  The existing
cutoff-two novel-flow compiler instead requires the fixed positive floor

  cutoffTwoNovelSimpleFlowCoercivityFloor.

Consequently the remaining comparison is direct: whenever that fixed floor
is at most the later simple floor, monotonicity of multiplication transfers
the automatic payment to the fixed-floor payment.  This file proves the
finite transfer and packages a cofinal family of such comparisons into the
already constructed novel-flow capacity and completed cylinder strict-
contraction data.

The cofinal comparison family is an explicit open certificate and is not
inhabited here.  In particular, no cutoff-uniform lower bound on the later
simple floors, thermodynamic/continuum construction, continuum QFT, or Clay
mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity

/-! ## 1. The later simple floor and its exact finite transfer -/

def cutoffTwoLaterSimpleCoercivityFloor (later : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
    cutoffTwoHalfCoupling (by decide) later 0

theorem cutoffTwoLaterSimpleCoercivityFloor_pos (later : Nat) :
    (0 : Q') < cutoffTwoLaterSimpleCoercivityFloor later :=
  centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_pos
    cutoffTwoHalfCoupling (by decide) later 0

theorem cutoffTwoNovelNewShellMassEdgeFloorPayment_of_fixedFloor_le_simpleFloor
    (later : Nat) (hcutoff : 2 ≤ later)
    (hfloor : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoLaterSimpleCoercivityFloor later) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 + (cutoffTwoEdgeLoadNewStates later).length) *
          (Q'.ofNat 2 * cutoffTwoNewMass later)) ≤
      HalfPow.half *
        YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor.centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 := by
  let load := centralPhysicalFiniteMovingBaseSimpleNewMassLoad
    cutoffTwoHalfCoupling (by decide) 2 later 0
  have hload0 : (0 : Q') ≤ load := by
    unfold load centralPhysicalFiniteMovingBaseSimpleNewMassLoad
    exact Q'.mul_nonneg _ _
      (Q'.ofNat_nonneg
        (centralPhysicalFiniteMovingBaseStateCount
          cutoffTwoHalfCoupling (by decide) later 0))
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg 2)
        (centralPhysicalFiniteVacuumSectorNewMass_nonnegative
          cutoffTwoHalfCoupling (by decide) 2 later 0))
  have hscaled :
      cutoffTwoNovelSimpleFlowCoercivityFloor * load ≤
        cutoffTwoLaterSimpleCoercivityFloor later * load :=
    Q'.mul_le_mul_of_nonneg_right _ _ load hfloor hload0
  have hauto := cutoffTwoMovingBaseSimpleNewMassPhysicalPayment
    later hcutoff
  have hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor * load ≤
        centralPhysicalFiniteMovingBaseEdgePaymentBudget
          cutoffTwoHalfCoupling (by decide) later 0 :=
    Q'.le_trans' _ _ _ hscaled hauto
  unfold load centralPhysicalFiniteMovingBaseSimpleNewMassLoad
    centralPhysicalFiniteMovingBaseEdgePaymentBudget at hpayment
  rw [cutoffTwoMovingBaseStateCount_eq_65_add_new hcutoff] at hpayment
  change cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 + (cutoffTwoEdgeLoadNewStates later).length) *
          (Q'.ofNat 2 * cutoffTwoNewMass later)) ≤
      HalfPow.half *
        YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor.centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 at hpayment
  exact hpayment

def cutoffTwoNovelSimpleFlowCapacityAt_of_fixedFloor_le_simpleFloor
    (later : Nat)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later)
    (hfloor : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoLaterSimpleCoercivityFloor later) :
    CutoffTwoNovelSimpleFlowCapacityAt later :=
  cutoffTwoNovelSimpleFlowCapacityAt_of_newShellMassEdgeFloorPayment
    later hlaterFloor hlaterMass
    (cutoffTwoNovelNewShellMassEdgeFloorPayment_of_fixedFloor_le_simpleFloor
      later
      (Nat.le_trans
        cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
        hlaterFloor)
      hfloor)

/-! ## 2. The exact cofinal comparison certificate -/

structure CutoffTwoCofinalSimpleCoercivityFloorComparison : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  fixedFloor_le_simpleFloor : ∀ request,
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoLaterSimpleCoercivityFloor (anchor request)

namespace CutoffTwoCofinalSimpleCoercivityFloorComparison

def toCofinalNovelNewShellMassEdgeFloorPayment
    (family : CutoffTwoCofinalSimpleCoercivityFloorComparison) :
    CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  payment := by
    intro request
    exact
      cutoffTwoNovelNewShellMassEdgeFloorPayment_of_fixedFloor_le_simpleFloor
        (family.anchor request)
        (Nat.le_trans
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
          (Nat.le_trans
            (Nat.le_max_left _ _)
            (Nat.le_trans
              (Nat.le_max_left _ _)
              (family.anchor_ge request))))
        (family.fixedFloor_le_simpleFloor request)

def toCofinalNovelSimpleFlowCapacity
    (family : CutoffTwoCofinalSimpleCoercivityFloorComparison) :
    CutoffTwoCofinalNovelSimpleFlowCapacity :=
  family.toCofinalNovelNewShellMassEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalSimpleCoercivityFloorComparison) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelNewShellMassEdgeFloorPayment.toCompletedStrictContractionData

end CutoffTwoCofinalSimpleCoercivityFloorComparison

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison.cutoffTwoLaterSimpleCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison.cutoffTwoNovelNewShellMassEdgeFloorPayment_of_fixedFloor_le_simpleFloor
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison.cutoffTwoNovelSimpleFlowCapacityAt_of_fixedFloor_le_simpleFloor
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison.CutoffTwoCofinalSimpleCoercivityFloorComparison.toCofinalNovelNewShellMassEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison.CutoffTwoCofinalSimpleCoercivityFloorComparison.toCofinalNovelSimpleFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison.CutoffTwoCofinalSimpleCoercivityFloorComparison.toCompletedStrictContractionData
