/-
# The explicit simple-carrier all-base BF4 rate frontier

Loop erasure replaces the opaque canonical-walk maximum by the explicit base
scale `1 + (# vacuum-sector states)^2`.  This module isolates one common
ceiling on the corresponding fixed-base rates and its exact
denominator-cleared carrier-size/edge-floor condition.  Either witness
contracts to the cofinal centered gap and the actual completed vacuum-sector
operator contraction.

The all-base witness is deliberately not inhabited.  No thermodynamic or
continuum limit, QFT reconstruction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

/-! ## 1. One common ceiling on the simple-carrier rates -/

structure FixedNomeUniformSimpleCarrierVacuumSectorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  simpleCarrierRate_le : ∀ base : Nat,
    FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareRate
      (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤ q

namespace FixedNomeUniformSimpleCarrierVacuumSectorRateBound

def selectedAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (_family : FixedNomeUniformSimpleCarrierVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) : Nat :=
  max (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half).start threshold

theorem selectedAnchor_ge
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformSimpleCarrierVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) :
    max base threshold ≤ family.selectedAnchor base threshold := by
  apply Nat.max_le.mpr
  exact
    ⟨Nat.le_trans
        (fixedBasePulledPositiveEdgeFloor
          hw0 hw1 base half).start_ge_base
        (Nat.le_max_left _ _),
      Nat.le_max_right _ _⟩

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformSimpleCarrierVacuumSectorRateBound
      w hw0 hw1 half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.selectedAnchor
  anchor_ge := family.selectedAnchor_ge
  centeredGap := by
    intro base threshold coefficient
    let certificate := fixedBasePulledPositiveEdgeFloor
      hw0 hw1 base half
    let later := family.selectedAnchor base threshold
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    have hstart : certificate.start ≤ later := Nat.le_max_left _ _
    have hbaseLater : base ≤ later :=
      Nat.le_trans certificate.start_ge_base hstart
    have hgap :=
      FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_simpleCarrierPoincareRate
        certificate later hstart coefficient
    have hmatrixNonnegative := fixedBasePulledMovingMatrix_nonnegative
      (w := w) (hw := Q'.le_of_lt hw0)
      base later half hbaseLater coefficient
    have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
      (w := w) (hw := Q'.le_of_lt hw0)
      base later half hbaseLater coefficient
    have hdiagonal : (0 : Q') ≤
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) base later half moving :=
      Q'.le_trans' _ _ _ hmatrixNonnegative hmatrixDiagonal
    exact Q'.le_trans' _ _ _ hgap
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (family.simpleCarrierRate_le base) hdiagonal)

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformSimpleCarrierVacuumSectorRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap

end FixedNomeUniformSimpleCarrierVacuumSectorRateBound

/-! ## 2. Exact denominator-cleared carrier-size frontier -/

structure FixedNomeUniformSimpleCarrierFloorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  simpleCarrierScale_le_rate_mul_denominator : ∀ base : Nat,
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    let scale := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
      w (Q'.le_of_lt hw0) base half
    scale ≤ q * (scale + certificate.floor)

namespace FixedNomeUniformSimpleCarrierFloorRateBound

theorem simpleCarrierPoincareRate_le
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformSimpleCarrierFloorRateBound
      w hw0 hw1 half q)
    (base : Nat) :
    FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareRate
        (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤ q := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  let data := FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareScaleData
    certificate
  apply Q'.divPos_le_of_le_mul data.scale data.denominator
    data.denominator_pos
  exact family.simpleCarrierScale_le_rate_mul_denominator base

def toUniformSimpleCarrierVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformSimpleCarrierFloorRateBound
      w hw0 hw1 half q) :
    FixedNomeUniformSimpleCarrierVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  simpleCarrierRate_le := family.simpleCarrierPoincareRate_le

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformSimpleCarrierFloorRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  FixedNomeUniformSimpleCarrierVacuumSectorRateBound.toCompletedStrictContractionData
    family.toUniformSimpleCarrierVacuumSectorRateBound

end FixedNomeUniformSimpleCarrierFloorRateBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge.FixedNomeUniformSimpleCarrierVacuumSectorRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge.FixedNomeUniformSimpleCarrierVacuumSectorRateBound.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge.FixedNomeUniformSimpleCarrierFloorRateBound.simpleCarrierPoincareRate_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge.FixedNomeUniformSimpleCarrierFloorRateBound.toCompletedStrictContractionData
