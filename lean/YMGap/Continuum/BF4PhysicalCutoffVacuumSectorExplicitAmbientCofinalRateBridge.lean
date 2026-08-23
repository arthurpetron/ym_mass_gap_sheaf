/-
# The explicit ambient-count/finite-minimum all-base BF4 frontier

The fixed-base rate now has two formula interfaces: its scale is one plus the
square of the full bounded-labelling count, and its persistent edge floor is
one half of an exact positive finite minimum of pulled physical-kernel
entries. This module isolates one common ceiling on those explicit rates and
compiles it to the same-object cofinal gap and completed vacuum-sector
contraction.

The all-base inequality is deliberately not inhabited. It is a sufficient,
fully expanded canonical-path frontier, not a claim that global path bounds
remain uniform or that the thermodynamic/continuum and Clay targets close.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One common ceiling on the explicit ambient rates -/

structure FixedNomeUniformExplicitAmbientVacuumSectorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  explicitAmbientRate_le : forall base : Nat,
    explicitAmbientPoincareRate hw0 hw1 base half ≤ q

namespace FixedNomeUniformExplicitAmbientVacuumSectorRateBound

def selectedAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (_family : FixedNomeUniformExplicitAmbientVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) : Nat :=
  max
    (explicitFixedBasePulledPositiveEdgeFloor
      hw0 hw1 base half).start
    threshold

theorem selectedAnchor_ge
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformExplicitAmbientVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) :
    max base threshold ≤ family.selectedAnchor base threshold := by
  apply Nat.max_le.mpr
  exact
    ⟨Nat.le_trans
        (explicitFixedBasePulledPositiveEdgeFloor
          hw0 hw1 base half).start_ge_base
        (Nat.le_max_left _ _),
      Nat.le_max_right _ _⟩

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformExplicitAmbientVacuumSectorRateBound
      w hw0 hw1 half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.selectedAnchor
  anchor_ge := family.selectedAnchor_ge
  centeredGap := by
    intro base threshold coefficient
    let certificate := explicitFixedBasePulledPositiveEdgeFloor
      hw0 hw1 base half
    let later := family.selectedAnchor base threshold
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    have hstart : certificate.start ≤ later := Nat.le_max_left _ _
    have hbaseLater : base ≤ later :=
      Nat.le_trans certificate.start_ge_base hstart
    have hgap := moving_abs_gap_at_explicitAmbientPoincareRate
      hw0 hw1 base half later hstart coefficient
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
        (family.explicitAmbientRate_le base) hdiagonal)

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformExplicitAmbientVacuumSectorRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap

end FixedNomeUniformExplicitAmbientVacuumSectorRateBound

/-! ## 2. Denominator-cleared primitive finite-data frontier -/

structure FixedNomeUniformExplicitAmbientFloorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  ambientScale_le_rate_mul_denominator : forall base : Nat,
    let scale :=
      centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale base half
    let floor := fixedBasePulledPositiveEdgeFloorValue
      w (Q'.le_of_lt hw0) base half
    scale ≤ q * (scale + floor)

namespace FixedNomeUniformExplicitAmbientFloorRateBound

theorem explicitAmbientPoincareRate_le
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformExplicitAmbientFloorRateBound
      w hw0 hw1 half q)
    (base : Nat) :
    explicitAmbientPoincareRate hw0 hw1 base half ≤ q := by
  let certificate := explicitFixedBasePulledPositiveEdgeFloor
    hw0 hw1 base half
  let data := explicitAmbientPoincareScaleData hw0 hw1 base half
  let scale :=
    centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale base half
  let floor := fixedBasePulledPositiveEdgeFloorValue
    w (Q'.le_of_lt hw0) base half
  have hscale : data.scale ≈ scale :=
    explicitAmbientPoincareScaleData_scale_eqv_ambient
      hw0 hw1 base half
  have hfloor : certificate.floor ≈ floor :=
    explicitFixedBasePulledPositiveEdgeFloor_floor_eqv_value
      hw0 hw1 base half
  have hdenominator : data.denominator ≈ scale + floor := by
    unfold FixedBasePulledPoincareScaleData.denominator
    exact Q'.eqv_trans _ (scale + certificate.floor) _
      (Q'.add_eqv_congr_right _ _ certificate.floor hscale)
      (Q'.add_eqv_congr_left scale _ _ hfloor)
  have hcleared : data.scale ≤ q * data.denominator :=
    Q'.le_trans' _ scale _ (Q'.le_of_eqv hscale)
      (Q'.le_trans' _ (q * (scale + floor)) _
        (family.ambientScale_le_rate_mul_denominator base)
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left q _ _
            (Q'.eqv_symm hdenominator))))
  unfold explicitAmbientPoincareRate
  apply Q'.divPos_le_of_le_mul data.scale data.denominator
    data.denominator_pos
  exact hcleared

def toUniformExplicitAmbientVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformExplicitAmbientFloorRateBound
      w hw0 hw1 half q) :
    FixedNomeUniformExplicitAmbientVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  explicitAmbientRate_le := family.explicitAmbientPoincareRate_le

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformExplicitAmbientFloorRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  FixedNomeUniformExplicitAmbientVacuumSectorRateBound.toCompletedStrictContractionData
    family.toUniformExplicitAmbientVacuumSectorRateBound

end FixedNomeUniformExplicitAmbientFloorRateBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge.FixedNomeUniformExplicitAmbientVacuumSectorRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge.FixedNomeUniformExplicitAmbientVacuumSectorRateBound.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge.FixedNomeUniformExplicitAmbientFloorRateBound.explicitAmbientPoincareRate_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge.FixedNomeUniformExplicitAmbientFloorRateBound.toCompletedStrictContractionData
