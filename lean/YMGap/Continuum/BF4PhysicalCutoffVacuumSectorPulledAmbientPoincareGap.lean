/-
# An ambient-cardinality Poincare rate with the transparent BF4 edge floor

For each fixed cutoff, the loop-erased vacuum-sector scale is bounded by the
explicit full Cartesian carrier square.  This module enlarges the endpoint
scale accordingly and combines it with the transparent finite-minimum edge
floor.  The resulting fixed-base rate is completely explicit in the ambient
enumeration and the pulled-kernel minimum.

The ambient enlargement is intentionally cruder than the sector scale.  Its
purpose is to expose cutoff dependence, not to assert a common all-cutoff
rate, thermodynamic/continuum control, or a Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Enlarge the endpoint scale to the explicit ambient count -/

/-- A fixed-base Poincare datum together with the exact equation identifying
its scale with the full Cartesian carrier square. -/
structure ExplicitAmbientPoincareScaleFormula
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat)
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Type 1 where
  data : FixedBasePulledPoincareScaleData certificate
  scale_eqv_ambient : data.scale ≈
    centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale base half

/-- Construct the ambient endpoint estimate and compile it once. The proof
payload is opaque, while `scale_eqv_ambient` remains a public exact formula. -/
opaque explicitAmbientPoincareScaleFormula
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    ExplicitAmbientPoincareScaleFormula
      w (Q'.le_of_lt hw0) base half
      (explicitFixedBasePulledPositiveEdgeFloor hw0 hw1 base half) := by
  let certificate := explicitFixedBasePulledPositiveEdgeFloor
    hw0 hw1 base half
  let simple := FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareScaleData
    certificate
  let ambient : FixedBasePulledPoincareScaleData certificate :=
    { scale := centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
        base half
      scale_pos :=
        centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale_pos base half
      floor_mul_diagonal_le_scale_mul_deficit := by
        intro later hlater coefficient
        let moving :=
          centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
            w (Q'.le_of_lt hw0) base later half coefficient
        let diagonal :=
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w (Q'.le_of_lt hw0) base later half moving
        let matrix :=
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w (Q'.le_of_lt hw0) base later half moving
        have hsimple := simple.floor_mul_diagonal_le_scale_mul_deficit
          later hlater coefficient
        have hbaseLater : base ≤ later :=
          Nat.le_trans certificate.start_ge_base hlater
        have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
          (w := w) (hw := Q'.le_of_lt hw0)
          base later half hbaseLater coefficient
        have hdeficit0 : (0 : Q') ≤ diagonal + -matrix :=
          Q'.sub_nonneg_of_le hmatrixDiagonal
        have hscale : simple.scale ≤
            centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
              base half :=
          centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_le_ambient
            w (Q'.le_of_lt hw0) base half
        exact Q'.le_trans' _ _ _ hsimple
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hscale hdeficit0) }
  exact
    { data := ambient
      scale_eqv_ambient := Q'.eqv_refl _ }

def explicitAmbientPoincareScaleData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    FixedBasePulledPoincareScaleData
      (explicitFixedBasePulledPositiveEdgeFloor hw0 hw1 base half) :=
  (explicitAmbientPoincareScaleFormula hw0 hw1 base half).data

theorem explicitAmbientPoincareScaleData_scale_eqv_ambient
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    (explicitAmbientPoincareScaleData hw0 hw1 base half).scale ≈
      centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
        base half :=
  (explicitAmbientPoincareScaleFormula
    hw0 hw1 base half).scale_eqv_ambient

def explicitAmbientPoincareRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) : Q' :=
  (explicitAmbientPoincareScaleData hw0 hw1 base half).rate

theorem explicitAmbientPoincareRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    (0 : Q') ≤ explicitAmbientPoincareRate hw0 hw1 base half :=
  (explicitAmbientPoincareScaleData hw0 hw1 base half).rate_nonnegative

theorem explicitAmbientPoincareRate_lt_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    explicitAmbientPoincareRate hw0 hw1 base half < (1 : Q') :=
  (explicitAmbientPoincareScaleData hw0 hw1 base half).rate_lt_one

/-! ## 2. The ambient rate really dominates the sharper sector rate -/

theorem explicitSimpleCarrierPoincareRate_le_ambient
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareRate
        (explicitFixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤
      explicitAmbientPoincareRate hw0 hw1 base half := by
  have hscale :
      (FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareScaleData
          (explicitFixedBasePulledPositiveEdgeFloor
            hw0 hw1 base half)).scale ≤
        (explicitAmbientPoincareScaleData hw0 hw1 base half).scale :=
    Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_le_ambient
        w (Q'.le_of_lt hw0) base half)
      (Q'.ge_of_eqv
        (explicitAmbientPoincareScaleData_scale_eqv_ambient
          hw0 hw1 base half))
  exact FixedBasePulledPoincareScaleData.rate_le_of_scale_le
    (FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareScaleData
      (explicitFixedBasePulledPositiveEdgeFloor hw0 hw1 base half))
    (explicitAmbientPoincareScaleData hw0 hw1 base half)
    hscale

theorem moving_abs_gap_at_explicitAmbientPoincareRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half later : Nat)
    (hlater :
      (explicitFixedBasePulledPositiveEdgeFloor
        hw0 hw1 base half).start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half moving) ≤
      explicitAmbientPoincareRate hw0 hw1 base half *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) base later half moving :=
  (explicitAmbientPoincareScaleData hw0 hw1 base half).moving_abs_gap
    later hlater coefficient

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap.explicitAmbientPoincareScaleFormula
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap.explicitAmbientPoincareScaleData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap.explicitAmbientPoincareScaleData_scale_eqv_ambient
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap.explicitAmbientPoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap.explicitSimpleCarrierPoincareRate_le_ambient
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap.moving_abs_gap_at_explicitAmbientPoincareRate
