/-
# Explicit simple-carrier Poincare rate on each pulled BF4 carrier

The loop-erased endpoint estimate has the positive base scale

  1 + (vacuum-sector carrier length)^2.

The generic endpoint-scale compiler combines it with the persistent pulled
edge floor, producing a strict rational Poincare rate on every fixed base
carrier.  The scale and floor may still vary with the base, so no all-base
common rate, unconditional completed gap, thermodynamic/continuum limit, or
Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

namespace FixedBasePulledPositiveEdgeFloor

def simpleCarrierEndpointScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    FixedBasePulledEndpointScaleData certificate where
  scale := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    w hw base half
  scale_pos :=
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
      w hw base half
  endpoint_bound := by
    intro later hlater coefficient left hleft right hright
    exact
      BF4PhysicalCutoffVacuumSectorPulledSimplePathScale.FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_pulledDirichlet
        certificate later hlater coefficient left right hleft hright

def simpleCarrierPoincareScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    FixedBasePulledPoincareScaleData certificate :=
  (simpleCarrierEndpointScaleData certificate).toPoincareScaleData

def simpleCarrierPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Q' :=
  (simpleCarrierPoincareScaleData certificate).rate

theorem simpleCarrierPoincareRate_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    (0 : Q') ≤ simpleCarrierPoincareRate certificate :=
  (simpleCarrierPoincareScaleData certificate).rate_nonnegative

theorem simpleCarrierPoincareRate_lt_one
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    simpleCarrierPoincareRate certificate < (1 : Q') :=
  (simpleCarrierPoincareScaleData certificate).rate_lt_one

theorem moving_abs_gap_at_simpleCarrierPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w hw base later half moving) ≤
      simpleCarrierPoincareRate certificate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving :=
  (simpleCarrierPoincareScaleData certificate).moving_abs_gap
    later hlater coefficient

end FixedBasePulledPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap.FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareScaleData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap.FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap.FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_simpleCarrierPoincareRate
