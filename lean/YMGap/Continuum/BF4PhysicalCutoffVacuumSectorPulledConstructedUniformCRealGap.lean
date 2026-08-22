/-
# Unconditional same-object BF4 gap data on every fixed carrier

For every fixed nome, representation base, and half-extent, the persistent
positive-edge floor is already constructed.  This module applies the finite
Poincare and Bishop-real contraction compilers to that witness and seals the
result as one dependent package: a rational rate, its strictness, the finite
tail estimate, and the same-object cutoff-limit inequality.

The package is pointwise in the base carrier.  Its rate and tail start may
vary with that base.  It does not provide a common cofinal rate, a completed
Hilbert-space gap, a thermodynamic limit, a continuum QFT, or the Clay result.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

/-- One package records the fully constructed strict gap for a chosen finite
base carrier, both on its later moving forms and on their Bishop-real limits. -/
structure FixedBaseConstructedUniformGapData
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) : Type 1 where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  start : Nat
  start_ge_base : base ≤ start
  moving_abs_gap : ∀ later : Nat, start ≤ later →
    ∀ coefficient : Nat → Q',
      let moving :=
        centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient
      Q'.abs
          (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w (Q'.le_of_lt hw0) base later half moving) ≤
        rate *
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w (Q'.le_of_lt hw0) base later half moving
  cutoffLimit_gap : ∀ coefficient : Nat → Q',
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' rate)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient))

/-- **Unconditional fixed-base same-object gap data.**  The body is fully
kernel checked and sealed so clients need not normalize the explicit finite
positive minimum and canonical-path ceiling. -/
opaque fixedBaseConstructedUniformGapData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    FixedBaseConstructedUniformGapData w hw0 hw1 base half := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  exact
    { rate := FixedBasePulledPositiveEdgeFloor.uniformPoincareRate certificate
      rate_nonnegative :=
        FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_nonnegative
          certificate
      rate_lt_one :=
        FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_lt_one certificate
      start := certificate.start
      start_ge_base := certificate.start_ge_base
      moving_abs_gap := by
        intro later hlater coefficient
        exact
          FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate
            certificate later hlater coefficient
      cutoffLimit_gap := by
        intro coefficient
        exact
          centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal
            hw0 hw1 base half certificate coefficient }

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap.fixedBaseConstructedUniformGapData
