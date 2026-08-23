/-
# A formula-carrying constructed BF4 pulled edge floor

The original persistent fixed-base certificate is opaque for elaboration
performance. This module independently packages the same proved estimates in
an opaque bundle which also carries exact projection equations. Its floor is
proved equal to one half of the positive minimum of the pulled kernel on the
finite base-sector pair carrier at the common row-tail anchor.

This exposes an exact finite formula; it does not provide a cutoff-uniform
lower bound and does not identify the new formula-carrying object with the
original opaque performance wrapper.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor

local infix:50 " ≈ " => Q'.eqv

/-- A fixed-base floor certificate together with exact equations exposing the
finite value and anchor chosen in its construction. -/
structure FixedBasePulledPositiveEdgeFloorFormula
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) : Type 1 where
  certificate : FixedBasePulledPositiveEdgeFloor w hw base half
  floor_eqv_value : certificate.floor ≈
    fixedBasePulledPositiveEdgeFloorValue w hw base half
  start_eq_anchor : certificate.start =
    fixedBasePulledEdgeFloorAnchor w base half

/-- The formula-carrying copy of the constructed persistent fixed-base floor.
All fields are discharged by the public finite-minimum and half-retention
theorems; no field is assumed. The proof payload remains opaque so downstream
rate compilation does not unfold it. -/
opaque explicitFixedBasePulledPositiveEdgeFloorFormula
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    FixedBasePulledPositiveEdgeFloorFormula
      w (Q'.le_of_lt hw0) base half :=
  { certificate :=
      { floor := fixedBasePulledPositiveEdgeFloorValue
          w (Q'.le_of_lt hw0) base half
        floor_pos := fixedBasePulledPositiveEdgeFloorValue_pos
          w (Q'.le_of_lt hw0) base half
        start := fixedBasePulledEdgeFloorAnchor w base half
        start_ge_base := fixedBasePulledEdgeFloorAnchor_ge_base w base half
        floor_le := by
          intro later hlater left right hleft hright hbasePositive
          exact Q'.le_trans' _ _ _
            (fixedBasePulledPositiveEdgeFloorValue_le_half_anchor
              hleft hright hbasePositive)
            (half_mul_centralPhysicalFinitePulledKernel_le_of_increment_le_one
              (fixedBasePulledEdgeFloorAnchor_ge_base w base half)
              hlater
              (fixedBasePulledEdgeFloor_increment_le_one hw0 hw1 hlater)
              hleft hright) }
    floor_eqv_value := Q'.eqv_refl _
    start_eq_anchor := rfl }

/-- The certificate projection used by fixed-base and cofinal rate compilers. -/
def explicitFixedBasePulledPositiveEdgeFloor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    FixedBasePulledPositiveEdgeFloor
      w (Q'.le_of_lt hw0) base half :=
  (explicitFixedBasePulledPositiveEdgeFloorFormula
    hw0 hw1 base half).certificate

/-- The floor projection of the certificate exposes the exact
finite-minimum value. -/
theorem explicitFixedBasePulledPositiveEdgeFloor_floor_eqv_value
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    (explicitFixedBasePulledPositiveEdgeFloor
        hw0 hw1 base half).floor ≈
      fixedBasePulledPositiveEdgeFloorValue
        w (Q'.le_of_lt hw0) base half := by
  exact (explicitFixedBasePulledPositiveEdgeFloorFormula
    hw0 hw1 base half).floor_eqv_value

/-- The start projection is the explicit maximum of the base cutoff and the
common row-tail cutoff. -/
theorem explicitFixedBasePulledPositiveEdgeFloor_start_eq_anchor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    (explicitFixedBasePulledPositiveEdgeFloor
        hw0 hw1 base half).start =
      fixedBasePulledEdgeFloorAnchor w base half := by
  exact (explicitFixedBasePulledPositiveEdgeFloorFormula
    hw0 hw1 base half).start_eq_anchor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula.explicitFixedBasePulledPositiveEdgeFloorFormula
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula.explicitFixedBasePulledPositiveEdgeFloor
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula.explicitFixedBasePulledPositiveEdgeFloor_floor_eqv_value
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula.explicitFixedBasePulledPositiveEdgeFloor_start_eq_anchor
