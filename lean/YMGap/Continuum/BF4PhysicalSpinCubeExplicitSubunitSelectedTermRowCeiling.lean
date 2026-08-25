/-
# A selected-term spin-cube row ceiling at every subunit nome

The arbitrary-nome degree-thirteen face envelope bounds the 66 non-source
faces of the central BF4 spin cube.  The source faces factor exactly as the
literal selected zero-boundary physical term.  Consequently every rational
`0 < w < 1` has a computed cutoff-uniform selected-term row ceiling, hence a
positive cofinal return floor and ray capacity.

The ceiling is nome-dependent and can grow as `w -> 1`; no physical uniform
gap or continuum estimate follows from this result alone.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
is used.
-/

import YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm
import YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
import YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling

namespace YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-- The explicit 66-face ceiling compares the complete raw row with its
literal selected physical production term at every positive subunit nome. -/
def explicitSubunitCentralSpinCubeSelectedTermRowCeiling
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw0 where
  ceiling := explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w
  start := 0
  rawRow_le := by
    intro cutoff _hcutoff offset hoffset
    have hspin : offset + 1 <= cutoff := by omega
    have hraw :=
      centralLowerSpinCubePositiveRawRow_le_activity_mul_explicitFixedNomeCeiling
        hw0 hw1 hspin
    have hselected :=
      centralLowerSpinCubePhysicalTerm_eqv w hspin
    exact Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv
            ((coeffW w (offset + 1)) ^ 6)
            (explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w))
          (Q'.mul_eqv_congr_left
            (explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w) _ _
            (Q'.eqv_symm hselected))))

theorem explicitSubunitCentralSpinCubeReturnFloor_pos
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') <
      (explicitSubunitCentralSpinCubeSelectedTermRowCeiling
        w hw0 hw1).returnFloor :=
  (explicitSubunitCentralSpinCubeSelectedTermRowCeiling
    w hw0 hw1).returnFloor_pos

theorem explicitSubunitCentralSpinCubeRayCapacity_pos
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') <
      (explicitSubunitCentralSpinCubeSelectedTermRowCeiling
        w hw0 hw1).toCofinalRayCapacity.delta :=
  (explicitSubunitCentralSpinCubeSelectedTermRowCeiling
    w hw0 hw1).toCofinalRayCapacity.delta_pos

end YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling.explicitSubunitCentralSpinCubeSelectedTermRowCeiling
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling.explicitSubunitCentralSpinCubeReturnFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling.explicitSubunitCentralSpinCubeRayCapacity_pos
