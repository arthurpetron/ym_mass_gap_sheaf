/-
# A denominator-cleared BF4 floor/path frontier

The constructed fixed-base rate is

  pathCeiling / (pathCeiling + edgeFloor).

Consequently a supplied common strict rate `q` bounds every constructed rate
exactly when the denominator-cleared inequalities

  pathCeiling <= q * (pathCeiling + edgeFloor)

hold for every base carrier.  This module packages those concrete rational
inequalities and compiles them to the cross-carrier rate certificate, the
cofinal moving-centered vacuum-sector gap, and its Bishop-real limit form.

No inhabitant of the all-base floor/path inequalities is asserted.  No
vacuum-sector completion, thermodynamic limit, continuum QFT, or Clay
conclusion is claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling

/-- One strict common rate together with the exact denominator-cleared
floor/path inequality on every finite base carrier. -/
structure FixedNomeUniformFloorPathRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  ceiling_le_rate_mul_denominator : ∀ base : Nat,
    centralPhysicalFiniteVacuumSectorPathCeiling
        w (Q'.le_of_lt hw0) base half ≤
      q *
        (centralPhysicalFiniteVacuumSectorPathCeiling
            w (Q'.le_of_lt hw0) base half +
          (fixedBasePulledPositiveEdgeFloor
            hw0 hw1 base half).floor)

namespace FixedNomeUniformFloorPathRateBound

/-- The denominator-cleared inequality is precisely an upper bound on the
constructed fixed-base Poincare rate. -/
theorem uniformPoincareRate_le
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformFloorPathRateBound w hw0 hw1 half q)
    (base : Nat) :
    FixedBasePulledPositiveEdgeFloor.uniformPoincareRate
        (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤ q := by
  let floor := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  apply Q'.divPos_le_of_le_mul
    (centralPhysicalFiniteVacuumSectorPathCeiling
      w (Q'.le_of_lt hw0) base half)
    (FixedBasePulledPositiveEdgeFloor.uniformGapDenominator floor)
    (FixedBasePulledPositiveEdgeFloor.uniformGapDenominator_pos floor)
  exact family.ceiling_le_rate_mul_denominator base

/-- Concrete all-base floor/path inequalities inhabit the exact cross-carrier
rate certificate for the already constructed fixed-base packages. -/
def toUniformConstructedVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformFloorPathRateBound w hw0 hw1 half q) :
    FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  constructedRate_le := by
    intro base
    let data := fixedBaseConstructedUniformGapData hw0 hw1 base half
    rw [data.rate_eq_uniformPoincareRate]
    exact family.uniformPoincareRate_le base

/-- The same floor/path data therefore supplies the existing cofinal
moving-centered vacuum-sector strict-gap certificate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformFloorPathRateBound w hw0 hw1 half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q :=
  family.toUniformConstructedVacuumSectorRateBound.toVacuumSectorCenteredStrictGap

/-- Hence the common floor/path rate controls every fixed carrier's moving
centered Bishop-real matrix limit by its diagonal limit. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (family : FixedNomeUniformFloorPathRateBound w hw0 hw1 half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  family.toUniformConstructedVacuumSectorRateBound.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half base coefficient

end FixedNomeUniformFloorPathRateBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate.FixedNomeUniformFloorPathRateBound.uniformPoincareRate_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate.FixedNomeUniformFloorPathRateBound.toUniformConstructedVacuumSectorRateBound
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate.FixedNomeUniformFloorPathRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate.FixedNomeUniformFloorPathRateBound.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
