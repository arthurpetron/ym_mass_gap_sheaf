/-
# The exact cofinal return-floor frontier for the all-spin vacuum star

The preceding finite construction gives a positive ray-flow capacity at each
cutoff, but its value may depend on the cutoff.  This module isolates the
precise missing uniform datum: one positive rational below the explicit
finite return floor at every sufficiently large cutoff.

Such a datum compiles without carrier-cardinality loss into one positive
capacity for every oriented spin-ray spoke at every later cutoff.  The
compiler is unconditional; this module does not inhabit the cofinal datum.
It therefore proves no full-sector or completed spectral gap and makes no
thermodynamic, continuum, or Clay claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor

namespace YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The one missing scalar datum -/

/-- A named, Type-level assertion that the explicit finite spin-ray return
floors have a positive cofinal lower bound.  No inhabitant is supplied here. -/
structure FixedNomeCofinalSpinCubeRayReturnFloor
    {w : Q'} (hw : (0 : Q') < w) : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  start : Nat
  floor_le : ∀ K, start ≤ K →
    floor ≤ centralLowerExcitedSpinCubeReturnFloor hw K

/-- The corresponding cofinal capacity conclusion, restricted honestly to
the explicit spin-ray subsector. -/
structure FixedNomeCofinalSpinCubeRayCapacity
    {w : Q'} (hw : (0 : Q') < w) : Type where
  delta : Q'
  delta_pos : (0 : Q') < delta
  start : Nat
  twice_le_return : ∀ K, start ≤ K →
    ∀ offset, (hoffset : offset < K) →
      2 * delta ≤
        centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset
  left_spoke : ∀ K, start ≤ K →
    ∀ offset, (hoffset : offset < K) →
      delta * centralLowerExcitedSpinCubeRayFlowLoad
          w (Q'.le_of_lt hw) K
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) 0 ≤
        centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) 0
  right_spoke : ∀ K, start ≤ K →
    ∀ offset, (hoffset : offset < K) →
      delta * centralLowerExcitedSpinCubeRayFlowLoad
          w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) ≤
        centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset)

namespace FixedNomeCofinalSpinCubeRayReturnFloor

/-! ## 2. Lossless compilation to cofinal spoke capacity -/

def rayDelta {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) : Q' :=
  Q'.divPos family.floor 2 (by decide)

theorem rayDelta_pos {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) :
    (0 : Q') < family.rayDelta := by
  unfold rayDelta
  exact Q'.divPos_pos _ _ (by decide) family.floor_pos

theorem twice_rayDelta_eqv_floor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) :
    2 * family.rayDelta ≈ family.floor := by
  unfold rayDelta
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv 2
      (Q'.divPos family.floor 2 (by decide)))
    (Q'.divPos_mul_eqv family.floor 2 (by decide))

theorem twice_rayDelta_le_return
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw)
    {K : Nat} (hK : family.start ≤ K)
    {offset : Nat} (hoffset : offset < K) :
    2 * family.rayDelta ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv family.twice_rayDelta_eqv_floor)
    (Q'.le_trans' _ _ _
      (family.floor_le K hK)
      (centralLowerExcitedSpinCubeReturnFloor_le hw hoffset))

/-- At each later cutoff the cofinal datum gives an actual finite ray-capacity
certificate, with the same `delta` rather than the cutoff-dependent canonical
finite minimum. -/
def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw)
    (K : Nat) (hK : family.start ≤ K) :
    CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K where
  delta := family.rayDelta
  delta_pos := family.rayDelta_pos
  twice_le_return := fun _offset hoffset =>
    family.twice_rayDelta_le_return hK hoffset
  left_spoke := fun _offset hoffset =>
    delta_mul_leftSpokeLoad_le_kernel_of_twice_delta_le_return
      hw hoffset family.rayDelta
      (Q'.le_of_lt family.rayDelta_pos)
      (family.twice_rayDelta_le_return hK hoffset)
  right_spoke := fun _offset hoffset =>
    delta_mul_rightSpokeLoad_le_kernel_of_twice_delta_le_return
      hw hoffset family.rayDelta
      (Q'.le_of_lt family.rayDelta_pos)
      (family.twice_rayDelta_le_return hK hoffset)

def toCofinalRayCapacity
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) :
    FixedNomeCofinalSpinCubeRayCapacity hw where
  delta := family.rayDelta
  delta_pos := family.rayDelta_pos
  start := family.start
  twice_le_return := fun _K hK _offset hoffset =>
    family.twice_rayDelta_le_return hK hoffset
  left_spoke := fun K hK offset hoffset =>
    (family.finiteCapacityAt K hK).left_spoke offset hoffset
  right_spoke := fun K hK offset hoffset =>
    (family.finiteCapacityAt K hK).right_spoke offset hoffset

end FixedNomeCofinalSpinCubeRayReturnFloor

end YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor.FixedNomeCofinalSpinCubeRayReturnFloor.rayDelta_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor.FixedNomeCofinalSpinCubeRayReturnFloor.twice_rayDelta_le_return
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor.FixedNomeCofinalSpinCubeRayReturnFloor.finiteCapacityAt
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor.FixedNomeCofinalSpinCubeRayReturnFloor.toCofinalRayCapacity
