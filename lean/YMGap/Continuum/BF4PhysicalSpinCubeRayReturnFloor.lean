/-
# A constructive finite return floor for the all-spin vacuum star

At every finite cutoff, each admitted excited spin cube has a strictly
positive transition probability back to the vacuum.  This module takes the
literal minimum of those finitely many return probabilities, with the unit as
the empty-list fallback, and divides it by two.  The resulting explicit
positive rational pays every oriented spoke of the finite spin-ray flow.

The construction is non-vacuous at every cutoff and applies to every actual
ray vertex.  It does not prove that the finite floors stay bounded away from
zero as the cutoff grows, does not route the rest of the vacuum sector, and
makes no thermodynamic, continuum, or Clay claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity

namespace YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Strict positivity of every concrete ray return -/

theorem centralLowerExcitedSpinCubeVacuumReturnProbability_pos
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset := by
  unfold centralLowerExcitedSpinCubeVacuumReturnProbability
  exact Q'.divPos_pos _ _
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))
    (by
      change (0 : Q') < centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0
        (centralLowerSpinCubeIndex
          w (Q'.le_of_lt hw) K (offset + 1)) 0
      exact centralPhysicalFiniteKernel_spinCubeIndex_zero_pos
        hw (by omega))

/-- A total positive candidate on natural offsets.  Outside the admitted ray
the value is the harmless positive unit; only offsets in `List.range K` enter
the finite minimum. -/
def centralLowerExcitedSpinCubeReturnCandidate
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) : Q' :=
  if hoffset : offset < K then
    centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset
  else 1

theorem centralLowerExcitedSpinCubeReturnCandidate_pos
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) :
    (0 : Q') <
      centralLowerExcitedSpinCubeReturnCandidate hw K offset := by
  unfold centralLowerExcitedSpinCubeReturnCandidate
  by_cases hoffset : offset < K
  · rw [dif_pos hoffset]
    exact centralLowerExcitedSpinCubeVacuumReturnProbability_pos
      hw hoffset
  · rw [dif_neg hoffset]
    decide

/-! ## 2. The literal finite minimum and its half-capacity -/

def centralLowerExcitedSpinCubeReturnFloor
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) : Q' :=
  listPositiveMinOne
    (centralLowerExcitedSpinCubeReturnCandidate hw K)
    (List.range K)

theorem centralLowerExcitedSpinCubeReturnFloor_pos
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') < centralLowerExcitedSpinCubeReturnFloor hw K := by
  unfold centralLowerExcitedSpinCubeReturnFloor
  apply listPositiveMinOne_pos
  intro offset _hoffset
  exact centralLowerExcitedSpinCubeReturnCandidate_pos hw K offset

theorem centralLowerExcitedSpinCubeReturnFloor_le
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralLowerExcitedSpinCubeReturnFloor hw K ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset := by
  have hmin := listPositiveMinOne_le_of_mem
    (centralLowerExcitedSpinCubeReturnCandidate hw K)
    (List.range K) offset (List.mem_range.mpr hoffset)
  simpa [centralLowerExcitedSpinCubeReturnFloor,
    centralLowerExcitedSpinCubeReturnCandidate, hoffset] using hmin

/-- Half of the finite return floor is the explicit finite ray-flow capacity
constant. -/
def centralLowerExcitedSpinCubeRayCapacity
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) : Q' :=
  Q'.divPos (centralLowerExcitedSpinCubeReturnFloor hw K) 2 (by decide)

theorem centralLowerExcitedSpinCubeRayCapacity_pos
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') < centralLowerExcitedSpinCubeRayCapacity hw K := by
  unfold centralLowerExcitedSpinCubeRayCapacity
  exact Q'.divPos_pos _ _ (by decide)
    (centralLowerExcitedSpinCubeReturnFloor_pos hw K)

theorem twice_centralLowerExcitedSpinCubeRayCapacity_eqv_floor
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    2 * centralLowerExcitedSpinCubeRayCapacity hw K ≈
      centralLowerExcitedSpinCubeReturnFloor hw K := by
  unfold centralLowerExcitedSpinCubeRayCapacity
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv 2
      (Q'.divPos (centralLowerExcitedSpinCubeReturnFloor hw K)
        2 (by decide)))
    (Q'.divPos_mul_eqv
      (centralLowerExcitedSpinCubeReturnFloor hw K) 2 (by decide))

theorem twice_centralLowerExcitedSpinCubeRayCapacity_le_return
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    2 * centralLowerExcitedSpinCubeRayCapacity hw K ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (twice_centralLowerExcitedSpinCubeRayCapacity_eqv_floor hw K))
    (centralLowerExcitedSpinCubeReturnFloor_le hw hoffset)

/-! ## 3. A non-vacuous finite capacity certificate -/

structure CentralLowerExcitedSpinCubeFiniteRayCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) : Type where
  delta : Q'
  delta_pos : (0 : Q') < delta
  twice_le_return : ∀ offset, (hoffset : offset < K) →
    2 * delta ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset
  left_spoke : ∀ offset, (hoffset : offset < K) →
    delta * centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0 ≤
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0
  right_spoke : ∀ offset, (hoffset : offset < K) →
    delta * centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) ≤
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset)

def centralLowerExcitedSpinCubeFiniteRayCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K where
  delta := centralLowerExcitedSpinCubeRayCapacity hw K
  delta_pos := centralLowerExcitedSpinCubeRayCapacity_pos hw K
  twice_le_return := fun _offset hoffset =>
    twice_centralLowerExcitedSpinCubeRayCapacity_le_return hw hoffset
  left_spoke := fun _offset hoffset =>
    delta_mul_leftSpokeLoad_le_kernel_of_twice_delta_le_return
      hw hoffset (centralLowerExcitedSpinCubeRayCapacity hw K)
      (Q'.le_of_lt (centralLowerExcitedSpinCubeRayCapacity_pos hw K))
      (twice_centralLowerExcitedSpinCubeRayCapacity_le_return hw hoffset)
  right_spoke := fun _offset hoffset =>
    delta_mul_rightSpokeLoad_le_kernel_of_twice_delta_le_return
      hw hoffset (centralLowerExcitedSpinCubeRayCapacity hw K)
      (Q'.le_of_lt (centralLowerExcitedSpinCubeRayCapacity_pos hw K))
      (twice_centralLowerExcitedSpinCubeRayCapacity_le_return hw hoffset)

end YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor.centralLowerExcitedSpinCubeVacuumReturnProbability_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor.centralLowerExcitedSpinCubeReturnFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor.centralLowerExcitedSpinCubeReturnFloor_le
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor.centralLowerExcitedSpinCubeRayCapacity_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor.twice_centralLowerExcitedSpinCubeRayCapacity_le_return
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor.centralLowerExcitedSpinCubeFiniteRayCapacityAt
