/-
# Selected-term raw-row ceiling for the all-spin vacuum star

The arbitrary-spin return is the raw vacuum entry divided by the raw positive-
carrier row, and the explicit zero-boundary physical term lies below that
vacuum entry.  Therefore one cutoff-independent comparison of the whole raw
row with this selected term gives a positive cofinal return floor.

This module proves that compiler and states its sole remaining estimate as an
honest Type-level structure.  The structure is intentionally uninhabited: no
uniform selected-term row ceiling, full-sector gap, thermodynamic limit,
continuum theory, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
import YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor

namespace YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One pointwise raw-row ceiling gives one return floor -/

def spinCubeSelectedTermReturnFloor
    (ceiling : Q') (hceiling : (0 : Q') < ceiling) : Q' :=
  Q'.recipPos ceiling hceiling

theorem spinCubeSelectedTermReturnFloor_pos
    (ceiling : Q') (hceiling : (0 : Q') < ceiling) :
    (0 : Q') < spinCubeSelectedTermReturnFloor ceiling hceiling :=
  Q'.recipPos_pos ceiling hceiling

theorem spinCubeSelectedTermReturnFloor_le_one
    (ceiling : Q') (hceiling : (0 : Q') < ceiling)
    (hone : (1 : Q') ≤ ceiling) :
    spinCubeSelectedTermReturnFloor ceiling hceiling ≤ 1 := by
  let floor := spinCubeSelectedTermReturnFloor ceiling hceiling
  have hfloor0 : (0 : Q') ≤ floor :=
    Q'.le_of_lt (spinCubeSelectedTermReturnFloor_pos ceiling hceiling)
  have hscaled : 1 * floor ≤ ceiling * floor :=
    Q'.mul_le_mul_of_nonneg_right 1 ceiling floor hone hfloor0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv floor))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_recipPos_eqv ceiling hceiling)))

/-- A ceiling on the literal raw row by a multiple of the selected positive
zero-boundary term yields the reciprocal lower bound on the actual return. -/
theorem spinCubeSelectedTermReturnFloor_le_return_of_rawRow_le
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (ceiling : Q')
    (hceiling : (0 : Q') < ceiling)
    (hrow :
      centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) K 0
          (centralLowerSpinCubeState (offset + 1)) ≤
        ceiling *
          slabParametricKPhysicalTerm w K 1
            (centralLowerSpinCubePhysical (offset + 1))) :
    spinCubeSelectedTermReturnFloor ceiling hceiling ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset := by
  let floor := spinCubeSelectedTermReturnFloor ceiling hceiling
  let row := centralPhysicalPositiveRawRowMass
    w (Q'.le_of_lt hw) K 0
    (centralLowerSpinCubeState (offset + 1))
  let selected := slabParametricKPhysicalTerm w K 1
    (centralLowerSpinCubePhysical (offset + 1))
  let numerator := centralPhysicalReflectedKernel w K 0
    (centralLowerSpinCubeState (offset + 1)) zeroEdgeLabelling
  have hfloor0 : (0 : Q') ≤ floor :=
    Q'.le_of_lt (spinCubeSelectedTermReturnFloor_pos ceiling hceiling)
  have hscaled : floor * row ≤ floor * (ceiling * selected) :=
    Q'.mul_le_mul_of_nonneg_left row (ceiling * selected) floor
      hrow hfloor0
  have hcollapse : floor * (ceiling * selected) ≈ selected := by
    have hfloorCeiling : floor * ceiling ≈ 1 := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv floor ceiling) ?_
      exact Q'.mul_recipPos_eqv ceiling hceiling
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv floor ceiling selected)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ selected hfloorCeiling) ?_
    exact Q'.one_mul_eqv selected
  have hfloorNumerator : floor * row ≤ numerator := by
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse)
        (centralLowerSpinCubePhysicalTerm_le_rawVacuumKernel
          hw K (offset + 1)))
  have hrawFloor : floor ≤
      Q'.divPos numerator row
        (centralPhysicalPositiveRawRowMass_pos
          (centralLowerSpinCubeState_mem_centralPositiveHalfStates
            (w := w) (K := K) (spin := offset + 1) hw (by omega))) := by
    apply Q'.le_divPos_of_mul_le numerator row
      (centralPhysicalPositiveRawRowMass_pos
        (centralLowerSpinCubeState_mem_centralPositiveHalfStates
          (w := w) (K := K) (spin := offset + 1) hw (by omega)))
    exact hfloorNumerator
  exact Q'.le_trans' _ _ _ hrawFloor
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (centralLowerExcitedSpinCubeVacuumReturnProbability_eqv_rawRatio
          hw hoffset)))

/-! ## 2. The exact cofinal analytic datum -/

/-- One cutoff-independent comparison of every later arbitrary-spin raw row
with its explicit selected zero-boundary physical term.  This is a stronger,
more geometric datum than an opaque return floor and is intentionally
uninhabited in this module. -/
structure FixedNomeCofinalSpinCubeSelectedTermRowCeiling
    {w : Q'} (hw : (0 : Q') < w) : Type where
  ceiling : Q'
  start : Nat
  rawRow_le : ∀ K, start ≤ K →
    ∀ offset, (hoffset : offset < K) →
      centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) K 0
          (centralLowerSpinCubeState (offset + 1)) ≤
        ceiling *
          slabParametricKPhysicalTerm w K 1
            (centralLowerSpinCubePhysical (offset + 1))

namespace FixedNomeCofinalSpinCubeSelectedTermRowCeiling

/-! ## 3. The comparison forces `1 <= ceiling` constructively -/

theorem one_le_ceiling
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw) :
    (1 : Q') ≤ family.ceiling := by
  let K := family.start + 1
  let selected := slabParametricKPhysicalTerm w K 1
    (centralLowerSpinCubePhysical 1)
  let row := centralPhysicalPositiveRawRowMass
    w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1)
  have hselectedPos : (0 : Q') < selected := by
    exact centralLowerSpinCubePhysicalTerm_pos hw (by
      unfold K
      omega)
  have hselectedRow : selected ≤ row :=
    centralLowerSpinCubePhysicalTerm_le_rawRowMass hw K 1
  have hrowCeiling : row ≤ family.ceiling * selected := by
    simpa only [K, selected, row] using
      family.rawRow_le K (by unfold K; omega) 0 (by unfold K; omega)
  have hscaled : selected * 1 ≤ selected * family.ceiling := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv selected))
      (Q'.le_trans' _ _ _ hselectedRow
        (Q'.le_trans' _ _ _ hrowCeiling
          (Q'.le_of_eqv
            (Q'.mul_comm_eqv family.ceiling selected))))
  exact Q'.le_of_mul_le_mul_left hscaled hselectedPos

theorem ceiling_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw) :
    (0 : Q') < family.ceiling :=
  Q'.pos_of_lt_of_le (by decide) family.one_le_ceiling

def returnFloor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw) : Q' :=
  spinCubeSelectedTermReturnFloor family.ceiling family.ceiling_pos

theorem returnFloor_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw) :
    (0 : Q') < family.returnFloor :=
  spinCubeSelectedTermReturnFloor_pos family.ceiling family.ceiling_pos

theorem returnFloor_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw) :
    family.returnFloor ≤ 1 :=
  spinCubeSelectedTermReturnFloor_le_one
    family.ceiling family.ceiling_pos family.one_le_ceiling

theorem returnFloor_le_return
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw)
    {K : Nat} (hK : family.start ≤ K)
    {offset : Nat} (hoffset : offset < K) :
    family.returnFloor ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset :=
  spinCubeSelectedTermReturnFloor_le_return_of_rawRow_le
    hw hoffset family.ceiling family.ceiling_pos
    (family.rawRow_le K hK offset hoffset)

private theorem le_listPositiveMinOne_of_forall_local
    {State : Type} (value : State → Q') (candidate : Q') :
    ∀ states : List State,
      candidate ≤ 1 →
      (∀ state, state ∈ states → candidate ≤ value state) →
      candidate ≤ listPositiveMinOne value states
  | [], hunit, _hall => hunit
  | first :: rest, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hall first List.mem_cons_self
      · rw [if_neg hle]
        exact le_listPositiveMinOne_of_forall_local
          value candidate rest hunit
          (fun state hstate =>
            hall state (List.mem_cons_of_mem first hstate))

theorem returnFloor_le_finiteReturnFloor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw)
    (K : Nat) (hK : family.start ≤ K) :
    family.returnFloor ≤
      centralLowerExcitedSpinCubeReturnFloor hw K := by
  unfold centralLowerExcitedSpinCubeReturnFloor
  apply le_listPositiveMinOne_of_forall_local
  · exact family.returnFloor_le_one
  · intro offset hoffsetMem
    have hoffset : offset < K := List.mem_range.mp hoffsetMem
    simpa [centralLowerExcitedSpinCubeReturnCandidate, hoffset] using
      family.returnFloor_le_return hK hoffset

/-! ## 4. Compilation to the existing cofinal ray-capacity frontier -/

def toCofinalRayReturnFloor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw) :
    FixedNomeCofinalSpinCubeRayReturnFloor hw where
  floor := family.returnFloor
  floor_pos := family.returnFloor_pos
  start := family.start
  floor_le := fun K hK => family.returnFloor_le_finiteReturnFloor K hK

def finiteRayCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw)
    (K : Nat) (hK : family.start ≤ K) :
    CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K :=
  family.toCofinalRayReturnFloor.finiteCapacityAt K hK

def toCofinalRayCapacity
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeSelectedTermRowCeiling hw) :
    FixedNomeCofinalSpinCubeRayCapacity hw :=
  family.toCofinalRayReturnFloor.toCofinalRayCapacity

end FixedNomeCofinalSpinCubeSelectedTermRowCeiling

end YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.spinCubeSelectedTermReturnFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.spinCubeSelectedTermReturnFloor_le_one
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.spinCubeSelectedTermReturnFloor_le_return_of_rawRow_le
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.one_le_ceiling
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.ceiling_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.returnFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.returnFloor_le_return
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.returnFloor_le_finiteReturnFloor
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.toCofinalRayReturnFloor
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.finiteRayCapacityAt
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling.FixedNomeCofinalSpinCubeSelectedTermRowCeiling.toCofinalRayCapacity
