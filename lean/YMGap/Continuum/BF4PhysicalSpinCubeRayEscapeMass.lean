/-
# Exact non-vacuum escape mass for the all-spin vacuum star

For an admitted excited spin cube, stationarity of the canonical finite
vacuum sector says that the full source-row mass is its stationary weight.
This module removes the unique vacuum index from that literal finite row and
identifies the remainder as the non-vacuum escape mass.  Thus the row splits
exactly into the vacuum-return joint mass plus all competing targets.

A pointwise comparison `escape <= C * vacuumReturnJoint`, with explicit
nonnegative `C`, then yields the return-probability floor `1 / (1 + C)`.
This is the precise causal bridge needed by the cofinal ray-capacity compiler;
no such cutoff-uniform comparison is asserted here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws

namespace YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Removing the unique vacuum entry from a duplicate-free row -/

private theorem listQSum_eqv_zero_add_filter_nonzero
    (value : Nat → Q') :
    ∀ states : List Nat,
      states.Nodup →
      0 ∈ states →
      listQSum value states ≈
        value 0 +
          listQSum value
            (states.filter (fun state => decide (state ≠ 0)))
  | [], _hnodup, hzero => by cases hzero
  | first :: rest, hnodup, hzero => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hfirst : first = 0
      · subst first
        have hfilter :
            rest.filter (fun state => decide (state ≠ 0)) = rest := by
          apply List.filter_eq_self.mpr
          intro state hstate
          apply decide_eq_true
          intro hstateZero
          apply hparts.1
          exact hstateZero ▸ hstate
        simp only [listQSum, List.filter_cons, ne_eq,
          not_true_eq_false, decide_false, Bool.false_eq_true,
          ↓reduceIte, hfilter]
        exact Q'.eqv_refl _
      · have hzeroRest : 0 ∈ rest := by
          rcases List.mem_cons.mp hzero with hzeroFirst | hzeroTail
          · exact False.elim (hfirst hzeroFirst.symm)
          · exact hzeroTail
        have ih := listQSum_eqv_zero_add_filter_nonzero
          value rest hparts.2 hzeroRest
        simp only [listQSum, List.filter_cons, ne_eq, hfirst,
          not_false_eq_true, decide_true, ↓reduceIte]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (value first) _ _ ih) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_assoc_eqv (value first) (value 0)
              (listQSum value
                (rest.filter (fun state => decide (state ≠ 0)))))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.add_comm_eqv (value first) (value 0))) ?_
        exact Q'.add_assoc_eqv (value 0) (value first)
          (listQSum value
            (rest.filter (fun state => decide (state ≠ 0))))

private theorem listQSum_nonnegative_local
    (value : Nat → Q') :
    ∀ states : List Nat,
      (∀ state, state ∈ states → (0 : Q') ≤ value state) →
      (0 : Q') ≤ listQSum value states
  | [], _hvalue => Q'.le_refl' 0
  | first :: rest, hvalue =>
      Q'.zero_le_add _ _
        (hvalue first List.mem_cons_self)
        (listQSum_nonnegative_local value rest
          (fun state hstate =>
            hvalue state (List.mem_cons_of_mem first hstate)))

/-! ## 2. Literal non-vacuum target list and escape mass -/

def centralPhysicalFiniteVacuumSectorNonVacuumIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun index => decide (index ≠ 0))

/-- The literal joint-kernel row mass from an excited spin cube to every
non-vacuum target in the canonical finite vacuum sector. -/
def centralLowerExcitedSpinCubeNonVacuumEscapeMass
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) : Q' :=
  listQSum
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset))
    (centralPhysicalFiniteVacuumSectorNonVacuumIndices
      w (Q'.le_of_lt hw) K)

theorem centralLowerExcitedSpinCubeNonVacuumEscapeMass_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset := by
  unfold centralLowerExcitedSpinCubeNonVacuumEscapeMass
  apply listQSum_nonnegative_local
  intro target _htarget
  unfold centralPhysicalFiniteKernel
  exact centralNormalizedPhysicalReflectedKernel_nonnegative
    (Q'.le_of_lt hw) K 0 _ _

/-- Exact source-row decomposition: stationary weight equals the vacuum joint
entry plus the literal sum over all non-vacuum sector targets. -/
theorem centralLowerExcitedSpinCube_weight_eqv_vacuumJoint_add_escape
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) ≈
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) 0 +
        centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset := by
  let source := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let sector := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let value := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 source
  have hsource : source ∈ sector :=
    centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)
  have hstationary :
      listQSum value sector ≈
        centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 source :=
    centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hsource
  have hsplit :
      listQSum value sector ≈
        value 0 +
          listQSum value
            (sector.filter (fun index => decide (index ≠ 0))) :=
    listQSum_eqv_zero_add_filter_nonzero value sector
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw) K 0)
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hstationary) hsplit

/-- The non-vacuum escape is a literal nonnegative part of the stationary
row, hence is bounded above by the source weight. -/
theorem centralLowerExcitedSpinCubeNonVacuumEscapeMass_le_weight
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset ≤
      centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) := by
  let joint := centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
    (centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K offset) 0
  let escape := centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset
  have hjoint : (0 : Q') ≤ joint := by
    unfold joint centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (Q'.le_of_lt hw) K 0 _ _
  have hpart : escape ≤ joint + escape := by
    have h := Q'.add_le_add_right 0 joint escape hjoint
    rw [Q'.zero_add'] at h
    exact h
  exact Q'.le_trans' _ _ _ hpart
    (Q'.ge_of_eqv
      (centralLowerExcitedSpinCube_weight_eqv_vacuumJoint_add_escape
        hw hoffset))

/-! ## 3. A pointwise escape ceiling forces a return floor -/

def spinCubeEscapeReturnFloor (ceiling : Q')
    (hceiling : (0 : Q') ≤ ceiling) : Q' :=
  Q'.recipPos (1 + ceiling)
    (Q'.pos_add_nonneg (by decide) hceiling)

theorem spinCubeEscapeReturnFloor_pos (ceiling : Q')
    (hceiling : (0 : Q') ≤ ceiling) :
    (0 : Q') < spinCubeEscapeReturnFloor ceiling hceiling := by
  unfold spinCubeEscapeReturnFloor
  exact Q'.recipPos_pos _ _

theorem spinCubeEscapeReturnFloor_le_one (ceiling : Q')
    (hceiling : (0 : Q') ≤ ceiling) :
    spinCubeEscapeReturnFloor ceiling hceiling ≤ 1 := by
  let denominator := (1 : Q') + ceiling
  let floor := spinCubeEscapeReturnFloor ceiling hceiling
  have hfloor0 : (0 : Q') ≤ floor :=
    Q'.le_of_lt (spinCubeEscapeReturnFloor_pos ceiling hceiling)
  have honeDenominator : (1 : Q') ≤ denominator :=
    Q'.add_le_self_of_nonneg 1 ceiling hceiling
  have hscaled : 1 * floor ≤ denominator * floor :=
    Q'.mul_le_mul_of_nonneg_right 1 denominator floor
      honeDenominator hfloor0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv floor))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.mul_recipPos_eqv denominator
          (Q'.pos_add_nonneg (by decide) hceiling))))

/-- If all competing non-vacuum target mass is at most `ceiling` times the
vacuum joint entry, then the actual return probability is at least
`1 / (1 + ceiling)`. -/
theorem spinCubeEscapeReturnFloor_le_return_of_escape_le
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (ceiling : Q')
    (hceiling : (0 : Q') ≤ ceiling)
    (hescape :
      centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset ≤
        ceiling *
          centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K offset) 0) :
    spinCubeEscapeReturnFloor ceiling hceiling ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let joint := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 index 0
  let escape := centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 index
  let denominator := (1 : Q') + ceiling
  let floor := spinCubeEscapeReturnFloor ceiling hceiling
  have hweightPos : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega))
  have hweightCeiling : weight ≤ denominator * joint := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centralLowerExcitedSpinCube_weight_eqv_vacuumJoint_add_escape
          hw hoffset)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left joint escape (ceiling * joint) hescape) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.add_mul_eqv 1 ceiling joint)
          (Q'.add_eqv_congr_right _ _ _
            (Q'.one_mul_eqv joint))))
  have hfloor0 : (0 : Q') ≤ floor :=
    Q'.le_of_lt (spinCubeEscapeReturnFloor_pos ceiling hceiling)
  have hscaled : floor * weight ≤ floor * (denominator * joint) :=
    Q'.mul_le_mul_of_nonneg_left weight (denominator * joint) floor
      hweightCeiling hfloor0
  have hcollapse : floor * (denominator * joint) ≈ joint := by
    have hfloorDenominator : floor * denominator ≈ 1 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv floor denominator) ?_
      exact Q'.mul_recipPos_eqv denominator
        (Q'.pos_add_nonneg (by decide) hceiling)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv floor denominator joint)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ joint
        hfloorDenominator) ?_
    exact Q'.one_mul_eqv joint
  apply Q'.le_divPos_of_mul_le joint weight hweightPos
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

end YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass.centralLowerExcitedSpinCubeNonVacuumEscapeMass_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass.centralLowerExcitedSpinCube_weight_eqv_vacuumJoint_add_escape
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass.centralLowerExcitedSpinCubeNonVacuumEscapeMass_le_weight
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass.spinCubeEscapeReturnFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass.spinCubeEscapeReturnFloor_le_one
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass.spinCubeEscapeReturnFloor_le_return_of_escape_le
