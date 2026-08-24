/-
# Carrier-growth obstruction for the finite simple coercivity floor

The finite vacuum-sector edge floor is defined by folding a minimum with `1`
as an explicit fallback candidate.  It is therefore always at most one.  The
simple coercivity floor divides this edge floor by `1 + N^2`, where `N` is the
literal vacuum-component state count.

It follows that any fixed nonnegative floor lying below a later simple floor
must satisfy the exact quadratic budget

  fixedFloor * ofNat (N^2) <= 1.

For the fixed positive cutoff-two novel-flow floor, a cofinal simple-floor
comparison therefore forces the same uniform quadratic state-count budget at
every chosen cutoff.  This isolates the next missing combinatorial step:
construct enough connected positive-row states to escape that budget.

No unbounded carrier-growth theorem is proved here, so the cofinal comparison
is not declared impossible.  No completed gap without that open comparison,
thermodynamic/continuum construction, continuum QFT, or Clay mass gap is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The constructed edge floor is normalized by one -/

theorem listPositiveMinOne_le_one
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      listPositiveMinOne value states ≤ 1
  | [] => Q'.le_refl' 1
  | _first :: rest =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one value rest)

theorem centralPhysicalFiniteVacuumSectorEdgeFloor_le_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorEdgeFloor
      w hw cutoff half ≤ 1 := by
  unfold centralPhysicalFiniteVacuumSectorEdgeFloor
  exact listPositiveMinOne_le_one _ _

/-! ## 2. Every fixed-floor comparison imposes a quadratic size budget -/

theorem centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_mul_scale_le_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
          w hw cutoff half *
        centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          w hw cutoff half ≤
      1 := by
  have heq :
      centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
            w hw cutoff half *
          centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
            w hw cutoff half ≈
        centralPhysicalFiniteVacuumSectorEdgeFloor
          w hw cutoff half := by
    unfold centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
    exact Q'.divPos_mul_eqv
      (centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
        w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
        w hw cutoff half)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv heq)
    (centralPhysicalFiniteVacuumSectorEdgeFloor_le_one
      w hw cutoff half)

theorem fixedFloor_mul_simpleCarrierSquareScale_le_one_of_le
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (fixedFloor : Q')
    (hfixed : fixedFloor ≤
      centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
        w hw cutoff half) :
    fixedFloor *
        centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          w hw cutoff half ≤
      1 := by
  have hscale0 : (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
        w hw cutoff half :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
        w hw cutoff half)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hfixed hscale0)
    (centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_mul_scale_le_one
      w hw cutoff half)

theorem fixedFloor_mul_vacuumStateCountSquare_le_one_of_le
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (fixedFloor : Q')
    (hfixed0 : (0 : Q') ≤ fixedFloor)
    (hfixed : fixedFloor ≤
      centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
        w hw cutoff half) :
    fixedFloor *
        Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half *
            centralPhysicalFiniteMovingBaseStateCount w hw cutoff half) ≤
      1 := by
  let square := Q'.ofNat
    (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half *
      centralPhysicalFiniteMovingBaseStateCount w hw cutoff half)
  have hsquare_le_scale : square ≤
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
        w hw cutoff half := by
    unfold square centralPhysicalFiniteMovingBaseStateCount
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    have hadd := Q'.add_le_add_right
      (0 : Q') 1
      (Q'.ofNat
        ((centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length *
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length))
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ fixedFloor
      hsquare_le_scale hfixed0)
    (fixedFloor_mul_simpleCarrierSquareScale_le_one_of_le
      w hw cutoff half fixedFloor hfixed)

/-! ## 3. Consequence for the proposed cutoff-two cofinal comparison -/

theorem cutoffTwoFixedFloorComparison_forces_stateCountSquareBudget
    (later : Nat)
    (hfixed : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoLaterSimpleCoercivityFloor later) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount
              cutoffTwoHalfCoupling (by decide) later 0 *
            centralPhysicalFiniteMovingBaseStateCount
              cutoffTwoHalfCoupling (by decide) later 0) ≤
      1 := by
  unfold cutoffTwoLaterSimpleCoercivityFloor at hfixed
  exact fixedFloor_mul_vacuumStateCountSquare_le_one_of_le
    cutoffTwoHalfCoupling (by decide) later 0
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    hfixed

namespace CutoffTwoCofinalSimpleCoercivityFloorComparison

theorem stateCountSquareBudget
    (family : CutoffTwoCofinalSimpleCoercivityFloorComparison)
    (request : Nat) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount
              cutoffTwoHalfCoupling (by decide) (family.anchor request) 0 *
            centralPhysicalFiniteMovingBaseStateCount
              cutoffTwoHalfCoupling (by decide) (family.anchor request) 0) ≤
      1 :=
  cutoffTwoFixedFloorComparison_forces_stateCountSquareBudget
    (family.anchor request)
    (family.fixedFloor_le_simpleFloor request)

end CutoffTwoCofinalSimpleCoercivityFloorComparison

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction.listPositiveMinOne_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction.centralPhysicalFiniteVacuumSectorEdgeFloor_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction.centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_mul_scale_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction.fixedFloor_mul_vacuumStateCountSquare_le_one_of_le
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction.cutoffTwoFixedFloorComparison_forces_stateCountSquareBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction.CutoffTwoCofinalSimpleCoercivityFloorComparison.stateCountSquareBudget
