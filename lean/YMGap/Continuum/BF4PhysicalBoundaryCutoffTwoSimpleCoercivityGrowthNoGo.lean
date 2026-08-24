/-
# Linear carrier growth rules out the cofinal simple-floor comparison

The fixed cutoff-two novel-flow floor is a strictly positive constructive
rational.  If `d` is its positive denominator, then multiplying the floor by
`(d + 1)^2` is already strictly greater than one.  On the other hand, every
comparison with a later simple floor forces the floor times the square of
the later rooted-sector state count to be at most one.

The all-spin cube ray proves that this state count is at least `later + 1`.
Thus no comparison is possible once `d <= later`, and the proposed cofinal
comparison certificate is uninhabited.

This no-go theorem applies only to the crude simple-path floor obtained by
dividing a normalized edge minimum by `1 + N^2`.  It does not rule out a
uniform spectral gap obtained by sharper flow, canonical-path, multiscale,
or direct operator estimates.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction
import YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth

/-! ## 1. An explicit quadratic escape scale for every positive rational -/

/-- A positive rational multiplied by the square of one more than its own
denominator is strictly greater than one.  No Archimedean choice is needed:
the denominator itself is an explicit witness. -/
theorem one_lt_mul_den_succ_square
    (value : Q') (hvalue : (0 : Q') < value) :
    (1 : Q') <
      value * Q'.ofNat ((value.den + 1) * (value.den + 1)) := by
  have hnum : (0 : Int) < value.num := Q'.num_pos_of_pos hvalue
  have hsquareNat :
      value.den < (value.den + 1) * (value.den + 1) := by
    have hstep : value.den < value.den + 1 := Nat.lt_succ_self _
    have hmul : value.den + 1 <=
        (value.den + 1) * (value.den + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos value.den)
    exact Nat.lt_of_lt_of_le hstep hmul
  have hsquareInt :
      (value.den : Int) <
        (((value.den + 1) * (value.den + 1) : Nat) : Int) :=
    Int.ofNat_lt.mpr hsquareNat
  have honeNum : (1 : Int) <= value.num := by omega
  have hmulInt :
      (((value.den + 1) * (value.den + 1) : Nat) : Int) <=
        value.num *
          (((value.den + 1) * (value.den + 1) : Nat) : Int) := by
    have hnonnegative : (0 : Int) <=
        (((value.den + 1) * (value.den + 1) : Nat) : Int) :=
      Int.natCast_nonneg _
    have hscaled := Int.mul_le_mul_of_nonneg_right honeNum hnonnegative
    simpa only [Int.one_mul] using hscaled
  show (1 : Int) *
        (((value * Q'.ofNat
          ((value.den + 1) * (value.den + 1))).den : Nat) : Int) <
      (value * Q'.ofNat
        ((value.den + 1) * (value.den + 1))).num * (1 : Int)
  rw [Q'.mul_den_cast]
  simp only [Q'.ofNat, Q'.den, Int.one_mul, Int.mul_one]
  simpa [Q'.den] using Int.lt_of_lt_of_le hsquareInt hmulInt

/-! ## 2. The actual rooted state count crosses that scale -/

theorem cutoffTwoMovingBaseStateCount_ge_cutoff_succ
    (later : Nat) :
    later + 1 <=
      centralPhysicalFiniteMovingBaseStateCount
        cutoffTwoHalfCoupling (by decide) later 0 := by
  unfold centralPhysicalFiniteMovingBaseStateCount
  exact centralPhysicalFiniteVacuumSectorIndices_length_ge_cutoff_succ
    (by decide : (0 : Q') < cutoffTwoHalfCoupling) later

/-- Beyond the explicit denominator threshold, the fixed positive novel-flow
floor cannot lie below the later simple coercivity floor. -/
theorem cutoffTwoFixedFloor_not_le_simpleFloor_of_den_le
    (later : Nat)
    (hlater : cutoffTwoNovelSimpleFlowCoercivityFloor.den <= later) :
    Not (cutoffTwoNovelSimpleFlowCoercivityFloor <=
      cutoffTwoLaterSimpleCoercivityFloor later) := by
  intro hfixed
  let count := centralPhysicalFiniteMovingBaseStateCount
    cutoffTwoHalfCoupling (by decide) later 0
  have hcount : later + 1 <= count := by
    exact cutoffTwoMovingBaseStateCount_ge_cutoff_succ later
  have hthreshold :
      cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1 <= count := by
    omega
  have hsquareNat :
      (cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1) *
          (cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1) <=
        count * count :=
    Nat.mul_le_mul hthreshold hthreshold
  have hsquareQ :
      Q'.ofNat
          ((cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1) *
            (cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1)) <=
        Q'.ofNat (count * count) :=
    Q'.ofNat_le_ofNat hsquareNat
  have hscaled :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          Q'.ofNat
            ((cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1) *
              (cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1)) <=
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          Q'.ofNat (count * count) :=
    Q'.mul_le_mul_of_nonneg_left _ _
      cutoffTwoNovelSimpleFlowCoercivityFloor hsquareQ
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
  have hbudget :=
    cutoffTwoFixedFloorComparison_forces_stateCountSquareBudget
      later hfixed
  change cutoffTwoNovelSimpleFlowCoercivityFloor *
      Q'.ofNat (count * count) <= 1 at hbudget
  have hle :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          Q'.ofNat
            ((cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1) *
              (cutoffTwoNovelSimpleFlowCoercivityFloor.den + 1)) <=
        1 :=
    Q'.le_trans' _ _ _ hscaled hbudget
  have hlt := one_lt_mul_den_succ_square
    cutoffTwoNovelSimpleFlowCoercivityFloor
    cutoffTwoNovelSimpleFlowCoercivityFloor_pos
  exact (Int.not_lt_of_ge hle) hlt

/-! ## 3. The cofinal comparison certificate is empty -/

theorem cutoffTwoCofinalSimpleCoercivityFloorComparison_impossible
    (family : CutoffTwoCofinalSimpleCoercivityFloorComparison) : False := by
  let request := cutoffTwoNovelSimpleFlowCoercivityFloor.den
  have hrequest : request <= family.anchor request := by
    exact Nat.le_trans
      (Nat.le_max_right
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request)
      (family.anchor_ge request)
  exact cutoffTwoFixedFloor_not_le_simpleFloor_of_den_le
    (family.anchor request) hrequest
    (family.fixedFloor_le_simpleFloor request)

theorem no_cutoffTwoCofinalSimpleCoercivityFloorComparison :
    Not (Nonempty CutoffTwoCofinalSimpleCoercivityFloorComparison) := by
  intro hfamily
  rcases hfamily with ⟨family⟩
  exact cutoffTwoCofinalSimpleCoercivityFloorComparison_impossible family

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo.one_lt_mul_den_succ_square
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo.cutoffTwoMovingBaseStateCount_ge_cutoff_succ
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo.cutoffTwoFixedFloor_not_le_simpleFloor_of_den_le
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo.cutoffTwoCofinalSimpleCoercivityFloorComparison_impossible
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo.no_cutoffTwoCofinalSimpleCoercivityFloorComparison
