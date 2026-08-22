/-
# Unconditional common gaps on every finite prefix of BF4 carriers

Each fixed finite vacuum carrier has a constructed rational rate below one.
Located rational maxima therefore give one strict common rate on every finite
prefix of base cutoffs.  This module constructs that prefix rate and packages
both the later moving-form estimates and the same-object Bishop-real limit
inequalities for every base in the prefix.

The prefix bound is finite and fixed.  No bound away from one is proved as the
prefix expands without limit, so this does not inhabit the all-carrier rate
certificate, prove a completed gap, or reach a thermodynamic/continuum or Clay
conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

private theorem max'_lt_local {left right ceiling : Q'}
    (hleft : left < ceiling) (hright : right < ceiling) :
    Q'.max' left right < ceiling := by
  unfold Q'.max'
  by_cases h : left ≤ right
  · rw [if_pos h]
    exact hright
  · rw [if_neg h]
    exact hleft

/-! ## 1. Located finite-prefix maximum -/

/-- The constructed strict rate on one chosen fixed base carrier. -/
def constructedFixedBaseRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half base : Nat) : Q' :=
  (fixedBaseConstructedUniformGapData hw0 hw1 base half).rate

theorem constructedFixedBaseRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half base : Nat) :
    (0 : Q') ≤ constructedFixedBaseRate hw0 hw1 half base :=
  (fixedBaseConstructedUniformGapData
    hw0 hw1 base half).rate_nonnegative

theorem constructedFixedBaseRate_lt_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half base : Nat) :
    constructedFixedBaseRate hw0 hw1 half base < (1 : Q') :=
  (fixedBaseConstructedUniformGapData hw0 hw1 base half).rate_lt_one

/-- Located maximum of the constructed rates for bases `0, ..., bound`. -/
def constructedFinitePrefixRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) : Q' :=
  Q'.runningMax (constructedFixedBaseRate hw0 hw1 half) bound

theorem constructedFixedBaseRate_le_finitePrefixRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half base bound : Nat) (hbase : base ≤ bound) :
    constructedFixedBaseRate hw0 hw1 half base ≤
      constructedFinitePrefixRate hw0 hw1 half bound := by
  induction bound with
  | zero =>
      have hbaseEq : base = 0 := Nat.eq_zero_of_le_zero hbase
      subst base
      exact Q'.le_runningMax
        (constructedFixedBaseRate hw0 hw1 half) 0
  | succ bound ih =>
      by_cases hprevious : base ≤ bound
      · exact Q'.le_trans' _ _ _ (ih hprevious)
          (Q'.le_runningMax_succ
            (constructedFixedBaseRate hw0 hw1 half) bound)
      · have hbaseEq : base = bound + 1 := by omega
        subst base
        exact Q'.le_runningMax
          (constructedFixedBaseRate hw0 hw1 half) (bound + 1)

theorem constructedFinitePrefixRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) :
    (0 : Q') ≤ constructedFinitePrefixRate hw0 hw1 half bound := by
  exact Q'.le_trans' _ _ _
    (constructedFixedBaseRate_nonnegative hw0 hw1 half bound)
    (Q'.le_runningMax
      (constructedFixedBaseRate hw0 hw1 half) bound)

theorem constructedFinitePrefixRate_lt_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : ∀ bound : Nat,
    constructedFinitePrefixRate hw0 hw1 half bound < (1 : Q')
  | 0 => constructedFixedBaseRate_lt_one hw0 hw1 half 0
  | bound + 1 => by
      exact max'_lt_local
        (constructedFinitePrefixRate_lt_one hw0 hw1 half bound)
        (constructedFixedBaseRate_lt_one hw0 hw1 half (bound + 1))

/-! ## 2. Common finite and limit estimates on a finite prefix -/

theorem constructedFinitePrefixMoving_abs_gap
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound base : Nat) (hbase : base ≤ bound)
    (later : Nat)
    (hlater :
      (fixedBaseConstructedUniformGapData hw0 hw1 base half).start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half moving) ≤
      constructedFinitePrefixRate hw0 hw1 half bound *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) base later half moving := by
  let data := fixedBaseConstructedUniformGapData hw0 hw1 base half
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w (Q'.le_of_lt hw0) base later half coefficient
  have hgap := data.moving_abs_gap later hlater coefficient
  have hbaseLater : base ≤ later :=
    Nat.le_trans data.start_ge_base hlater
  have hmatrixNonnegative := fixedBasePulledMovingMatrix_nonnegative
    (w := w) (hw := Q'.le_of_lt hw0)
    base later half hbaseLater coefficient
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
    (w := w) (hw := Q'.le_of_lt hw0)
    base later half hbaseLater coefficient
  have hdiagonal : (0 : Q') ≤
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half moving :=
    Q'.le_trans' _ _ _ hmatrixNonnegative hmatrixDiagonal
  exact Q'.le_trans' _ _ _ hgap
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (constructedFixedBaseRate_le_finitePrefixRate
        hw0 hw1 half base bound hbase)
      hdiagonal)

theorem constructedFinitePrefixCutoffLimit_gap
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound base : Nat) (hbase : base ≤ bound)
    (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' (constructedFinitePrefixRate hw0 hw1 half bound))
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) := by
  let matrix :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
      hw0 hw1 base half coefficient
  let diagonal :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
      hw0 hw1 base half coefficient
  let data := fixedBaseConstructedUniformGapData hw0 hw1 base half
  apply cReal_leEv_of_eventual_abs_gap matrix diagonal
    (constructedFinitePrefixRate hw0 hw1 half bound)
    (constructedFinitePrefixRate_nonnegative hw0 hw1 half bound)
    (constructedFinitePrefixRate_lt_one hw0 hw1 half bound)
    data.start
  intro later hlater
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit_approx]
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit_approx]
  exact constructedFinitePrefixMoving_abs_gap
    hw0 hw1 half bound base hbase later hlater coefficient

/-! ## 3. One unconditional package for a finite carrier prefix -/

/-- One strict common rate and its finite-tail and Bishop-real consequences on
all base carriers up to and including `bound`. -/
structure FixedCarrierPrefixConstructedUniformGapData
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) : Type 1 where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  baseRate_le : ∀ base : Nat, base ≤ bound →
    constructedFixedBaseRate hw0 hw1 half base ≤ rate
  moving_abs_gap : ∀ base : Nat, base ≤ bound →
    ∀ later : Nat,
      (fixedBaseConstructedUniformGapData hw0 hw1 base half).start ≤ later →
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
  cutoffLimit_gap : ∀ base : Nat, base ≤ bound →
    ∀ coefficient : Nat → Q',
      CReal.leEv
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
          hw0 hw1 base half coefficient)
        (CReal.mul
          (CReal.ofQ' rate)
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
            hw0 hw1 base half coefficient))

/-- **Unconditional finite-prefix common gap.**  Finite located maximum is the
only compactness principle used; no infinite supremum is inferred. -/
def fixedCarrierPrefixConstructedUniformGapData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) :
    FixedCarrierPrefixConstructedUniformGapData
      w hw0 hw1 half bound where
  rate := constructedFinitePrefixRate hw0 hw1 half bound
  rate_nonnegative :=
    constructedFinitePrefixRate_nonnegative hw0 hw1 half bound
  rate_lt_one := constructedFinitePrefixRate_lt_one hw0 hw1 half bound
  baseRate_le := by
    intro base hbase
    exact constructedFixedBaseRate_le_finitePrefixRate
      hw0 hw1 half base bound hbase
  moving_abs_gap := constructedFinitePrefixMoving_abs_gap
    hw0 hw1 half bound
  cutoffLimit_gap := constructedFinitePrefixCutoffLimit_gap
    hw0 hw1 half bound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap.constructedFixedBaseRate_le_finitePrefixRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap.constructedFinitePrefixRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap.constructedFinitePrefixCutoffLimit_gap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap.fixedCarrierPrefixConstructedUniformGapData
