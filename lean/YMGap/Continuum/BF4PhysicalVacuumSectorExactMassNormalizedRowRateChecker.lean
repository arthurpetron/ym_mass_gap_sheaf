/-
# Exact finite checker for the sharp mass-normalized row rate

The existing Boolean sector checker decides whether every actual finite row
obeys a supplied rational bound.  The exact normalized row maximum `h_K`
packages the same inequalities as one scalar.  This module proves that the
two interfaces are equivalent: for every nonnegative rate, the all-row check
succeeds exactly when `h_K` is at most that rate.

The cofinal checked-family and exact-rate-family structures therefore convert
in both directions without analytic slack.  The cutoff-one rank-one theorem
also gives an actual successful all-row check at rate zero.

No cofinal all-cutoff check is claimed.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate
import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker

namespace YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact one-row and all-row characterizations -/

theorem centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck_eq_true_iff
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    {rate : Q'} :
    centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck
        w hw cutoff half rate source = true ↔
      centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
          w hw cutoff half source ≤
        rate * centralPhysicalFiniteWeight w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck
    finiteCarrierMassNormalizedStationaryProductRowDistanceCheck
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
  simp only [decide_eq_true_eq]

theorem centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_rowBounds
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {rate : Q'} :
    centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
        w hw cutoff half rate = true ↔
      ∀ source,
        source ∈ centralPhysicalFiniteVacuumSectorIndices
            w hw cutoff half →
          centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
              w hw cutoff half source ≤
            rate * centralPhysicalFiniteWeight
              w hw cutoff half source := by
  constructor
  · intro checked source hsource
    simpa [centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance] using
      (centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_of_allRowsCheck
        checked source hsource)
  · intro hrow
    unfold centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
    apply List.all_eq_true.mpr
    intro source hsource
    exact
      centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck_eq_true_iff.mpr
        (hrow source hsource)

/-- The executable all-row checker recognizes precisely the upper bounds on
the sharp scalar `h_K`. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_exactRate_le
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {rate : Q'} (rate_nonnegative : (0 : Q') ≤ rate) :
    centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
        w hw cutoff half rate = true ↔
      centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        w hw cutoff half ≤ rate := by
  constructor
  · intro checked
    apply
      centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_of_rowBound
        rate_nonnegative
    exact
      centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_rowBounds.mp
        checked
  · intro hexact
    apply
      centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_rowBounds.mpr
    intro source hsource
    refine Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_le_exactRate_mul_weight
        hsource) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hexact
      (Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource))

/-! ## 2. Cofinal exact/checker equivalence -/

namespace FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound

def toCheckedRows
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound
      w hw half rate) :
    FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  allRows_checked := by
    intro base threshold
    exact
      (centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_exactRate_le
        family.rate_nonnegative).mpr
        (family.exactRateBound base threshold)

end FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound

namespace FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows

def toExactRateBound
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (checked : FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows
      w hw half rate) :
    FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound
      w hw half rate where
  rate_nonnegative := checked.rate_nonnegative
  rate_lt_one := checked.rate_lt_one
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  exactRateBound := by
    intro base threshold
    exact
      (centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_exactRate_le
        checked.rate_nonnegative).mp
        (checked.allRows_checked base threshold)

end FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows

/-! ## 3. The exact cutoff-one check -/

theorem centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_cutoffOne_zero
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck
        w (Q'.le_of_lt hw) 1 0 0 = true := by
  exact
    (centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_exactRate_le
      (Q'.le_refl' 0)).mpr
      (Q'.le_of_eqv
        (centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_cutoffOne_eqv_zero
          hw))

end YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker.centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck_eq_true_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker.centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_rowBounds
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker.centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_exactRate_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker.FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound.toCheckedRows
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker.FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows.toExactRateBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker.centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_cutoffOne_zero
