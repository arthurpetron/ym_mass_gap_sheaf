/-
# Quantitative OLD quartic-center mismatch budget

Changing only the supplied OLD quartic coefficient by `delta` changes the
residual-free neighboring frontier by exactly `-delta` times the OLD-even
bracket.  This leaf turns that identity into the absolute payment

  `abs(frontier_shifted-frontier) <= abs(delta)*abs(B_even)`

and composes it with the existing Heron approximation error.  A base-center
negative margin exceeding both payments therefore forces the actual cleared
numerator for the shifted center to be negative.

This is the exact consumer for a future ORIGINAL-to-reference `c4` comparison.
It assumes `c2,c3` are unchanged, supplies no such comparison, proves no
bracket bound or margin, and establishes no continuum Hamiltonian or Clay
mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSensitivity
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticMismatchBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSensitivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer

local infix:50 " ≈ " => Q'.eqv

private theorem value_le_reference_add_error
    (value reference error : Q')
    (herror : Q'.abs (value - reference) ≤ error) :
    value ≤ reference + error := by
  have hdifference : value - reference ≤ error :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (value - reference)) herror
  have hadd := Q'.add_le_add
    (Q'.le_refl' reference) hdifference
  have hrewrite : value ≈ reference + (value - reference) :=
    poly_identity_of_normal_eq
      (.var 0)
      (.add (.var 1)
        (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun
        | 0 => value
        | _ => reference)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) hadd

/-- Exact difference caused by changing only the supplied OLD quartic
coefficient. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4_sub
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldQuarticCenter oldCenter delta) -
        openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter ≈
      (-delta) *
        openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
          timeBonds side sidePositive stage baseTime lag oldCenter := by
  let frontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  have hsensitivity :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  change
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldQuarticCenter oldCenter delta) - frontier ≈
      (-delta) * bracket
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hsensitivity (Q'.eqv_refl (-frontier))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
      (.neg (.var 0)))
    (.mul (.neg (.var 1)) (.var 2))
    (by decide) (fun
      | 0 => frontier
      | 1 => delta
      | _ => bracket)

/-- The exact quartic-center sensitivity gives its canonical absolute
payment. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4_abs_le
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    Q'.abs
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
              timeBonds side sidePositive stage baseTime lag
              (shiftOldQuarticCenter oldCenter delta) -
          openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
            timeBonds side sidePositive stage baseTime lag oldCenter) ≤
      Q'.abs delta *
        Q'.abs
          (openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter) := by
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4_sub
          timeBonds side sidePositive stage baseTime lag oldCenter delta))) ?_
  refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le (-delta) bracket) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_right _ _ _ (Q'.abs_neg' delta))

/-- A base-center margin which pays both the quartic-center mismatch and the
Heron approximation tail transfers to the actual cleared numerator for the
shifted center. -/
theorem openCubeHeatCayleyTraceP6NeighboringClearedComparison_shift_c4_lt_zero_of_margin
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta centerError epsilon : Q')
    (hepsilon : (0 : Q') < epsilon)
    (hcenter :
      Q'.abs delta *
          Q'.abs
            (openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
              timeBonds side sidePositive stage baseTime lag oldCenter) ≤
        centerError)
    (hstage :
      bulkSourceHeatP6NeighboringClearedAdaptiveStage
          timeBonds side sidePositive baseTime lag
          (shiftOldQuarticCenter oldCenter delta) epsilon ≤ stage)
    (hmargin :
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
            timeBonds side sidePositive stage baseTime lag oldCenter +
          (centerError + epsilon) < 0) :
    openCubeHeatCayleyTraceP6NeighboringClearedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuarticCenter oldCenter delta) < 0 := by
  let baseFrontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let shiftedFrontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag
      (shiftOldQuarticCenter oldCenter delta)
  have habsolute : Q'.abs (shiftedFrontier - baseFrontier) ≤ centerError :=
    Q'.le_trans' _ _ _
      (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4_abs_le
        timeBonds side sidePositive stage baseTime lag oldCenter delta)
      hcenter
  have hfrontier : shiftedFrontier ≤ baseFrontier + centerError :=
    value_le_reference_add_error shiftedFrontier baseFrontier centerError habsolute
  have hadd : shiftedFrontier + epsilon ≤
      (baseFrontier + centerError) + epsilon :=
    Q'.add_le_add_right _ _ epsilon hfrontier
  have hreassociate :
      (baseFrontier + centerError) + epsilon ≈
        baseFrontier + (centerError + epsilon) :=
    Q'.add_assoc_eqv baseFrontier centerError epsilon
  have hshiftedMargin : shiftedFrontier + epsilon < 0 :=
    Q'.lt_of_le_of_lt
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreassociate)) hmargin
  exact
    openCubeHeatCayleyTraceP6NeighboringClearedComparison_lt_zero_of_residualFree_margin
      timeBonds side sidePositive stage baseTime lag
      (shiftOldQuarticCenter oldCenter delta)
      epsilon hepsilon hstage hshiftedMargin

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticMismatchBudget

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4_sub
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4_abs_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringClearedComparison_shift_c4_lt_zero_of_margin
