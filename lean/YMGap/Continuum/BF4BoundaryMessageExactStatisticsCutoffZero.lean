/-
# Genuine BF4 exact-statistics certificate at cutoff zero

At cutoff zero the literal retained BF4 source carrier and boundary carrier
each contain only the vacuum labelling.  This file evaluates the actual
physical half-amplitude statistic, rather than a separately supplied matrix.
The unique row is exactly rank one, so both its regularized projection defect
and its exact residual-and-bias maximum vanish.

This is a genuine but degenerate finite-regulator checkpoint.  It supplies no
positive-cutoff estimate and no all-cutoff tail theorem.
-/

import YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics

namespace YMGap.Continuum.BF4BoundaryMessageExactStatisticsCutoffZero

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def cutoffZeroWeight : Q' := 1

theorem cutoffZeroWeight_nonnegative :
    (0 : Q') ≤ cutoffZeroWeight := by
  decide

def cutoffZeroPseudocount : Q' := 1

theorem cutoffZeroPseudocount_pos :
    (0 : Q') < cutoffZeroPseudocount := by
  decide

/-- The actual BF4 exact residual-and-bias maximum vanishes on the unique
cutoff-zero source-by-boundary coordinate. -/
theorem cutoffZeroExactStatisticalMax_eqv_zero :
    centralBoundaryExactStatisticalRankOneMaxBudget
        cutoffZeroWeight cutoffZeroWeight_nonnegative
        0 0 cutoffZeroPseudocount cutoffZeroPseudocount_pos ≈
      0 := by
  decide

/-- The corresponding actual BF4 regularized rank-one defect vanishes at the
vacuum coordinate. -/
theorem cutoffZeroDefect_eqv_zero :
    centralHalfAmplitudeRegularizedRankOneDefect
        cutoffZeroWeight cutoffZeroWeight_nonnegative
        0 0 cutoffZeroPseudocount cutoffZeroPseudocount_pos
        zeroEdgeLabelling zeroEdgeLabelling ≈
      0 := by
  decide

end YMGap.Continuum.BF4BoundaryMessageExactStatisticsCutoffZero

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4BoundaryMessageExactStatisticsCutoffZero.cutoffZeroExactStatisticalMax_eqv_zero
#print axioms YMGap.Continuum.BF4BoundaryMessageExactStatisticsCutoffZero.cutoffZeroDefect_eqv_zero
