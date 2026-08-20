/-
# Exact cutoff-two vacuum-column posterior denominator core

This small interface transports the kernel-checked cutoff-two column value to
the total-amplitude name used by the physical posterior layer.

This is finite `K = 2`, half-extent-zero data at coupling `1/2`; it is not a
spectral-gap or continuum claim.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation
import YMGap.Continuum.BF4PhysicalBoundaryPosterior

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The exact physical mass of the retained cutoff-two vacuum column. -/
def cutoffTwoVacuumColumnDenominator : Q' :=
  cutoffTwoVacuumExpectedScalar

theorem cutoffTwoVacuumColumnDenominator_pos :
    (0 : Q') < cutoffTwoVacuumColumnDenominator := by
  unfold cutoffTwoVacuumColumnDenominator cutoffTwoVacuumExpectedScalar
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior
