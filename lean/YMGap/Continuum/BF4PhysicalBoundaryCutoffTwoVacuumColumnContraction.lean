/-
# Exact retained cutoff-two BF4 vacuum-column contraction

The full-carrier sparse contraction and the generic vacuum-column support
theorem combine here to evaluate the genuine retained positive-source BF4
boundary column at cutoff two, half-extent zero, and coupling one half.

This is one finite-volume exact statistic.  It makes no cutoff-uniform,
volume-uniform, spectral-gap, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction
import YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

/-- The genuine retained physical cutoff-two vacuum column has the exact
kernel-checked rational value emitted by the sparse certificate producer. -/
theorem centralBoundaryColumnMass_cutoffTwo_vacuum_eqv_expected :
    centralBoundaryColumnMass cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling ≈
      cutoffTwoVacuumExpectedScalar := by
  exact Q'.eqv_trans _ cutoffTwoVacuumFullColumnMass _
    (centralBoundaryColumnMass_vacuum_eqv_full
      cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0)
    cutoffTwoVacuumFullColumnMass_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction.centralBoundaryColumnMass_cutoffTwo_vacuum_eqv_expected
