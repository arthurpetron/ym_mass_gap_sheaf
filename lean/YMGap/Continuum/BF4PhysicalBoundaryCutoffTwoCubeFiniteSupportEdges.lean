/-
# Cutoff-two table-star edges on the indexed physical carrier

This module specializes the generic physical support bridge once: whenever a
positive-carrier index represents table state zero and another represents an
in-range table column, the exact production-kernel row-zero star supplies a
Boolean support edge between those indices.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector

/-- The production row-zero star transported to arbitrary indexed
positive-carrier representatives of its table endpoints. -/
theorem cutoffTwoTableHub_supportEdge
    {tableColumn hubIndex columnIndex : Nat}
    (htableColumn : tableColumn < 65)
    (hhub : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 hubIndex = cutoffTwoSectorStateAt 0)
    (hcolumn : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 columnIndex = cutoffTwoSectorStateAt tableColumn) :
    centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
      (by decide) 2 0 hubIndex columnIndex = true :=
  centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
    cutoffTwoHalfCoupling (by decide) 2 0 hhub hcolumn
    (centralPhysicalReflectedKernel_cutoffTwo_stateAt_zero_sectorStateAt_pos
      htableColumn)

/-- Reversed orientation of the same support edge, cached so later proofs do
not specialize Boolean support symmetry at the concrete carrier. -/
theorem cutoffTwoTableHub_supportEdge_reverse
    {tableColumn hubIndex columnIndex : Nat}
    (htableColumn : tableColumn < 65)
    (hhub : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 hubIndex = cutoffTwoSectorStateAt 0)
    (hcolumn : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 columnIndex = cutoffTwoSectorStateAt tableColumn) :
    centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
      (by decide) 2 0 columnIndex hubIndex = true :=
  centralPhysicalFiniteSupportAdjacentB_reverse_true_of_kernel_pos
    cutoffTwoHalfCoupling (by decide) 2 0 hhub hcolumn
    (centralPhysicalReflectedKernel_cutoffTwo_stateAt_zero_sectorStateAt_pos
      htableColumn)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges.cutoffTwoTableHub_supportEdge
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges.cutoffTwoTableHub_supportEdge_reverse
