/-
# Positive fundamental-cube star in the cutoff-two production kernel

This module is the expression-size boundary between the complete shared-DAG
physical-table certificate and the later graph argument.  It transports the
isolated positive raw row zero to the genuine production reflected kernel and
also records the positive vacuum-to-cube edge.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSectorStateAt_zero_eq_cube :
    cutoffTwoSectorStateAt 0 = centralLowerCubeState :=
  cutoffTwoSectorStateAt_zero_eq_cube_sealed

theorem centralPhysicalReflectedKernel_cutoffTwo_stateAt_zero_sectorStateAt_pos
    {column : Nat} (hcolumn : column < 65) :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt 0) (cutoffTwoSectorStateAt column) :=
  cutoffTwoSectorPhysicalTableCertificateSealed_rowZero_pos hcolumn

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar.centralPhysicalReflectedKernel_cutoffTwo_stateAt_zero_sectorStateAt_pos
