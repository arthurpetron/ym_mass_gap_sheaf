/-
# First generic-sector elimination step, specialized to cube/cube

This module tests reuse of the independently generated cube sparse trace
against the new 140-factor graph whose state-dependent factors are the genuine
production lower-link multiplicities.  Passing this step checks that the first
external sparse table is not tied merely to the earlier folded cube surrogate.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def sectorCubeFactors0 : List ScopedQFactor :=
  cutoffTwoSectorPairInterfaceFactors
    centralLowerCubeState centralLowerCubeState

def sectorCubeStep0 : CheckedScopedEliminationStep 2 38
    (cutoffTwoCubeInterfaceEliminationOrder.drop 1)
    sectorCubeFactors0 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 0).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

theorem sectorCubeStep0_partitionSum_eqv :
    scopedFactorPartitionSum 2
        cutoffTwoCubeInterfaceEliminationOrder sectorCubeFactors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 1)
        sectorCubeStep0.afterFactors := by
  simpa [cutoffTwoCubeInterfaceEliminationOrder] using
    sectorCubeStep0.partitionSum_eqv_after

def sectorCubeFactors1 : List ScopedQFactor := sectorCubeStep0.afterFactors

def sectorCubeStep1 : CheckedScopedEliminationStep 2 22
    (cutoffTwoCubeInterfaceEliminationOrder.drop 2)
    sectorCubeFactors1 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 1).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors2 : List ScopedQFactor := sectorCubeStep1.afterFactors

def sectorCubeStep2 : CheckedScopedEliminationStep 2 14
    (cutoffTwoCubeInterfaceEliminationOrder.drop 3)
    sectorCubeFactors2 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 2).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors3 : List ScopedQFactor := sectorCubeStep2.afterFactors

def sectorCubeStep3 : CheckedScopedEliminationStep 2 5
    (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
    sectorCubeFactors3 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 3).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors4 : List ScopedQFactor := sectorCubeStep3.afterFactors

theorem sectorCubeShardA_partitionSum_eqv :
    scopedFactorPartitionSum 2
        cutoffTwoCubeInterfaceEliminationOrder sectorCubeFactors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        sectorCubeFactors4 := by
  exact Q'.eqv_trans _ _ _ sectorCubeStep0_partitionSum_eqv
    (Q'.eqv_trans _ _ _
      (by simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep1.partitionSum_eqv_after)
      (Q'.eqv_trans _ _ _
        (by simpa [cutoffTwoCubeInterfaceEliminationOrder] using
          sectorCubeStep2.partitionSum_eqv_after)
        (by simpa [cutoffTwoCubeInterfaceEliminationOrder] using
          sectorCubeStep3.partitionSum_eqv_after)))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0.sectorCubeStep0_partitionSum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0.sectorCubeShardA_partitionSum_eqv
