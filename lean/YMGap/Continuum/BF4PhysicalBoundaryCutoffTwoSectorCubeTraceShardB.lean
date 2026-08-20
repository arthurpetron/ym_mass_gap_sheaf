/- Generated generic-sector cube trace shard B. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardB

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def sectorCubeStep4 : CheckedScopedEliminationStep 2 31
    (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
    sectorCubeFactors4 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 4).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors5 : List ScopedQFactor :=
  sectorCubeStep4.afterFactors

def sectorCubeStep5 : CheckedScopedEliminationStep 2 32
    (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
    sectorCubeFactors5 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 5).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors6 : List ScopedQFactor :=
  sectorCubeStep5.afterFactors

def sectorCubeStep6 : CheckedScopedEliminationStep 2 56
    (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
    sectorCubeFactors6 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 6).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors7 : List ScopedQFactor :=
  sectorCubeStep6.afterFactors

def sectorCubeStep7 : CheckedScopedEliminationStep 2 58
    (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
    sectorCubeFactors7 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 7).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors8 : List ScopedQFactor :=
  sectorCubeStep7.afterFactors

theorem sectorCubeShardB_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        sectorCubeFactors4 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        sectorCubeFactors8 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
        sectorCubeFactors5 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep4.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
        sectorCubeFactors6 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep5.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
        sectorCubeFactors7 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep6.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        sectorCubeFactors8 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep7.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardB

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardB.sectorCubeShardB_partitionSum_eqv
