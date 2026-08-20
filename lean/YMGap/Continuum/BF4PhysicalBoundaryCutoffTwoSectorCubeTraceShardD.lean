/- Generated generic-sector cube trace shard D. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardC

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardD

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardC
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def sectorCubeStep12 : CheckedScopedEliminationStep 2 13
    (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
    sectorCubeFactors12 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 12).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors13 : List ScopedQFactor :=
  sectorCubeStep12.afterFactors

def sectorCubeStep13 : CheckedScopedEliminationStep 2 4
    (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
    sectorCubeFactors13 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 13).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors14 : List ScopedQFactor :=
  sectorCubeStep13.afterFactors

def sectorCubeStep14 : CheckedScopedEliminationStep 2 41
    (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
    sectorCubeFactors14 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 14).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors15 : List ScopedQFactor :=
  sectorCubeStep14.afterFactors

def sectorCubeStep15 : CheckedScopedEliminationStep 2 2
    (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
    sectorCubeFactors15 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 15).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors16 : List ScopedQFactor :=
  sectorCubeStep15.afterFactors

theorem sectorCubeShardD_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        sectorCubeFactors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        sectorCubeFactors16 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
        sectorCubeFactors13 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep12.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
        sectorCubeFactors14 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep13.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
        sectorCubeFactors15 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep14.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        sectorCubeFactors16 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardD

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardD.sectorCubeShardD_partitionSum_eqv
