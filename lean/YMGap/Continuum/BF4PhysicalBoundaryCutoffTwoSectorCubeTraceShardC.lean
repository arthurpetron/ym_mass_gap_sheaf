/- Generated generic-sector cube trace shard C. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardB

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardC

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardB
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def sectorCubeStep8 : CheckedScopedEliminationStep 2 23
    (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
    sectorCubeFactors8 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 8).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors9 : List ScopedQFactor :=
  sectorCubeStep8.afterFactors

def sectorCubeStep9 : CheckedScopedEliminationStep 2 40
    (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
    sectorCubeFactors9 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 9).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors10 : List ScopedQFactor :=
  sectorCubeStep9.afterFactors

def sectorCubeStep10 : CheckedScopedEliminationStep 2 47
    (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
    sectorCubeFactors10 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 10).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors11 : List ScopedQFactor :=
  sectorCubeStep10.afterFactors

def sectorCubeStep11 : CheckedScopedEliminationStep 2 50
    (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
    sectorCubeFactors11 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 11).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors12 : List ScopedQFactor :=
  sectorCubeStep11.afterFactors

theorem sectorCubeShardC_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        sectorCubeFactors8 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        sectorCubeFactors12 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
        sectorCubeFactors9 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep8.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
        sectorCubeFactors10 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep9.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
        sectorCubeFactors11 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep10.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        sectorCubeFactors12 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardC

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardC.sectorCubeShardC_partitionSum_eqv
