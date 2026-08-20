/- Generated generic-sector cube trace shard F. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardE

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardF

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardE
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def sectorCubeStep20 : CheckedScopedEliminationStep 2 59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
    sectorCubeFactors20 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 20).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors21 : List ScopedQFactor :=
  sectorCubeStep20.afterFactors

def sectorCubeStep21 : CheckedScopedEliminationStep 2 49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
    sectorCubeFactors21 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 21).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors22 : List ScopedQFactor :=
  sectorCubeStep21.afterFactors

def sectorCubeStep22 : CheckedScopedEliminationStep 2 68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
    sectorCubeFactors22 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 22).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors23 : List ScopedQFactor :=
  sectorCubeStep22.afterFactors

def sectorCubeStep23 : CheckedScopedEliminationStep 2 67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
    sectorCubeFactors23 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 23).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors24 : List ScopedQFactor :=
  sectorCubeStep23.afterFactors

theorem sectorCubeShardF_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        sectorCubeFactors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        sectorCubeFactors24 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
        sectorCubeFactors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep20.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
        sectorCubeFactors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep21.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
        sectorCubeFactors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep22.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        sectorCubeFactors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardF

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardF.sectorCubeShardF_partitionSum_eqv
