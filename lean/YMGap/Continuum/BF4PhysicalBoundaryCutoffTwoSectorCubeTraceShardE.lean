/- Generated generic-sector cube trace shard E. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardD

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardE

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardD
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def sectorCubeStep16 : CheckedScopedEliminationStep 2 11
    (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
    sectorCubeFactors16 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 16).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors17 : List ScopedQFactor :=
  sectorCubeStep16.afterFactors

def sectorCubeStep17 : CheckedScopedEliminationStep 2 20
    (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
    sectorCubeFactors17 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 17).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors18 : List ScopedQFactor :=
  sectorCubeStep17.afterFactors

def sectorCubeStep18 : CheckedScopedEliminationStep 2 65
    (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
    sectorCubeFactors18 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 18).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors19 : List ScopedQFactor :=
  sectorCubeStep18.afterFactors

def sectorCubeStep19 : CheckedScopedEliminationStep 2 29
    (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
    sectorCubeFactors19 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 19).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sectorCubeFactors20 : List ScopedQFactor :=
  sectorCubeStep19.afterFactors

theorem sectorCubeShardE_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        sectorCubeFactors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        sectorCubeFactors20 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
        sectorCubeFactors17 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep16.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
        sectorCubeFactors18 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep17.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
        sectorCubeFactors19 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep18.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        sectorCubeFactors20 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardE

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardE.sectorCubeShardE_partitionSum_eqv
