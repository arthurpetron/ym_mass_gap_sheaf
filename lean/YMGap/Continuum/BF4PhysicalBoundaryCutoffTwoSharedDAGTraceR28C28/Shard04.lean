/- Structural shared-DAG trace R28C28, shard 4. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C28Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C28Shard04

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C28Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR28C28Step16 : CheckedScopedEliminationStep 2
    11
    (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
    cutoffTwoSharedDAGTraceR28C28Factors16 where
  bucketResult := cutoffTwoSharedDAGBucket1007Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C28Edge16 :
    CheckedReorderedEliminationStep 2 11
      (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
      cutoffTwoSharedDAGTraceR28C28Factors16
      cutoffTwoSharedDAGTraceR28C28Factors17 where
  step := cutoffTwoSharedDAGTraceR28C28Step16
  after_perm := by
    have houtside :
        factorOutside 11
            cutoffTwoSharedDAGTraceR28C28Factors16 =
          cutoffTwoSharedDAGFactorList [6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 73, 73, 75, 75] := by
      rfl
    have hids : ([303, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 73, 73, 75, 75]).Perm [6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 73, 73, 75, 75, 303] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C28Step16.bucketResult.result ::
        factorOutside 11
          cutoffTwoSharedDAGTraceR28C28Factors16).Perm
        cutoffTwoSharedDAGTraceR28C28Factors17
    rw [houtside]
    change
      (([303, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 73, 73, 75, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 73, 73, 75, 75, 303]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR28C28Step17 : CheckedScopedEliminationStep 2
    20
    (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
    cutoffTwoSharedDAGTraceR28C28Factors17 where
  bucketResult := cutoffTwoSharedDAGBucket1008Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C28Edge17 :
    CheckedReorderedEliminationStep 2 20
      (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
      cutoffTwoSharedDAGTraceR28C28Factors17
      cutoffTwoSharedDAGTraceR28C28Factors18 where
  step := cutoffTwoSharedDAGTraceR28C28Step17
  after_perm := by
    have houtside :
        factorOutside 20
            cutoffTwoSharedDAGTraceR28C28Factors17 =
          cutoffTwoSharedDAGFactorList [9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75] := by
      rfl
    have hids : ([304, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75]).Perm [9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75, 304] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C28Step17.bucketResult.result ::
        factorOutside 20
          cutoffTwoSharedDAGTraceR28C28Factors17).Perm
        cutoffTwoSharedDAGTraceR28C28Factors18
    rw [houtside]
    change
      (([304, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75, 304]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR28C28Step18 : CheckedScopedEliminationStep 2
    65
    (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
    cutoffTwoSharedDAGTraceR28C28Factors18 where
  bucketResult := cutoffTwoSharedDAGBucket0018Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C28Edge18 :
    CheckedReorderedEliminationStep 2 65
      (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
      cutoffTwoSharedDAGTraceR28C28Factors18
      cutoffTwoSharedDAGTraceR28C28Factors19 where
  step := cutoffTwoSharedDAGTraceR28C28Step18
  after_perm := by
    have houtside :
        factorOutside 65
            cutoffTwoSharedDAGTraceR28C28Factors18 =
          cutoffTwoSharedDAGFactorList [9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75, 304] := by
      rfl
    have hids : ([99, 9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75, 304]).Perm [9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75, 99, 304] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C28Step18.bucketResult.result ::
        factorOutside 65
          cutoffTwoSharedDAGTraceR28C28Factors18).Perm
        cutoffTwoSharedDAGTraceR28C28Factors19
    rw [houtside]
    change
      (([99, 9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75, 304]).map cutoffTwoSharedDAGFactor).Perm
        (([9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 75, 75, 99, 304]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR28C28Step19 : CheckedScopedEliminationStep 2
    29
    (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
    cutoffTwoSharedDAGTraceR28C28Factors19 where
  bucketResult := cutoffTwoSharedDAGBucket1009Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C28Edge19 :
    CheckedReorderedEliminationStep 2 29
      (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
      cutoffTwoSharedDAGTraceR28C28Factors19
      cutoffTwoSharedDAGTraceR28C28Factors20 where
  step := cutoffTwoSharedDAGTraceR28C28Step19
  after_perm := by
    have houtside :
        factorOutside 29
            cutoffTwoSharedDAGTraceR28C28Factors19 =
          cutoffTwoSharedDAGFactorList [16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71] := by
      rfl
    have hids : ([305, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71]).Perm [16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 305] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C28Step19.bucketResult.result ::
        factorOutside 29
          cutoffTwoSharedDAGTraceR28C28Factors19).Perm
        cutoffTwoSharedDAGTraceR28C28Factors20
    rw [houtside]
    change
      (([305, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 71, 71, 305]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR28C28Shard04_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR28C28Factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR28C28Factors20 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
        cutoffTwoSharedDAGTraceR28C28Factors17 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C28Edge16.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
        cutoffTwoSharedDAGTraceR28C28Factors18 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C28Edge17.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
        cutoffTwoSharedDAGTraceR28C28Factors19 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C28Edge18.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR28C28Factors20 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C28Edge19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C28Shard04

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C28Shard04.cutoffTwoSharedDAGTraceR28C28Shard04_partitionSum_eqv
