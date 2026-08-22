/- Structural shared-DAG trace R29C44, shard 4. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR29C44Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR29C44Shard04

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR29C44Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR29C44Step16 : CheckedScopedEliminationStep 2
    11
    (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
    cutoffTwoSharedDAGTraceR29C44Factors16 where
  bucketResult := cutoffTwoSharedDAGBucket1086Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR29C44Edge16 :
    CheckedReorderedEliminationStep 2 11
      (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
      cutoffTwoSharedDAGTraceR29C44Factors16
      cutoffTwoSharedDAGTraceR29C44Factors17 where
  step := cutoffTwoSharedDAGTraceR29C44Step16
  after_perm := by
    have houtside :
        factorOutside 11
            cutoffTwoSharedDAGTraceR29C44Factors16 =
          cutoffTwoSharedDAGFactorList [6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 68, 71, 71, 75, 75] := by
      rfl
    have hids : ([752, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 68, 71, 71, 75, 75]).Perm [6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 68, 71, 71, 75, 75, 752] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR29C44Step16.bucketResult.result ::
        factorOutside 11
          cutoffTwoSharedDAGTraceR29C44Factors16).Perm
        cutoffTwoSharedDAGTraceR29C44Factors17
    rw [houtside]
    change
      (([752, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 68, 71, 71, 75, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 68, 71, 71, 75, 75, 752]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR29C44Step17 : CheckedScopedEliminationStep 2
    20
    (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
    cutoffTwoSharedDAGTraceR29C44Factors17 where
  bucketResult := cutoffTwoSharedDAGBucket1087Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR29C44Edge17 :
    CheckedReorderedEliminationStep 2 20
      (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
      cutoffTwoSharedDAGTraceR29C44Factors17
      cutoffTwoSharedDAGTraceR29C44Factors18 where
  step := cutoffTwoSharedDAGTraceR29C44Step17
  after_perm := by
    have houtside :
        factorOutside 20
            cutoffTwoSharedDAGTraceR29C44Factors17 =
          cutoffTwoSharedDAGFactorList [9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75] := by
      rfl
    have hids : ([753, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75]).Perm [9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75, 753] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR29C44Step17.bucketResult.result ::
        factorOutside 20
          cutoffTwoSharedDAGTraceR29C44Factors17).Perm
        cutoffTwoSharedDAGTraceR29C44Factors18
    rw [houtside]
    change
      (([753, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75, 753]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR29C44Step18 : CheckedScopedEliminationStep 2
    65
    (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
    cutoffTwoSharedDAGTraceR29C44Factors18 where
  bucketResult := cutoffTwoSharedDAGBucket0018Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR29C44Edge18 :
    CheckedReorderedEliminationStep 2 65
      (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
      cutoffTwoSharedDAGTraceR29C44Factors18
      cutoffTwoSharedDAGTraceR29C44Factors19 where
  step := cutoffTwoSharedDAGTraceR29C44Step18
  after_perm := by
    have houtside :
        factorOutside 65
            cutoffTwoSharedDAGTraceR29C44Factors18 =
          cutoffTwoSharedDAGFactorList [9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75, 753] := by
      rfl
    have hids : ([99, 9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75, 753]).Perm [9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75, 99, 753] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR29C44Step18.bucketResult.result ::
        factorOutside 65
          cutoffTwoSharedDAGTraceR29C44Factors18).Perm
        cutoffTwoSharedDAGTraceR29C44Factors19
    rw [houtside]
    change
      (([99, 9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75, 753]).map cutoffTwoSharedDAGFactor).Perm
        (([9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 75, 75, 99, 753]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR29C44Step19 : CheckedScopedEliminationStep 2
    29
    (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
    cutoffTwoSharedDAGTraceR29C44Factors19 where
  bucketResult := cutoffTwoSharedDAGBucket1088Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR29C44Edge19 :
    CheckedReorderedEliminationStep 2 29
      (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
      cutoffTwoSharedDAGTraceR29C44Factors19
      cutoffTwoSharedDAGTraceR29C44Factors20 where
  step := cutoffTwoSharedDAGTraceR29C44Step19
  after_perm := by
    have houtside :
        factorOutside 29
            cutoffTwoSharedDAGTraceR29C44Factors19 =
          cutoffTwoSharedDAGFactorList [16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71] := by
      rfl
    have hids : ([754, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71]).Perm [16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 754] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR29C44Step19.bucketResult.result ::
        factorOutside 29
          cutoffTwoSharedDAGTraceR29C44Factors19).Perm
        cutoffTwoSharedDAGTraceR29C44Factors20
    rw [houtside]
    change
      (([754, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 71, 71, 754]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR29C44Shard04_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR29C44Factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR29C44Factors20 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
        cutoffTwoSharedDAGTraceR29C44Factors17 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR29C44Edge16.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
        cutoffTwoSharedDAGTraceR29C44Factors18 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR29C44Edge17.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
        cutoffTwoSharedDAGTraceR29C44Factors19 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR29C44Edge18.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR29C44Factors20 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR29C44Edge19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR29C44Shard04

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR29C44Shard04.cutoffTwoSharedDAGTraceR29C44Shard04_partitionSum_eqv
