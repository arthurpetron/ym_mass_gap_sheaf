/- Structural shared-DAG trace R12C55, shard 4. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C55Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C55Shard04

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C55Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR12C55Step16 : CheckedScopedEliminationStep 2
    11
    (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
    cutoffTwoSharedDAGTraceR12C55Factors16 where
  bucketResult := cutoffTwoSharedDAGBucket0105Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C55Edge16 :
    CheckedReorderedEliminationStep 2 11
      (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
      cutoffTwoSharedDAGTraceR12C55Factors16
      cutoffTwoSharedDAGTraceR12C55Factors17 where
  step := cutoffTwoSharedDAGTraceR12C55Step16
  after_perm := by
    have houtside :
        factorOutside 11
            cutoffTwoSharedDAGTraceR12C55Factors16 =
          cutoffTwoSharedDAGFactorList [6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 73, 75] := by
      rfl
    have hids : ([179, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 73, 75]).Perm [6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 73, 75, 179] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C55Step16.bucketResult.result ::
        factorOutside 11
          cutoffTwoSharedDAGTraceR12C55Factors16).Perm
        cutoffTwoSharedDAGTraceR12C55Factors17
    rw [houtside]
    change
      (([179, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 73, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 73, 75, 179]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C55Step17 : CheckedScopedEliminationStep 2
    20
    (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
    cutoffTwoSharedDAGTraceR12C55Factors17 where
  bucketResult := cutoffTwoSharedDAGBucket0612Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C55Edge17 :
    CheckedReorderedEliminationStep 2 20
      (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
      cutoffTwoSharedDAGTraceR12C55Factors17
      cutoffTwoSharedDAGTraceR12C55Factors18 where
  step := cutoffTwoSharedDAGTraceR12C55Step17
  after_perm := by
    have houtside :
        factorOutside 20
            cutoffTwoSharedDAGTraceR12C55Factors17 =
          cutoffTwoSharedDAGFactorList [9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75] := by
      rfl
    have hids : ([529, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75]).Perm [9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75, 529] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C55Step17.bucketResult.result ::
        factorOutside 20
          cutoffTwoSharedDAGTraceR12C55Factors17).Perm
        cutoffTwoSharedDAGTraceR12C55Factors18
    rw [houtside]
    change
      (([529, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75, 529]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C55Step18 : CheckedScopedEliminationStep 2
    65
    (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
    cutoffTwoSharedDAGTraceR12C55Factors18 where
  bucketResult := cutoffTwoSharedDAGBucket0018Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C55Edge18 :
    CheckedReorderedEliminationStep 2 65
      (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
      cutoffTwoSharedDAGTraceR12C55Factors18
      cutoffTwoSharedDAGTraceR12C55Factors19 where
  step := cutoffTwoSharedDAGTraceR12C55Step18
  after_perm := by
    have houtside :
        factorOutside 65
            cutoffTwoSharedDAGTraceR12C55Factors18 =
          cutoffTwoSharedDAGFactorList [9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75, 529] := by
      rfl
    have hids : ([99, 9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75, 529]).Perm [9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75, 99, 529] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C55Step18.bucketResult.result ::
        factorOutside 65
          cutoffTwoSharedDAGTraceR12C55Factors18).Perm
        cutoffTwoSharedDAGTraceR12C55Factors19
    rw [houtside]
    change
      (([99, 9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75, 529]).map cutoffTwoSharedDAGFactor).Perm
        (([9, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 75, 99, 529]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C55Step19 : CheckedScopedEliminationStep 2
    29
    (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
    cutoffTwoSharedDAGTraceR12C55Factors19 where
  bucketResult := cutoffTwoSharedDAGBucket0613Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C55Edge19 :
    CheckedReorderedEliminationStep 2 29
      (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
      cutoffTwoSharedDAGTraceR12C55Factors19
      cutoffTwoSharedDAGTraceR12C55Factors20 where
  step := cutoffTwoSharedDAGTraceR12C55Step19
  after_perm := by
    have houtside :
        factorOutside 29
            cutoffTwoSharedDAGTraceR12C55Factors19 =
          cutoffTwoSharedDAGFactorList [16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72] := by
      rfl
    have hids : ([530, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72]).Perm [16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 530] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C55Step19.bucketResult.result ::
        factorOutside 29
          cutoffTwoSharedDAGTraceR12C55Factors19).Perm
        cutoffTwoSharedDAGTraceR12C55Factors20
    rw [houtside]
    change
      (([530, 16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 20, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 71, 71, 72, 530]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR12C55Shard04_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR12C55Factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR12C55Factors20 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
        cutoffTwoSharedDAGTraceR12C55Factors17 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C55Edge16.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
        cutoffTwoSharedDAGTraceR12C55Factors18 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C55Edge17.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
        cutoffTwoSharedDAGTraceR12C55Factors19 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C55Edge18.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR12C55Factors20 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C55Edge19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C55Shard04

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C55Shard04.cutoffTwoSharedDAGTraceR12C55Shard04_partitionSum_eqv
