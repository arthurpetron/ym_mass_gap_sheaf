/- Structural shared-DAG trace R16C58, shard 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C58Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C58Shard05

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C58Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR16C58Step20 : CheckedScopedEliminationStep 2
    59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
    cutoffTwoSharedDAGTraceR16C58Factors20 where
  bucketResult := cutoffTwoSharedDAGBucket0744Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR16C58Edge20 :
    CheckedReorderedEliminationStep 2 59
      (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
      cutoffTwoSharedDAGTraceR16C58Factors20
      cutoffTwoSharedDAGTraceR16C58Factors21 where
  step := cutoffTwoSharedDAGTraceR16C58Step20
  after_perm := by
    have houtside :
        factorOutside 59
            cutoffTwoSharedDAGTraceR16C58Factors20 =
          cutoffTwoSharedDAGFactorList [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71] := by
      rfl
    have hids : ([598, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71]).Perm [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 598] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR16C58Step20.bucketResult.result ::
        factorOutside 59
          cutoffTwoSharedDAGTraceR16C58Factors20).Perm
        cutoffTwoSharedDAGTraceR16C58Factors21
    rw [houtside]
    change
      (([598, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 598]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR16C58Step21 : CheckedScopedEliminationStep 2
    49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
    cutoffTwoSharedDAGTraceR16C58Factors21 where
  bucketResult := cutoffTwoSharedDAGBucket0745Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR16C58Edge21 :
    CheckedReorderedEliminationStep 2 49
      (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
      cutoffTwoSharedDAGTraceR16C58Factors21
      cutoffTwoSharedDAGTraceR16C58Factors22 where
  step := cutoffTwoSharedDAGTraceR16C58Step21
  after_perm := by
    have houtside :
        factorOutside 49
            cutoffTwoSharedDAGTraceR16C58Factors21 =
          cutoffTwoSharedDAGFactorList [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([599, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 599] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR16C58Step21.bucketResult.result ::
        factorOutside 49
          cutoffTwoSharedDAGTraceR16C58Factors21).Perm
        cutoffTwoSharedDAGTraceR16C58Factors22
    rw [houtside]
    change
      (([599, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 599]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR16C58Step22 : CheckedScopedEliminationStep 2
    68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
    cutoffTwoSharedDAGTraceR16C58Factors22 where
  bucketResult := cutoffTwoSharedDAGBucket0746Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR16C58Edge22 :
    CheckedReorderedEliminationStep 2 68
      (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
      cutoffTwoSharedDAGTraceR16C58Factors22
      cutoffTwoSharedDAGTraceR16C58Factors23 where
  step := cutoffTwoSharedDAGTraceR16C58Step22
  after_perm := by
    have houtside :
        factorOutside 68
            cutoffTwoSharedDAGTraceR16C58Factors22 =
          cutoffTwoSharedDAGFactorList [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([600, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 600] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR16C58Step22.bucketResult.result ::
        factorOutside 68
          cutoffTwoSharedDAGTraceR16C58Factors22).Perm
        cutoffTwoSharedDAGTraceR16C58Factors23
    rw [houtside]
    change
      (([600, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 600]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR16C58Step23 : CheckedScopedEliminationStep 2
    67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
    cutoffTwoSharedDAGTraceR16C58Factors23 where
  bucketResult := cutoffTwoSharedDAGBucket0747Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR16C58Edge23 :
    CheckedReorderedEliminationStep 2 67
      (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
      cutoffTwoSharedDAGTraceR16C58Factors23
      cutoffTwoSharedDAGTraceR16C58Factors24 where
  step := cutoffTwoSharedDAGTraceR16C58Step23
  after_perm := by
    have houtside :
        factorOutside 67
            cutoffTwoSharedDAGTraceR16C58Factors23 =
          cutoffTwoSharedDAGFactorList [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([534, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 534] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR16C58Step23.bucketResult.result ::
        factorOutside 67
          cutoffTwoSharedDAGTraceR16C58Factors23).Perm
        cutoffTwoSharedDAGTraceR16C58Factors24
    rw [houtside]
    change
      (([534, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 534]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR16C58Shard05_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR16C58Factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR16C58Factors24 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
        cutoffTwoSharedDAGTraceR16C58Factors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR16C58Edge20.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
        cutoffTwoSharedDAGTraceR16C58Factors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR16C58Edge21.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
        cutoffTwoSharedDAGTraceR16C58Factors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR16C58Edge22.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR16C58Factors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR16C58Edge23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C58Shard05

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C58Shard05.cutoffTwoSharedDAGTraceR16C58Shard05_partitionSum_eqv
