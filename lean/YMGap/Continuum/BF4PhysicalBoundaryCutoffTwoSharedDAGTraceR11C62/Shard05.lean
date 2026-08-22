/- Structural shared-DAG trace R11C62, shard 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Shard05

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR11C62Step20 : CheckedScopedEliminationStep 2
    59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
    cutoffTwoSharedDAGTraceR11C62Factors20 where
  bucketResult := cutoffTwoSharedDAGBucket0598Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR11C62Edge20 :
    CheckedReorderedEliminationStep 2 59
      (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
      cutoffTwoSharedDAGTraceR11C62Factors20
      cutoffTwoSharedDAGTraceR11C62Factors21 where
  step := cutoffTwoSharedDAGTraceR11C62Step20
  after_perm := by
    have houtside :
        factorOutside 59
            cutoffTwoSharedDAGTraceR11C62Factors20 =
          cutoffTwoSharedDAGFactorList [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 67] := by
      rfl
    have hids : ([521, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 67]).Perm [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 67, 521] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR11C62Step20.bucketResult.result ::
        factorOutside 59
          cutoffTwoSharedDAGTraceR11C62Factors20).Perm
        cutoffTwoSharedDAGTraceR11C62Factors21
    rw [houtside]
    change
      (([521, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 67]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 67, 521]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR11C62Step21 : CheckedScopedEliminationStep 2
    49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
    cutoffTwoSharedDAGTraceR11C62Factors21 where
  bucketResult := cutoffTwoSharedDAGBucket0593Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR11C62Edge21 :
    CheckedReorderedEliminationStep 2 49
      (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
      cutoffTwoSharedDAGTraceR11C62Factors21
      cutoffTwoSharedDAGTraceR11C62Factors22 where
  step := cutoffTwoSharedDAGTraceR11C62Step21
  after_perm := by
    have houtside :
        factorOutside 49
            cutoffTwoSharedDAGTraceR11C62Factors21 =
          cutoffTwoSharedDAGFactorList [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([522, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 522] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR11C62Step21.bucketResult.result ::
        factorOutside 49
          cutoffTwoSharedDAGTraceR11C62Factors21).Perm
        cutoffTwoSharedDAGTraceR11C62Factors22
    rw [houtside]
    change
      (([522, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 522]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR11C62Step22 : CheckedScopedEliminationStep 2
    68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
    cutoffTwoSharedDAGTraceR11C62Factors22 where
  bucketResult := cutoffTwoSharedDAGBucket0594Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR11C62Edge22 :
    CheckedReorderedEliminationStep 2 68
      (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
      cutoffTwoSharedDAGTraceR11C62Factors22
      cutoffTwoSharedDAGTraceR11C62Factors23 where
  step := cutoffTwoSharedDAGTraceR11C62Step22
  after_perm := by
    have houtside :
        factorOutside 68
            cutoffTwoSharedDAGTraceR11C62Factors22 =
          cutoffTwoSharedDAGFactorList [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([523, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 523] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR11C62Step22.bucketResult.result ::
        factorOutside 68
          cutoffTwoSharedDAGTraceR11C62Factors22).Perm
        cutoffTwoSharedDAGTraceR11C62Factors23
    rw [houtside]
    change
      (([523, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 523]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR11C62Step23 : CheckedScopedEliminationStep 2
    67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
    cutoffTwoSharedDAGTraceR11C62Factors23 where
  bucketResult := cutoffTwoSharedDAGBucket0595Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR11C62Edge23 :
    CheckedReorderedEliminationStep 2 67
      (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
      cutoffTwoSharedDAGTraceR11C62Factors23
      cutoffTwoSharedDAGTraceR11C62Factors24 where
  step := cutoffTwoSharedDAGTraceR11C62Step23
  after_perm := by
    have houtside :
        factorOutside 67
            cutoffTwoSharedDAGTraceR11C62Factors23 =
          cutoffTwoSharedDAGFactorList [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([501, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 501] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR11C62Step23.bucketResult.result ::
        factorOutside 67
          cutoffTwoSharedDAGTraceR11C62Factors23).Perm
        cutoffTwoSharedDAGTraceR11C62Factors24
    rw [houtside]
    change
      (([501, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 501]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR11C62Shard05_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR11C62Factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR11C62Factors24 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
        cutoffTwoSharedDAGTraceR11C62Factors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR11C62Edge20.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
        cutoffTwoSharedDAGTraceR11C62Factors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR11C62Edge21.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
        cutoffTwoSharedDAGTraceR11C62Factors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR11C62Edge22.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR11C62Factors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR11C62Edge23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Shard05

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Shard05.cutoffTwoSharedDAGTraceR11C62Shard05_partitionSum_eqv
