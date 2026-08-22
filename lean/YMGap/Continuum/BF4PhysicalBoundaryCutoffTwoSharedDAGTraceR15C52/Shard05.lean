/- Structural shared-DAG trace R15C52, shard 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR15C52Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR15C52Shard05

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR15C52Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR15C52Step20 : CheckedScopedEliminationStep 2
    59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
    cutoffTwoSharedDAGTraceR15C52Factors20 where
  bucketResult := cutoffTwoSharedDAGBucket0689Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR15C52Edge20 :
    CheckedReorderedEliminationStep 2 59
      (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
      cutoffTwoSharedDAGTraceR15C52Factors20
      cutoffTwoSharedDAGTraceR15C52Factors21 where
  step := cutoffTwoSharedDAGTraceR15C52Step20
  after_perm := by
    have houtside :
        factorOutside 59
            cutoffTwoSharedDAGTraceR15C52Factors20 =
          cutoffTwoSharedDAGFactorList [16, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 71] := by
      rfl
    have hids : ([564, 16, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 71]).Perm [16, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 71, 564] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR15C52Step20.bucketResult.result ::
        factorOutside 59
          cutoffTwoSharedDAGTraceR15C52Factors20).Perm
        cutoffTwoSharedDAGTraceR15C52Factors21
    rw [houtside]
    change
      (([564, 16, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 71]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 71, 564]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR15C52Step21 : CheckedScopedEliminationStep 2
    49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
    cutoffTwoSharedDAGTraceR15C52Factors21 where
  bucketResult := cutoffTwoSharedDAGBucket0690Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR15C52Edge21 :
    CheckedReorderedEliminationStep 2 49
      (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
      cutoffTwoSharedDAGTraceR15C52Factors21
      cutoffTwoSharedDAGTraceR15C52Factors22 where
  step := cutoffTwoSharedDAGTraceR15C52Step21
  after_perm := by
    have houtside :
        factorOutside 49
            cutoffTwoSharedDAGTraceR15C52Factors21 =
          cutoffTwoSharedDAGFactorList [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([565, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 565] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR15C52Step21.bucketResult.result ::
        factorOutside 49
          cutoffTwoSharedDAGTraceR15C52Factors21).Perm
        cutoffTwoSharedDAGTraceR15C52Factors22
    rw [houtside]
    change
      (([565, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 565]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR15C52Step22 : CheckedScopedEliminationStep 2
    68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
    cutoffTwoSharedDAGTraceR15C52Factors22 where
  bucketResult := cutoffTwoSharedDAGBucket0691Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR15C52Edge22 :
    CheckedReorderedEliminationStep 2 68
      (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
      cutoffTwoSharedDAGTraceR15C52Factors22
      cutoffTwoSharedDAGTraceR15C52Factors23 where
  step := cutoffTwoSharedDAGTraceR15C52Step22
  after_perm := by
    have houtside :
        factorOutside 68
            cutoffTwoSharedDAGTraceR15C52Factors22 =
          cutoffTwoSharedDAGFactorList [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([566, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 566] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR15C52Step22.bucketResult.result ::
        factorOutside 68
          cutoffTwoSharedDAGTraceR15C52Factors22).Perm
        cutoffTwoSharedDAGTraceR15C52Factors23
    rw [houtside]
    change
      (([566, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 566]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR15C52Step23 : CheckedScopedEliminationStep 2
    67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
    cutoffTwoSharedDAGTraceR15C52Factors23 where
  bucketResult := cutoffTwoSharedDAGBucket0692Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR15C52Edge23 :
    CheckedReorderedEliminationStep 2 67
      (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
      cutoffTwoSharedDAGTraceR15C52Factors23
      cutoffTwoSharedDAGTraceR15C52Factors24 where
  step := cutoffTwoSharedDAGTraceR15C52Step23
  after_perm := by
    have houtside :
        factorOutside 67
            cutoffTwoSharedDAGTraceR15C52Factors23 =
          cutoffTwoSharedDAGFactorList [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([185, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 185] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR15C52Step23.bucketResult.result ::
        factorOutside 67
          cutoffTwoSharedDAGTraceR15C52Factors23).Perm
        cutoffTwoSharedDAGTraceR15C52Factors24
    rw [houtside]
    change
      (([185, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 185]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR15C52Shard05_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR15C52Factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR15C52Factors24 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
        cutoffTwoSharedDAGTraceR15C52Factors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR15C52Edge20.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
        cutoffTwoSharedDAGTraceR15C52Factors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR15C52Edge21.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
        cutoffTwoSharedDAGTraceR15C52Factors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR15C52Edge22.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR15C52Factors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR15C52Edge23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR15C52Shard05

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR15C52Shard05.cutoffTwoSharedDAGTraceR15C52Shard05_partitionSum_eqv
