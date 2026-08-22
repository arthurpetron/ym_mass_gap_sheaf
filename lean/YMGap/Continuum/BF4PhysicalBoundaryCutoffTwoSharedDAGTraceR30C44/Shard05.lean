/- Structural shared-DAG trace R30C44, shard 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C44Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C44Shard05

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C44Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR30C44Step20 : CheckedScopedEliminationStep 2
    59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
    cutoffTwoSharedDAGTraceR30C44Factors20 where
  bucketResult := cutoffTwoSharedDAGBucket1127Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C44Edge20 :
    CheckedReorderedEliminationStep 2 59
      (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
      cutoffTwoSharedDAGTraceR30C44Factors20
      cutoffTwoSharedDAGTraceR30C44Factors21 where
  step := cutoffTwoSharedDAGTraceR30C44Step20
  after_perm := by
    have houtside :
        factorOutside 59
            cutoffTwoSharedDAGTraceR30C44Factors20 =
          cutoffTwoSharedDAGFactorList [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71] := by
      rfl
    have hids : ([531, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71]).Perm [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 531] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C44Step20.bucketResult.result ::
        factorOutside 59
          cutoffTwoSharedDAGTraceR30C44Factors20).Perm
        cutoffTwoSharedDAGTraceR30C44Factors21
    rw [houtside]
    change
      (([531, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 71, 531]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C44Step21 : CheckedScopedEliminationStep 2
    49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
    cutoffTwoSharedDAGTraceR30C44Factors21 where
  bucketResult := cutoffTwoSharedDAGBucket0628Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C44Edge21 :
    CheckedReorderedEliminationStep 2 49
      (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
      cutoffTwoSharedDAGTraceR30C44Factors21
      cutoffTwoSharedDAGTraceR30C44Factors22 where
  step := cutoffTwoSharedDAGTraceR30C44Step21
  after_perm := by
    have houtside :
        factorOutside 49
            cutoffTwoSharedDAGTraceR30C44Factors21 =
          cutoffTwoSharedDAGFactorList [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([532, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 532] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C44Step21.bucketResult.result ::
        factorOutside 49
          cutoffTwoSharedDAGTraceR30C44Factors21).Perm
        cutoffTwoSharedDAGTraceR30C44Factors22
    rw [houtside]
    change
      (([532, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 532]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C44Step22 : CheckedScopedEliminationStep 2
    68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
    cutoffTwoSharedDAGTraceR30C44Factors22 where
  bucketResult := cutoffTwoSharedDAGBucket0616Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C44Edge22 :
    CheckedReorderedEliminationStep 2 68
      (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
      cutoffTwoSharedDAGTraceR30C44Factors22
      cutoffTwoSharedDAGTraceR30C44Factors23 where
  step := cutoffTwoSharedDAGTraceR30C44Step22
  after_perm := by
    have houtside :
        factorOutside 68
            cutoffTwoSharedDAGTraceR30C44Factors22 =
          cutoffTwoSharedDAGFactorList [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([533, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 533] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C44Step22.bucketResult.result ::
        factorOutside 68
          cutoffTwoSharedDAGTraceR30C44Factors22).Perm
        cutoffTwoSharedDAGTraceR30C44Factors23
    rw [houtside]
    change
      (([533, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 533]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C44Step23 : CheckedScopedEliminationStep 2
    67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
    cutoffTwoSharedDAGTraceR30C44Factors23 where
  bucketResult := cutoffTwoSharedDAGBucket0617Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C44Edge23 :
    CheckedReorderedEliminationStep 2 67
      (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
      cutoffTwoSharedDAGTraceR30C44Factors23
      cutoffTwoSharedDAGTraceR30C44Factors24 where
  step := cutoffTwoSharedDAGTraceR30C44Step23
  after_perm := by
    have houtside :
        factorOutside 67
            cutoffTwoSharedDAGTraceR30C44Factors23 =
          cutoffTwoSharedDAGFactorList [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([534, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 534] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C44Step23.bucketResult.result ::
        factorOutside 67
          cutoffTwoSharedDAGTraceR30C44Factors23).Perm
        cutoffTwoSharedDAGTraceR30C44Factors24
    rw [houtside]
    change
      (([534, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 534]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR30C44Shard05_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR30C44Factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR30C44Factors24 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
        cutoffTwoSharedDAGTraceR30C44Factors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C44Edge20.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
        cutoffTwoSharedDAGTraceR30C44Factors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C44Edge21.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
        cutoffTwoSharedDAGTraceR30C44Factors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C44Edge22.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR30C44Factors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C44Edge23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C44Shard05

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C44Shard05.cutoffTwoSharedDAGTraceR30C44Shard05_partitionSum_eqv
