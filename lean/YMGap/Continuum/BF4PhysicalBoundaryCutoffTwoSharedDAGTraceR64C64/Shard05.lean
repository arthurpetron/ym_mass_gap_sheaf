/- Structural shared-DAG trace R64C64, shard 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR64C64Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR64C64Shard05

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR64C64Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR64C64Step20 : CheckedScopedEliminationStep 2
    59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
    cutoffTwoSharedDAGTraceR64C64Factors20 where
  bucketResult := cutoffTwoSharedDAGBucket0020Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR64C64Edge20 :
    CheckedReorderedEliminationStep 2 59
      (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
      cutoffTwoSharedDAGTraceR64C64Factors20
      cutoffTwoSharedDAGTraceR64C64Factors21 where
  step := cutoffTwoSharedDAGTraceR64C64Step20
  after_perm := by
    have houtside :
        factorOutside 59
            cutoffTwoSharedDAGTraceR64C64Factors20 =
          cutoffTwoSharedDAGFactorList [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([101, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 101] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR64C64Step20.bucketResult.result ::
        factorOutside 59
          cutoffTwoSharedDAGTraceR64C64Factors20).Perm
        cutoffTwoSharedDAGTraceR64C64Factors21
    rw [houtside]
    change
      (([101, 16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([16, 22, 23, 42, 42, 42, 43, 43, 43, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 101]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR64C64Step21 : CheckedScopedEliminationStep 2
    49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
    cutoffTwoSharedDAGTraceR64C64Factors21 where
  bucketResult := cutoffTwoSharedDAGBucket0021Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR64C64Edge21 :
    CheckedReorderedEliminationStep 2 49
      (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
      cutoffTwoSharedDAGTraceR64C64Factors21
      cutoffTwoSharedDAGTraceR64C64Factors22 where
  step := cutoffTwoSharedDAGTraceR64C64Step21
  after_perm := by
    have houtside :
        factorOutside 49
            cutoffTwoSharedDAGTraceR64C64Factors21 =
          cutoffTwoSharedDAGFactorList [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([102, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 102] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR64C64Step21.bucketResult.result ::
        factorOutside 49
          cutoffTwoSharedDAGTraceR64C64Factors21).Perm
        cutoffTwoSharedDAGTraceR64C64Factors22
    rw [houtside]
    change
      (([102, 22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 23, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 102]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR64C64Step22 : CheckedScopedEliminationStep 2
    68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
    cutoffTwoSharedDAGTraceR64C64Factors22 where
  bucketResult := cutoffTwoSharedDAGBucket0022Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR64C64Edge22 :
    CheckedReorderedEliminationStep 2 68
      (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
      cutoffTwoSharedDAGTraceR64C64Factors22
      cutoffTwoSharedDAGTraceR64C64Factors23 where
  step := cutoffTwoSharedDAGTraceR64C64Step22
  after_perm := by
    have houtside :
        factorOutside 68
            cutoffTwoSharedDAGTraceR64C64Factors22 =
          cutoffTwoSharedDAGFactorList [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([103, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 103] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR64C64Step22.bucketResult.result ::
        factorOutside 68
          cutoffTwoSharedDAGTraceR64C64Factors22).Perm
        cutoffTwoSharedDAGTraceR64C64Factors23
    rw [houtside]
    change
      (([103, 22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([22, 42, 42, 42, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 103]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR64C64Step23 : CheckedScopedEliminationStep 2
    67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
    cutoffTwoSharedDAGTraceR64C64Factors23 where
  bucketResult := cutoffTwoSharedDAGBucket0023Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR64C64Edge23 :
    CheckedReorderedEliminationStep 2 67
      (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
      cutoffTwoSharedDAGTraceR64C64Factors23
      cutoffTwoSharedDAGTraceR64C64Factors24 where
  step := cutoffTwoSharedDAGTraceR64C64Step23
  after_perm := by
    have houtside :
        factorOutside 67
            cutoffTwoSharedDAGTraceR64C64Factors23 =
          cutoffTwoSharedDAGFactorList [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] := by
      rfl
    have hids : ([104, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).Perm [55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 104] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR64C64Step23.bucketResult.result ::
        factorOutside 67
          cutoffTwoSharedDAGTraceR64C64Factors23).Perm
        cutoffTwoSharedDAGTraceR64C64Factors24
    rw [houtside]
    change
      (([104, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]).map cutoffTwoSharedDAGFactor).Perm
        (([55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 104]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR64C64Shard05_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        cutoffTwoSharedDAGTraceR64C64Factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR64C64Factors24 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
        cutoffTwoSharedDAGTraceR64C64Factors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR64C64Edge20.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
        cutoffTwoSharedDAGTraceR64C64Factors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR64C64Edge21.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
        cutoffTwoSharedDAGTraceR64C64Factors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR64C64Edge22.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR64C64Factors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR64C64Edge23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR64C64Shard05

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR64C64Shard05.cutoffTwoSharedDAGTraceR64C64Shard05_partitionSum_eqv
