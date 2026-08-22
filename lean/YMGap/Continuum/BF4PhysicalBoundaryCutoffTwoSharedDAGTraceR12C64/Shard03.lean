/- Structural shared-DAG trace R12C64, shard 3. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C64Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C64Shard03

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C64Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR12C64Step12 : CheckedScopedEliminationStep 2
    13
    (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
    cutoffTwoSharedDAGTraceR12C64Factors12 where
  bucketResult := cutoffTwoSharedDAGBucket0112Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C64Edge12 :
    CheckedReorderedEliminationStep 2 13
      (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
      cutoffTwoSharedDAGTraceR12C64Factors12
      cutoffTwoSharedDAGTraceR12C64Factors13 where
  step := cutoffTwoSharedDAGTraceR12C64Step12
  after_perm := by
    have houtside :
        factorOutside 13
            cutoffTwoSharedDAGTraceR12C64Factors12 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 78, 92, 117] := by
      rfl
    have hids : ([186, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 78, 92, 117]).Perm [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 78, 92, 117, 186] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C64Step12.bucketResult.result ::
        factorOutside 13
          cutoffTwoSharedDAGTraceR12C64Factors12).Perm
        cutoffTwoSharedDAGTraceR12C64Factors13
    rw [houtside]
    change
      (([186, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 78, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 78, 92, 117, 186]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C64Step13 : CheckedScopedEliminationStep 2
    4
    (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
    cutoffTwoSharedDAGTraceR12C64Factors13 where
  bucketResult := cutoffTwoSharedDAGBucket0113Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C64Edge13 :
    CheckedReorderedEliminationStep 2 4
      (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
      cutoffTwoSharedDAGTraceR12C64Factors13
      cutoffTwoSharedDAGTraceR12C64Factors14 where
  step := cutoffTwoSharedDAGTraceR12C64Step13
  after_perm := by
    have houtside :
        factorOutside 4
            cutoffTwoSharedDAGTraceR12C64Factors13 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 92, 117] := by
      rfl
    have hids : ([187, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 92, 117]).Perm [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 92, 117, 187] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C64Step13.bucketResult.result ::
        factorOutside 4
          cutoffTwoSharedDAGTraceR12C64Factors13).Perm
        cutoffTwoSharedDAGTraceR12C64Factors14
    rw [houtside]
    change
      (([187, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 50, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 70, 71, 73, 75, 92, 117, 187]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C64Step14 : CheckedScopedEliminationStep 2
    41
    (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
    cutoffTwoSharedDAGTraceR12C64Factors14 where
  bucketResult := cutoffTwoSharedDAGBucket0039Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C64Edge14 :
    CheckedReorderedEliminationStep 2 41
      (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
      cutoffTwoSharedDAGTraceR12C64Factors14
      cutoffTwoSharedDAGTraceR12C64Factors15 where
  step := cutoffTwoSharedDAGTraceR12C64Step14
  after_perm := by
    have houtside :
        factorOutside 41
            cutoffTwoSharedDAGTraceR12C64Factors14 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 71, 73, 75, 187] := by
      rfl
    have hids : ([118, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 71, 73, 75, 187]).Perm [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 71, 73, 75, 118, 187] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C64Step14.bucketResult.result ::
        factorOutside 41
          cutoffTwoSharedDAGTraceR12C64Factors14).Perm
        cutoffTwoSharedDAGTraceR12C64Factors15
    rw [houtside]
    change
      (([118, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 71, 73, 75, 187]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 62, 71, 73, 75, 118, 187]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C64Step15 : CheckedScopedEliminationStep 2
    2
    (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
    cutoffTwoSharedDAGTraceR12C64Factors15 where
  bucketResult := cutoffTwoSharedDAGBucket0122Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C64Edge15 :
    CheckedReorderedEliminationStep 2 2
      (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
      cutoffTwoSharedDAGTraceR12C64Factors15
      cutoffTwoSharedDAGTraceR12C64Factors16 where
  step := cutoffTwoSharedDAGTraceR12C64Step15
  after_perm := by
    have houtside :
        factorOutside 2
            cutoffTwoSharedDAGTraceR12C64Factors15 =
          cutoffTwoSharedDAGFactorList [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 62, 71, 73, 75] := by
      rfl
    have hids : ([195, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 62, 71, 73, 75]).Perm [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 62, 71, 73, 75, 195] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C64Step15.bucketResult.result ::
        factorOutside 2
          cutoffTwoSharedDAGTraceR12C64Factors15).Perm
        cutoffTwoSharedDAGTraceR12C64Factors16
    rw [houtside]
    change
      (([195, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 62, 71, 73, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 62, 71, 73, 75, 195]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR12C64Shard03_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR12C64Factors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR12C64Factors16 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
        cutoffTwoSharedDAGTraceR12C64Factors13 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C64Edge12.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
        cutoffTwoSharedDAGTraceR12C64Factors14 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C64Edge13.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
        cutoffTwoSharedDAGTraceR12C64Factors15 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C64Edge14.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR12C64Factors16 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C64Edge15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C64Shard03

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C64Shard03.cutoffTwoSharedDAGTraceR12C64Shard03_partitionSum_eqv
