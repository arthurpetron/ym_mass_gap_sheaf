/- Structural shared-DAG trace R12C53, shard 3. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C53Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C53Shard03

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C53Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR12C53Step12 : CheckedScopedEliminationStep 2
    13
    (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
    cutoffTwoSharedDAGTraceR12C53Factors12 where
  bucketResult := cutoffTwoSharedDAGBucket0582Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C53Edge12 :
    CheckedReorderedEliminationStep 2 13
      (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
      cutoffTwoSharedDAGTraceR12C53Factors12
      cutoffTwoSharedDAGTraceR12C53Factors13 where
  step := cutoffTwoSharedDAGTraceR12C53Step12
  after_perm := by
    have houtside :
        factorOutside 13
            cutoffTwoSharedDAGTraceR12C53Factors12 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 78, 78, 92, 117] := by
      rfl
    have hids : ([258, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 78, 78, 92, 117]).Perm [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 78, 78, 92, 117, 258] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C53Step12.bucketResult.result ::
        factorOutside 13
          cutoffTwoSharedDAGTraceR12C53Factors12).Perm
        cutoffTwoSharedDAGTraceR12C53Factors13
    rw [houtside]
    change
      (([258, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 78, 78, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 78, 78, 92, 117, 258]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C53Step13 : CheckedScopedEliminationStep 2
    4
    (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
    cutoffTwoSharedDAGTraceR12C53Factors13 where
  bucketResult := cutoffTwoSharedDAGBucket0583Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C53Edge13 :
    CheckedReorderedEliminationStep 2 4
      (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
      cutoffTwoSharedDAGTraceR12C53Factors13
      cutoffTwoSharedDAGTraceR12C53Factors14 where
  step := cutoffTwoSharedDAGTraceR12C53Step13
  after_perm := by
    have houtside :
        factorOutside 4
            cutoffTwoSharedDAGTraceR12C53Factors13 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117] := by
      rfl
    have hids : ([436, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117]).Perm [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117, 436] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C53Step13.bucketResult.result ::
        factorOutside 4
          cutoffTwoSharedDAGTraceR12C53Factors13).Perm
        cutoffTwoSharedDAGTraceR12C53Factors14
    rw [houtside]
    change
      (([436, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117, 436]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C53Step14 : CheckedScopedEliminationStep 2
    41
    (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
    cutoffTwoSharedDAGTraceR12C53Factors14 where
  bucketResult := cutoffTwoSharedDAGBucket0485Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C53Edge14 :
    CheckedReorderedEliminationStep 2 41
      (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
      cutoffTwoSharedDAGTraceR12C53Factors14
      cutoffTwoSharedDAGTraceR12C53Factors15 where
  step := cutoffTwoSharedDAGTraceR12C53Step14
  after_perm := by
    have houtside :
        factorOutside 41
            cutoffTwoSharedDAGTraceR12C53Factors14 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 436] := by
      rfl
    have hids : ([118, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 436]).Perm [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 118, 436] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C53Step14.bucketResult.result ::
        factorOutside 41
          cutoffTwoSharedDAGTraceR12C53Factors14).Perm
        cutoffTwoSharedDAGTraceR12C53Factors15
    rw [houtside]
    change
      (([118, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 436]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 118, 436]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C53Step15 : CheckedScopedEliminationStep 2
    2
    (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
    cutoffTwoSharedDAGTraceR12C53Factors15 where
  bucketResult := cutoffTwoSharedDAGBucket0604Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C53Edge15 :
    CheckedReorderedEliminationStep 2 2
      (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
      cutoffTwoSharedDAGTraceR12C53Factors15
      cutoffTwoSharedDAGTraceR12C53Factors16 where
  step := cutoffTwoSharedDAGTraceR12C53Step15
  after_perm := by
    have houtside :
        factorOutside 2
            cutoffTwoSharedDAGTraceR12C53Factors15 =
          cutoffTwoSharedDAGFactorList [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75] := by
      rfl
    have hids : ([524, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75]).Perm [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75, 524] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C53Step15.bucketResult.result ::
        factorOutside 2
          cutoffTwoSharedDAGTraceR12C53Factors15).Perm
        cutoffTwoSharedDAGTraceR12C53Factors16
    rw [houtside]
    change
      (([524, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75, 524]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR12C53Shard03_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR12C53Factors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR12C53Factors16 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
        cutoffTwoSharedDAGTraceR12C53Factors13 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C53Edge12.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
        cutoffTwoSharedDAGTraceR12C53Factors14 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C53Edge13.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
        cutoffTwoSharedDAGTraceR12C53Factors15 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C53Edge14.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR12C53Factors16 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C53Edge15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C53Shard03

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C53Shard03.cutoffTwoSharedDAGTraceR12C53Shard03_partitionSum_eqv
