/- Structural shared-DAG trace R30C56, shard 3. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C56Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C56Shard03

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C56Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR30C56Step12 : CheckedScopedEliminationStep 2
    13
    (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
    cutoffTwoSharedDAGTraceR30C56Factors12 where
  bucketResult := cutoffTwoSharedDAGBucket0094Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C56Edge12 :
    CheckedReorderedEliminationStep 2 13
      (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
      cutoffTwoSharedDAGTraceR30C56Factors12
      cutoffTwoSharedDAGTraceR30C56Factors13 where
  step := cutoffTwoSharedDAGTraceR30C56Step12
  after_perm := by
    have houtside :
        factorOutside 13
            cutoffTwoSharedDAGTraceR30C56Factors12 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 78, 78, 80, 92, 117] := by
      rfl
    have hids : ([169, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 78, 78, 80, 92, 117]).Perm [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 78, 78, 80, 92, 117, 169] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C56Step12.bucketResult.result ::
        factorOutside 13
          cutoffTwoSharedDAGTraceR30C56Factors12).Perm
        cutoffTwoSharedDAGTraceR30C56Factors13
    rw [houtside]
    change
      (([169, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 78, 78, 80, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 78, 78, 80, 92, 117, 169]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C56Step13 : CheckedScopedEliminationStep 2
    4
    (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
    cutoffTwoSharedDAGTraceR30C56Factors13 where
  bucketResult := cutoffTwoSharedDAGBucket0561Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C56Edge13 :
    CheckedReorderedEliminationStep 2 4
      (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
      cutoffTwoSharedDAGTraceR30C56Factors13
      cutoffTwoSharedDAGTraceR30C56Factors14 where
  step := cutoffTwoSharedDAGTraceR30C56Step13
  after_perm := by
    have houtside :
        factorOutside 4
            cutoffTwoSharedDAGTraceR30C56Factors13 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 92, 117] := by
      rfl
    have hids : ([170, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 92, 117]).Perm [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 92, 117, 170] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C56Step13.bucketResult.result ::
        factorOutside 4
          cutoffTwoSharedDAGTraceR30C56Factors13).Perm
        cutoffTwoSharedDAGTraceR30C56Factors14
    rw [houtside]
    change
      (([170, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 50, 50, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 92, 117, 170]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C56Step14 : CheckedScopedEliminationStep 2
    41
    (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
    cutoffTwoSharedDAGTraceR30C56Factors14 where
  bucketResult := cutoffTwoSharedDAGBucket0171Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C56Edge14 :
    CheckedReorderedEliminationStep 2 41
      (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
      cutoffTwoSharedDAGTraceR30C56Factors14
      cutoffTwoSharedDAGTraceR30C56Factors15 where
  step := cutoffTwoSharedDAGTraceR30C56Step14
  after_perm := by
    have houtside :
        factorOutside 41
            cutoffTwoSharedDAGTraceR30C56Factors14 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 170] := by
      rfl
    have hids : ([240, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 170]).Perm [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 170, 240] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C56Step14.bucketResult.result ::
        factorOutside 41
          cutoffTwoSharedDAGTraceR30C56Factors14).Perm
        cutoffTwoSharedDAGTraceR30C56Factors15
    rw [houtside]
    change
      (([240, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 170]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 80, 170, 240]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C56Step15 : CheckedScopedEliminationStep 2
    2
    (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
    cutoffTwoSharedDAGTraceR30C56Factors15 where
  bucketResult := cutoffTwoSharedDAGBucket0967Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C56Edge15 :
    CheckedReorderedEliminationStep 2 2
      (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
      cutoffTwoSharedDAGTraceR30C56Factors15
      cutoffTwoSharedDAGTraceR30C56Factors16 where
  step := cutoffTwoSharedDAGTraceR30C56Step15
  after_perm := by
    have houtside :
        factorOutside 2
            cutoffTwoSharedDAGTraceR30C56Factors15 =
          cutoffTwoSharedDAGFactorList [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75] := by
      rfl
    have hids : ([686, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75]).Perm [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 686] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C56Step15.bucketResult.result ::
        factorOutside 2
          cutoffTwoSharedDAGTraceR30C56Factors15).Perm
        cutoffTwoSharedDAGTraceR30C56Factors16
    rw [houtside]
    change
      (([686, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 46, 49, 49, 53, 54, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 59, 72, 75, 686]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR30C56Shard03_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR30C56Factors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR30C56Factors16 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
        cutoffTwoSharedDAGTraceR30C56Factors13 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C56Edge12.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
        cutoffTwoSharedDAGTraceR30C56Factors14 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C56Edge13.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
        cutoffTwoSharedDAGTraceR30C56Factors15 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C56Edge14.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR30C56Factors16 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C56Edge15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C56Shard03

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C56Shard03.cutoffTwoSharedDAGTraceR30C56Shard03_partitionSum_eqv
