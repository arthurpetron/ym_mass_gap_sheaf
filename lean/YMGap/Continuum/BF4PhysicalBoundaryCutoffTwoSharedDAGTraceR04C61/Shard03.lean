/- Structural shared-DAG trace R04C61, shard 3. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C61Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C61Shard03

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C61Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR04C61Step12 : CheckedScopedEliminationStep 2
    13
    (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
    cutoffTwoSharedDAGTraceR04C61Factors12 where
  bucketResult := cutoffTwoSharedDAGBucket0049Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C61Edge12 :
    CheckedReorderedEliminationStep 2 13
      (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
      cutoffTwoSharedDAGTraceR04C61Factors12
      cutoffTwoSharedDAGTraceR04C61Factors13 where
  step := cutoffTwoSharedDAGTraceR04C61Step12
  after_perm := by
    have houtside :
        factorOutside 13
            cutoffTwoSharedDAGTraceR04C61Factors12 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117] := by
      rfl
    have hids : ([128, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117]).Perm [0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117, 128] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C61Step12.bucketResult.result ::
        factorOutside 13
          cutoffTwoSharedDAGTraceR04C61Factors12).Perm
        cutoffTwoSharedDAGTraceR04C61Factors13
    rw [houtside]
    change
      (([128, 0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117, 128]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR04C61Step13 : CheckedScopedEliminationStep 2
    4
    (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
    cutoffTwoSharedDAGTraceR04C61Factors13 where
  bucketResult := cutoffTwoSharedDAGBucket0050Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C61Edge13 :
    CheckedReorderedEliminationStep 2 4
      (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
      cutoffTwoSharedDAGTraceR04C61Factors13
      cutoffTwoSharedDAGTraceR04C61Factors14 where
  step := cutoffTwoSharedDAGTraceR04C61Step13
  after_perm := by
    have houtside :
        factorOutside 4
            cutoffTwoSharedDAGTraceR04C61Factors13 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117] := by
      rfl
    have hids : ([129, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117]).Perm [0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117, 129] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C61Step13.bucketResult.result ::
        factorOutside 4
          cutoffTwoSharedDAGTraceR04C61Factors13).Perm
        cutoffTwoSharedDAGTraceR04C61Factors14
    rw [houtside]
    change
      (([129, 0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 70, 70, 71, 71, 73, 73, 75, 75, 92, 117, 129]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR04C61Step14 : CheckedScopedEliminationStep 2
    41
    (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
    cutoffTwoSharedDAGTraceR04C61Factors14 where
  bucketResult := cutoffTwoSharedDAGBucket0485Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C61Edge14 :
    CheckedReorderedEliminationStep 2 41
      (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
      cutoffTwoSharedDAGTraceR04C61Factors14
      cutoffTwoSharedDAGTraceR04C61Factors15 where
  step := cutoffTwoSharedDAGTraceR04C61Step14
  after_perm := by
    have houtside :
        factorOutside 41
            cutoffTwoSharedDAGTraceR04C61Factors14 =
          cutoffTwoSharedDAGFactorList [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 129] := by
      rfl
    have hids : ([118, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 129]).Perm [0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 118, 129] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C61Step14.bucketResult.result ::
        factorOutside 41
          cutoffTwoSharedDAGTraceR04C61Factors14).Perm
        cutoffTwoSharedDAGTraceR04C61Factors15
    rw [houtside]
    change
      (([118, 0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 129]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 68, 71, 71, 73, 73, 75, 75, 118, 129]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR04C61Step15 : CheckedScopedEliminationStep 2
    2
    (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
    cutoffTwoSharedDAGTraceR04C61Factors15 where
  bucketResult := cutoffTwoSharedDAGBucket0057Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C61Edge15 :
    CheckedReorderedEliminationStep 2 2
      (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
      cutoffTwoSharedDAGTraceR04C61Factors15
      cutoffTwoSharedDAGTraceR04C61Factors16 where
  step := cutoffTwoSharedDAGTraceR04C61Step15
  after_perm := by
    have houtside :
        factorOutside 2
            cutoffTwoSharedDAGTraceR04C61Factors15 =
          cutoffTwoSharedDAGFactorList [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75] := by
      rfl
    have hids : ([135, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75]).Perm [3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75, 135] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C61Step15.bucketResult.result ::
        factorOutside 2
          cutoffTwoSharedDAGTraceR04C61Factors15).Perm
        cutoffTwoSharedDAGTraceR04C61Factors16
    rw [houtside]
    change
      (([135, 3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75]).map cutoffTwoSharedDAGFactor).Perm
        (([3, 6, 9, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 49, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 62, 68, 71, 71, 73, 73, 75, 75, 135]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR04C61Shard03_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR04C61Factors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR04C61Factors16 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
        cutoffTwoSharedDAGTraceR04C61Factors13 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C61Edge12.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
        cutoffTwoSharedDAGTraceR04C61Factors14 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C61Edge13.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
        cutoffTwoSharedDAGTraceR04C61Factors15 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C61Edge14.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        cutoffTwoSharedDAGTraceR04C61Factors16 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C61Edge15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C61Shard03

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C61Shard03.cutoffTwoSharedDAGTraceR04C61Shard03_partitionSum_eqv
