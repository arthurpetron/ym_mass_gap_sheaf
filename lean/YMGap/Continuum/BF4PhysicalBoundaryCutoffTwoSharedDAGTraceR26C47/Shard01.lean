/- Structural shared-DAG trace R26C47, shard 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Shard01

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR26C47Step4 : CheckedScopedEliminationStep 2
    31
    (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
    cutoffTwoSharedDAGTraceR26C47Factors4 where
  bucketResult := cutoffTwoSharedDAGBucket0004Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge4 :
    CheckedReorderedEliminationStep 2 31
      (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
      cutoffTwoSharedDAGTraceR26C47Factors4
      cutoffTwoSharedDAGTraceR26C47Factors5 where
  step := cutoffTwoSharedDAGTraceR26C47Step4
  after_perm := by
    have houtside :
        factorOutside 31
            cutoffTwoSharedDAGTraceR26C47Factors4 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168] := by
      rfl
    have hids : ([85, 0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168]).Perm [0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 85, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step4.bucketResult.result ::
        factorOutside 31
          cutoffTwoSharedDAGTraceR26C47Factors4).Perm
        cutoffTwoSharedDAGTraceR26C47Factors5
    rw [houtside]
    change
      (([85, 0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 85, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR26C47Step5 : CheckedScopedEliminationStep 2
    32
    (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
    cutoffTwoSharedDAGTraceR26C47Factors5 where
  bucketResult := cutoffTwoSharedDAGBucket0005Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge5 :
    CheckedReorderedEliminationStep 2 32
      (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
      cutoffTwoSharedDAGTraceR26C47Factors5
      cutoffTwoSharedDAGTraceR26C47Factors6 where
  step := cutoffTwoSharedDAGTraceR26C47Step5
  after_perm := by
    have houtside :
        factorOutside 32
            cutoffTwoSharedDAGTraceR26C47Factors5 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168] := by
      rfl
    have hids : ([86, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step5.bucketResult.result ::
        factorOutside 32
          cutoffTwoSharedDAGTraceR26C47Factors5).Perm
        cutoffTwoSharedDAGTraceR26C47Factors6
    rw [houtside]
    change
      (([86, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR26C47Step6 : CheckedScopedEliminationStep 2
    56
    (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
    cutoffTwoSharedDAGTraceR26C47Factors6 where
  bucketResult := cutoffTwoSharedDAGBucket0006Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge6 :
    CheckedReorderedEliminationStep 2 56
      (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
      cutoffTwoSharedDAGTraceR26C47Factors6
      cutoffTwoSharedDAGTraceR26C47Factors7 where
  step := cutoffTwoSharedDAGTraceR26C47Step6
  after_perm := by
    have houtside :
        factorOutside 56
            cutoffTwoSharedDAGTraceR26C47Factors6 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168] := by
      rfl
    have hids : ([87, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 87, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step6.bucketResult.result ::
        factorOutside 56
          cutoffTwoSharedDAGTraceR26C47Factors6).Perm
        cutoffTwoSharedDAGTraceR26C47Factors7
    rw [houtside]
    change
      (([87, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 87, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR26C47Step7 : CheckedScopedEliminationStep 2
    58
    (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
    cutoffTwoSharedDAGTraceR26C47Factors7 where
  bucketResult := cutoffTwoSharedDAGBucket0007Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge7 :
    CheckedReorderedEliminationStep 2 58
      (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
      cutoffTwoSharedDAGTraceR26C47Factors7
      cutoffTwoSharedDAGTraceR26C47Factors8 where
  step := cutoffTwoSharedDAGTraceR26C47Step7
  after_perm := by
    have houtside :
        factorOutside 58
            cutoffTwoSharedDAGTraceR26C47Factors7 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168] := by
      rfl
    have hids : ([88, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 88, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step7.bucketResult.result ::
        factorOutside 58
          cutoffTwoSharedDAGTraceR26C47Factors7).Perm
        cutoffTwoSharedDAGTraceR26C47Factors8
    rw [houtside]
    change
      (([88, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 86, 88, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR26C47Shard01_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        cutoffTwoSharedDAGTraceR26C47Factors4 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR26C47Factors8 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
        cutoffTwoSharedDAGTraceR26C47Factors5 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge4.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
        cutoffTwoSharedDAGTraceR26C47Factors6 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge5.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
        cutoffTwoSharedDAGTraceR26C47Factors7 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge6.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR26C47Factors8 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge7.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Shard01

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Shard01.cutoffTwoSharedDAGTraceR26C47Shard01_partitionSum_eqv
