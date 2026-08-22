/- Structural shared-DAG trace R26C47, shard 0. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Shard00

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

def cutoffTwoSharedDAGTraceR26C47Step0 : CheckedScopedEliminationStep 2
    38
    (cutoffTwoCubeInterfaceEliminationOrder.drop 1)
    cutoffTwoSharedDAGTraceR26C47Factors0 where
  bucketResult := cutoffTwoSharedDAGBucket0000Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge0 :
    CheckedReorderedEliminationStep 2 38
      (cutoffTwoCubeInterfaceEliminationOrder.drop 1)
      cutoffTwoSharedDAGTraceR26C47Factors0
      cutoffTwoSharedDAGTraceR26C47Factors1 where
  step := cutoffTwoSharedDAGTraceR26C47Step0
  after_perm := by
    have houtside :
        factorOutside 38
            cutoffTwoSharedDAGTraceR26C47Factors0 =
          cutoffTwoSharedDAGFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80] := by
      rfl
    have hids : ([81, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80]).Perm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step0.bucketResult.result ::
        factorOutside 38
          cutoffTwoSharedDAGTraceR26C47Factors0).Perm
        cutoffTwoSharedDAGTraceR26C47Factors1
    rw [houtside]
    change
      (([81, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR26C47Step1 : CheckedScopedEliminationStep 2
    22
    (cutoffTwoCubeInterfaceEliminationOrder.drop 2)
    cutoffTwoSharedDAGTraceR26C47Factors1 where
  bucketResult := cutoffTwoSharedDAGBucket0001Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge1 :
    CheckedReorderedEliminationStep 2 22
      (cutoffTwoCubeInterfaceEliminationOrder.drop 2)
      cutoffTwoSharedDAGTraceR26C47Factors1
      cutoffTwoSharedDAGTraceR26C47Factors2 where
  step := cutoffTwoSharedDAGTraceR26C47Step1
  after_perm := by
    have houtside :
        factorOutside 22
            cutoffTwoSharedDAGTraceR26C47Factors1 =
          cutoffTwoSharedDAGFactorList [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 30, 30, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81] := by
      rfl
    have hids : ([82, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 30, 30, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81]).Perm [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 30, 30, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81, 82] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step1.bucketResult.result ::
        factorOutside 22
          cutoffTwoSharedDAGTraceR26C47Factors1).Perm
        cutoffTwoSharedDAGTraceR26C47Factors2
    rw [houtside]
    change
      (([82, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 30, 30, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 30, 30, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81, 82]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR26C47Step2 : CheckedScopedEliminationStep 2
    14
    (cutoffTwoCubeInterfaceEliminationOrder.drop 3)
    cutoffTwoSharedDAGTraceR26C47Factors2 where
  bucketResult := cutoffTwoSharedDAGBucket0002Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge2 :
    CheckedReorderedEliminationStep 2 14
      (cutoffTwoCubeInterfaceEliminationOrder.drop 3)
      cutoffTwoSharedDAGTraceR26C47Factors2
      cutoffTwoSharedDAGTraceR26C47Factors3 where
  step := cutoffTwoSharedDAGTraceR26C47Step2
  after_perm := by
    have houtside :
        factorOutside 14
            cutoffTwoSharedDAGTraceR26C47Factors2 =
          cutoffTwoSharedDAGFactorList [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81, 82] := by
      rfl
    have hids : ([83, 0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81, 82]).Perm [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81, 82, 83] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step2.bucketResult.result ::
        factorOutside 14
          cutoffTwoSharedDAGTraceR26C47Factors2).Perm
        cutoffTwoSharedDAGTraceR26C47Factors3
    rw [houtside]
    change
      (([83, 0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81, 82]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 48, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 79, 80, 80, 81, 82, 83]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR26C47Step3 : CheckedScopedEliminationStep 2
    5
    (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
    cutoffTwoSharedDAGTraceR26C47Factors3 where
  bucketResult := cutoffTwoSharedDAGBucket0093Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR26C47Edge3 :
    CheckedReorderedEliminationStep 2 5
      (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
      cutoffTwoSharedDAGTraceR26C47Factors3
      cutoffTwoSharedDAGTraceR26C47Factors4 where
  step := cutoffTwoSharedDAGTraceR26C47Step3
  after_perm := by
    have houtside :
        factorOutside 5
            cutoffTwoSharedDAGTraceR26C47Factors3 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82] := by
      rfl
    have hids : ([168, 0, 1, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82]).Perm [0, 1, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR26C47Step3.bucketResult.result ::
        factorOutside 5
          cutoffTwoSharedDAGTraceR26C47Factors3).Perm
        cutoffTwoSharedDAGTraceR26C47Factors4
    rw [houtside]
    change
      (([168, 0, 1, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29, 31, 33, 34, 34, 34, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 50, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 66, 69, 69, 71, 71, 72, 72, 74, 76, 76, 77, 78, 80, 80, 81, 82, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR26C47Shard00_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 0)
        cutoffTwoSharedDAGTraceR26C47Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        cutoffTwoSharedDAGTraceR26C47Factors4 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 1)
        cutoffTwoSharedDAGTraceR26C47Factors1 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge0.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 2)
        cutoffTwoSharedDAGTraceR26C47Factors2 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge1.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 3)
        cutoffTwoSharedDAGTraceR26C47Factors3 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge2.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        cutoffTwoSharedDAGTraceR26C47Factors4 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR26C47Edge3.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Shard00

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C47Shard00.cutoffTwoSharedDAGTraceR26C47Shard00_partitionSum_eqv
