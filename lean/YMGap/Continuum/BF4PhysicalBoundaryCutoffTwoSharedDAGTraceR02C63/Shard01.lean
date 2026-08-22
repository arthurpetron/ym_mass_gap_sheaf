/- Structural shared-DAG trace R02C63, shard 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR02C63Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR02C63Shard01

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR02C63Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR02C63Step4 : CheckedScopedEliminationStep 2
    31
    (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
    cutoffTwoSharedDAGTraceR02C63Factors4 where
  bucketResult := cutoffTwoSharedDAGBucket0004Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR02C63Edge4 :
    CheckedReorderedEliminationStep 2 31
      (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
      cutoffTwoSharedDAGTraceR02C63Factors4
      cutoffTwoSharedDAGTraceR02C63Factors5 where
  step := cutoffTwoSharedDAGTraceR02C63Step4
  after_perm := by
    have houtside :
        factorOutside 31
            cutoffTwoSharedDAGTraceR02C63Factors4 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 105] := by
      rfl
    have hids : ([85, 0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 105]).Perm [0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 85, 105] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR02C63Step4.bucketResult.result ::
        factorOutside 31
          cutoffTwoSharedDAGTraceR02C63Factors4).Perm
        cutoffTwoSharedDAGTraceR02C63Factors5
    rw [houtside]
    change
      (([85, 0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 105]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 85, 105]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR02C63Step5 : CheckedScopedEliminationStep 2
    32
    (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
    cutoffTwoSharedDAGTraceR02C63Factors5 where
  bucketResult := cutoffTwoSharedDAGBucket0005Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR02C63Edge5 :
    CheckedReorderedEliminationStep 2 32
      (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
      cutoffTwoSharedDAGTraceR02C63Factors5
      cutoffTwoSharedDAGTraceR02C63Factors6 where
  step := cutoffTwoSharedDAGTraceR02C63Step5
  after_perm := by
    have houtside :
        factorOutside 32
            cutoffTwoSharedDAGTraceR02C63Factors5 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 105] := by
      rfl
    have hids : ([86, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 105]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR02C63Step5.bucketResult.result ::
        factorOutside 32
          cutoffTwoSharedDAGTraceR02C63Factors5).Perm
        cutoffTwoSharedDAGTraceR02C63Factors6
    rw [houtside]
    change
      (([86, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 105]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR02C63Step6 : CheckedScopedEliminationStep 2
    56
    (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
    cutoffTwoSharedDAGTraceR02C63Factors6 where
  bucketResult := cutoffTwoSharedDAGBucket0006Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR02C63Edge6 :
    CheckedReorderedEliminationStep 2 56
      (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
      cutoffTwoSharedDAGTraceR02C63Factors6
      cutoffTwoSharedDAGTraceR02C63Factors7 where
  step := cutoffTwoSharedDAGTraceR02C63Step6
  after_perm := by
    have houtside :
        factorOutside 56
            cutoffTwoSharedDAGTraceR02C63Factors6 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105] := by
      rfl
    have hids : ([87, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 87, 105] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR02C63Step6.bucketResult.result ::
        factorOutside 56
          cutoffTwoSharedDAGTraceR02C63Factors6).Perm
        cutoffTwoSharedDAGTraceR02C63Factors7
    rw [houtside]
    change
      (([87, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 87, 105]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR02C63Step7 : CheckedScopedEliminationStep 2
    58
    (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
    cutoffTwoSharedDAGTraceR02C63Factors7 where
  bucketResult := cutoffTwoSharedDAGBucket0007Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR02C63Edge7 :
    CheckedReorderedEliminationStep 2 58
      (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
      cutoffTwoSharedDAGTraceR02C63Factors7
      cutoffTwoSharedDAGTraceR02C63Factors8 where
  step := cutoffTwoSharedDAGTraceR02C63Step7
  after_perm := by
    have houtside :
        factorOutside 58
            cutoffTwoSharedDAGTraceR02C63Factors7 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105] := by
      rfl
    have hids : ([88, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 88, 105] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR02C63Step7.bucketResult.result ::
        factorOutside 58
          cutoffTwoSharedDAGTraceR02C63Factors7).Perm
        cutoffTwoSharedDAGTraceR02C63Factors8
    rw [houtside]
    change
      (([88, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 105]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 51, 52, 53, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 62, 64, 65, 66, 69, 69, 70, 70, 71, 71, 72, 72, 81, 82, 86, 88, 105]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR02C63Shard01_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        cutoffTwoSharedDAGTraceR02C63Factors4 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR02C63Factors8 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
        cutoffTwoSharedDAGTraceR02C63Factors5 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR02C63Edge4.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
        cutoffTwoSharedDAGTraceR02C63Factors6 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR02C63Edge5.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
        cutoffTwoSharedDAGTraceR02C63Factors7 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR02C63Edge6.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR02C63Factors8 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR02C63Edge7.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR02C63Shard01

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR02C63Shard01.cutoffTwoSharedDAGTraceR02C63Shard01_partitionSum_eqv
