/- Structural shared-DAG trace R28C60, shard 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C60Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C60Shard01

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C60Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR28C60Step4 : CheckedScopedEliminationStep 2
    31
    (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
    cutoffTwoSharedDAGTraceR28C60Factors4 where
  bucketResult := cutoffTwoSharedDAGBucket0004Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C60Edge4 :
    CheckedReorderedEliminationStep 2 31
      (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
      cutoffTwoSharedDAGTraceR28C60Factors4
      cutoffTwoSharedDAGTraceR28C60Factors5 where
  step := cutoffTwoSharedDAGTraceR28C60Step4
  after_perm := by
    have houtside :
        factorOutside 31
            cutoffTwoSharedDAGTraceR28C60Factors4 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84] := by
      rfl
    have hids : ([85, 0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84]).Perm [0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 85] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C60Step4.bucketResult.result ::
        factorOutside 31
          cutoffTwoSharedDAGTraceR28C60Factors4).Perm
        cutoffTwoSharedDAGTraceR28C60Factors5
    rw [houtside]
    change
      (([85, 0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 35, 35, 35, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 85]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR28C60Step5 : CheckedScopedEliminationStep 2
    32
    (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
    cutoffTwoSharedDAGTraceR28C60Factors5 where
  bucketResult := cutoffTwoSharedDAGBucket0005Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C60Edge5 :
    CheckedReorderedEliminationStep 2 32
      (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
      cutoffTwoSharedDAGTraceR28C60Factors5
      cutoffTwoSharedDAGTraceR28C60Factors6 where
  step := cutoffTwoSharedDAGTraceR28C60Step5
  after_perm := by
    have houtside :
        factorOutside 32
            cutoffTwoSharedDAGTraceR28C60Factors5 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84] := by
      rfl
    have hids : ([86, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C60Step5.bucketResult.result ::
        factorOutside 32
          cutoffTwoSharedDAGTraceR28C60Factors5).Perm
        cutoffTwoSharedDAGTraceR28C60Factors6
    rw [houtside]
    change
      (([86, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 31, 33, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR28C60Step6 : CheckedScopedEliminationStep 2
    56
    (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
    cutoffTwoSharedDAGTraceR28C60Factors6 where
  bucketResult := cutoffTwoSharedDAGBucket0006Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C60Edge6 :
    CheckedReorderedEliminationStep 2 56
      (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
      cutoffTwoSharedDAGTraceR28C60Factors6
      cutoffTwoSharedDAGTraceR28C60Factors7 where
  step := cutoffTwoSharedDAGTraceR28C60Step6
  after_perm := by
    have houtside :
        factorOutside 56
            cutoffTwoSharedDAGTraceR28C60Factors6 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86] := by
      rfl
    have hids : ([87, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86, 87] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C60Step6.bucketResult.result ::
        factorOutside 56
          cutoffTwoSharedDAGTraceR28C60Factors6).Perm
        cutoffTwoSharedDAGTraceR28C60Factors7
    rw [houtside]
    change
      (([87, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86, 87]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR28C60Step7 : CheckedScopedEliminationStep 2
    58
    (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
    cutoffTwoSharedDAGTraceR28C60Factors7 where
  bucketResult := cutoffTwoSharedDAGBucket0007Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR28C60Edge7 :
    CheckedReorderedEliminationStep 2 58
      (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
      cutoffTwoSharedDAGTraceR28C60Factors7
      cutoffTwoSharedDAGTraceR28C60Factors8 where
  step := cutoffTwoSharedDAGTraceR28C60Step7
  after_perm := by
    have houtside :
        factorOutside 58
            cutoffTwoSharedDAGTraceR28C60Factors7 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86] := by
      rfl
    have hids : ([88, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86]).Perm [0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86, 88] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR28C60Step7.bucketResult.result ::
        factorOutside 58
          cutoffTwoSharedDAGTraceR28C60Factors7).Perm
        cutoffTwoSharedDAGTraceR28C60Factors8
    rw [houtside]
    change
      (([88, 0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 8, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 50, 50, 52, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 69, 71, 71, 73, 75, 75, 76, 76, 77, 77, 78, 80, 81, 82, 84, 86, 88]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR28C60Shard01_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        cutoffTwoSharedDAGTraceR28C60Factors4 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR28C60Factors8 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
        cutoffTwoSharedDAGTraceR28C60Factors5 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C60Edge4.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
        cutoffTwoSharedDAGTraceR28C60Factors6 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C60Edge5.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
        cutoffTwoSharedDAGTraceR28C60Factors7 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C60Edge6.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR28C60Factors8 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR28C60Edge7.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C60Shard01

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C60Shard01.cutoffTwoSharedDAGTraceR28C60Shard01_partitionSum_eqv
