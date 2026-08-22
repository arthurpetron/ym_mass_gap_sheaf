/- Structural shared-DAG trace R30C47, shard 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C47Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C47Shard02

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C47Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR30C47Step8 : CheckedScopedEliminationStep 2
    23
    (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
    cutoffTwoSharedDAGTraceR30C47Factors8 where
  bucketResult := cutoffTwoSharedDAGBucket0048Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C47Edge8 :
    CheckedReorderedEliminationStep 2 23
      (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
      cutoffTwoSharedDAGTraceR30C47Factors8
      cutoffTwoSharedDAGTraceR30C47Factors9 where
  step := cutoffTwoSharedDAGTraceR30C47Step8
  after_perm := by
    have houtside :
        factorOutside 23
            cutoffTwoSharedDAGTraceR30C47Factors8 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 69, 69, 71, 72, 72, 75, 76, 78, 80, 80, 81, 88, 168] := by
      rfl
    have hids : ([127, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 69, 69, 71, 72, 72, 75, 76, 78, 80, 80, 81, 88, 168]).Perm [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 69, 69, 71, 72, 72, 75, 76, 78, 80, 80, 81, 88, 127, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C47Step8.bucketResult.result ::
        factorOutside 23
          cutoffTwoSharedDAGTraceR30C47Factors8).Perm
        cutoffTwoSharedDAGTraceR30C47Factors9
    rw [houtside]
    change
      (([127, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 69, 69, 71, 72, 72, 75, 76, 78, 80, 80, 81, 88, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 69, 69, 71, 72, 72, 75, 76, 78, 80, 80, 81, 88, 127, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C47Step9 : CheckedScopedEliminationStep 2
    40
    (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
    cutoffTwoSharedDAGTraceR30C47Factors9 where
  bucketResult := cutoffTwoSharedDAGBucket0484Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C47Edge9 :
    CheckedReorderedEliminationStep 2 40
      (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
      cutoffTwoSharedDAGTraceR30C47Factors9
      cutoffTwoSharedDAGTraceR30C47Factors10 where
  step := cutoffTwoSharedDAGTraceR30C47Step9
  after_perm := by
    have houtside :
        factorOutside 40
            cutoffTwoSharedDAGTraceR30C47Factors9 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 127, 168] := by
      rfl
    have hids : ([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 127, 168]).Perm [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C47Step9.bucketResult.result ::
        factorOutside 40
          cutoffTwoSharedDAGTraceR30C47Factors9).Perm
        cutoffTwoSharedDAGTraceR30C47Factors10
    rw [houtside]
    change
      (([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 127, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C47Step10 : CheckedScopedEliminationStep 2
    47
    (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
    cutoffTwoSharedDAGTraceR30C47Factors10 where
  bucketResult := cutoffTwoSharedDAGBucket0010Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C47Edge10 :
    CheckedReorderedEliminationStep 2 47
      (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
      cutoffTwoSharedDAGTraceR30C47Factors10
      cutoffTwoSharedDAGTraceR30C47Factors11 where
  step := cutoffTwoSharedDAGTraceR30C47Step10
  after_perm := by
    have houtside :
        factorOutside 47
            cutoffTwoSharedDAGTraceR30C47Factors10 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168] := by
      rfl
    have hids : ([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 91, 117, 127, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C47Step10.bucketResult.result ::
        factorOutside 47
          cutoffTwoSharedDAGTraceR30C47Factors10).Perm
        cutoffTwoSharedDAGTraceR30C47Factors11
    rw [houtside]
    change
      (([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 91, 117, 127, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR30C47Step11 : CheckedScopedEliminationStep 2
    50
    (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
    cutoffTwoSharedDAGTraceR30C47Factors11 where
  bucketResult := cutoffTwoSharedDAGBucket0011Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR30C47Edge11 :
    CheckedReorderedEliminationStep 2 50
      (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
      cutoffTwoSharedDAGTraceR30C47Factors11
      cutoffTwoSharedDAGTraceR30C47Factors12 where
  step := cutoffTwoSharedDAGTraceR30C47Step11
  after_perm := by
    have houtside :
        factorOutside 50
            cutoffTwoSharedDAGTraceR30C47Factors11 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168] := by
      rfl
    have hids : ([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 92, 117, 127, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR30C47Step11.bucketResult.result ::
        factorOutside 50
          cutoffTwoSharedDAGTraceR30C47Factors11).Perm
        cutoffTwoSharedDAGTraceR30C47Factors12
    rw [houtside]
    change
      (([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 117, 127, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 45, 46, 49, 50, 51, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 63, 71, 72, 72, 75, 76, 78, 80, 80, 92, 117, 127, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR30C47Shard02_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR30C47Factors8 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR30C47Factors12 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
        cutoffTwoSharedDAGTraceR30C47Factors9 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C47Edge8.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
        cutoffTwoSharedDAGTraceR30C47Factors10 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C47Edge9.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
        cutoffTwoSharedDAGTraceR30C47Factors11 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C47Edge10.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR30C47Factors12 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR30C47Edge11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C47Shard02

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C47Shard02.cutoffTwoSharedDAGTraceR30C47Shard02_partitionSum_eqv
