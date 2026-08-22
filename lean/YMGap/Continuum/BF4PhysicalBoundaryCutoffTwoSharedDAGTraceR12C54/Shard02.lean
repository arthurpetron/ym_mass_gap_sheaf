/- Structural shared-DAG trace R12C54, shard 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C54Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C54Shard02

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C54Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR12C54Step8 : CheckedScopedEliminationStep 2
    23
    (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
    cutoffTwoSharedDAGTraceR12C54Factors8 where
  bucketResult := cutoffTwoSharedDAGBucket0025Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C54Edge8 :
    CheckedReorderedEliminationStep 2 23
      (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
      cutoffTwoSharedDAGTraceR12C54Factors8
      cutoffTwoSharedDAGTraceR12C54Factors9 where
  step := cutoffTwoSharedDAGTraceR12C54Step8
  after_perm := by
    have houtside :
        factorOutside 23
            cutoffTwoSharedDAGTraceR12C54Factors8 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 47, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 69, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 81, 88, 168] := by
      rfl
    have hids : ([106, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 47, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 69, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 81, 88, 168]).Perm [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 47, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 69, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 81, 88, 106, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C54Step8.bucketResult.result ::
        factorOutside 23
          cutoffTwoSharedDAGTraceR12C54Factors8).Perm
        cutoffTwoSharedDAGTraceR12C54Factors9
    rw [houtside]
    change
      (([106, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 47, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 69, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 81, 88, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 47, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 69, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 81, 88, 106, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C54Step9 : CheckedScopedEliminationStep 2
    40
    (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
    cutoffTwoSharedDAGTraceR12C54Factors9 where
  bucketResult := cutoffTwoSharedDAGBucket0038Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C54Edge9 :
    CheckedReorderedEliminationStep 2 40
      (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
      cutoffTwoSharedDAGTraceR12C54Factors9
      cutoffTwoSharedDAGTraceR12C54Factors10 where
  step := cutoffTwoSharedDAGTraceR12C54Step9
  after_perm := by
    have houtside :
        factorOutside 40
            cutoffTwoSharedDAGTraceR12C54Factors9 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 168] := by
      rfl
    have hids : ([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 168]).Perm [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C54Step9.bucketResult.result ::
        factorOutside 40
          cutoffTwoSharedDAGTraceR12C54Factors9).Perm
        cutoffTwoSharedDAGTraceR12C54Factors10
    rw [houtside]
    change
      (([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C54Step10 : CheckedScopedEliminationStep 2
    47
    (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
    cutoffTwoSharedDAGTraceR12C54Factors10 where
  bucketResult := cutoffTwoSharedDAGBucket0010Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C54Edge10 :
    CheckedReorderedEliminationStep 2 47
      (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
      cutoffTwoSharedDAGTraceR12C54Factors10
      cutoffTwoSharedDAGTraceR12C54Factors11 where
  step := cutoffTwoSharedDAGTraceR12C54Step10
  after_perm := by
    have houtside :
        factorOutside 47
            cutoffTwoSharedDAGTraceR12C54Factors10 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168] := by
      rfl
    have hids : ([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 91, 106, 117, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C54Step10.bucketResult.result ::
        factorOutside 47
          cutoffTwoSharedDAGTraceR12C54Factors10).Perm
        cutoffTwoSharedDAGTraceR12C54Factors11
    rw [houtside]
    change
      (([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 91, 106, 117, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR12C54Step11 : CheckedScopedEliminationStep 2
    50
    (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
    cutoffTwoSharedDAGTraceR12C54Factors11 where
  bucketResult := cutoffTwoSharedDAGBucket0011Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR12C54Edge11 :
    CheckedReorderedEliminationStep 2 50
      (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
      cutoffTwoSharedDAGTraceR12C54Factors11
      cutoffTwoSharedDAGTraceR12C54Factors12 where
  step := cutoffTwoSharedDAGTraceR12C54Step11
  after_perm := by
    have houtside :
        factorOutside 50
            cutoffTwoSharedDAGTraceR12C54Factors11 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168] := by
      rfl
    have hids : ([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 92, 106, 117, 168] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR12C54Step11.bucketResult.result ::
        factorOutside 50
          cutoffTwoSharedDAGTraceR12C54Factors11).Perm
        cutoffTwoSharedDAGTraceR12C54Factors12
    rw [houtside]
    change
      (([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 106, 117, 168]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 49, 50, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 62, 70, 71, 72, 73, 73, 75, 75, 77, 77, 78, 78, 92, 106, 117, 168]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR12C54Shard02_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR12C54Factors8 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR12C54Factors12 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
        cutoffTwoSharedDAGTraceR12C54Factors9 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C54Edge8.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
        cutoffTwoSharedDAGTraceR12C54Factors10 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C54Edge9.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
        cutoffTwoSharedDAGTraceR12C54Factors11 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C54Edge10.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR12C54Factors12 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR12C54Edge11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C54Shard02

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR12C54Shard02.cutoffTwoSharedDAGTraceR12C54Shard02_partitionSum_eqv
