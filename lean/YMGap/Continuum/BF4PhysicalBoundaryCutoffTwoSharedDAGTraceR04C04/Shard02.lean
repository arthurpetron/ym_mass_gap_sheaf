/- Structural shared-DAG trace R04C04, shard 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C04Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C04Shard02

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C04Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR04C04Step8 : CheckedScopedEliminationStep 2
    23
    (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
    cutoffTwoSharedDAGTraceR04C04Factors8 where
  bucketResult := cutoffTwoSharedDAGBucket0492Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C04Edge8 :
    CheckedReorderedEliminationStep 2 23
      (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
      cutoffTwoSharedDAGTraceR04C04Factors8
      cutoffTwoSharedDAGTraceR04C04Factors9 where
  step := cutoffTwoSharedDAGTraceR04C04Step8
  after_perm := by
    have houtside :
        factorOutside 23
            cutoffTwoSharedDAGTraceR04C04Factors8 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 69, 69, 70, 70, 71, 71, 73, 73, 75, 75, 81, 88, 105] := by
      rfl
    have hids : ([127, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 69, 69, 70, 70, 71, 71, 73, 73, 75, 75, 81, 88, 105]).Perm [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 69, 69, 70, 70, 71, 71, 73, 73, 75, 75, 81, 88, 105, 127] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C04Step8.bucketResult.result ::
        factorOutside 23
          cutoffTwoSharedDAGTraceR04C04Factors8).Perm
        cutoffTwoSharedDAGTraceR04C04Factors9
    rw [houtside]
    change
      (([127, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 69, 69, 70, 70, 71, 71, 73, 73, 75, 75, 81, 88, 105]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 69, 69, 70, 70, 71, 71, 73, 73, 75, 75, 81, 88, 105, 127]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR04C04Step9 : CheckedScopedEliminationStep 2
    40
    (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
    cutoffTwoSharedDAGTraceR04C04Factors9 where
  bucketResult := cutoffTwoSharedDAGBucket0484Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C04Edge9 :
    CheckedReorderedEliminationStep 2 40
      (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
      cutoffTwoSharedDAGTraceR04C04Factors9
      cutoffTwoSharedDAGTraceR04C04Factors10 where
  step := cutoffTwoSharedDAGTraceR04C04Step9
  after_perm := by
    have houtside :
        factorOutside 40
            cutoffTwoSharedDAGTraceR04C04Factors9 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 127] := by
      rfl
    have hids : ([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 127]).Perm [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C04Step9.bucketResult.result ::
        factorOutside 40
          cutoffTwoSharedDAGTraceR04C04Factors9).Perm
        cutoffTwoSharedDAGTraceR04C04Factors10
    rw [houtside]
    change
      (([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 127]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR04C04Step10 : CheckedScopedEliminationStep 2
    47
    (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
    cutoffTwoSharedDAGTraceR04C04Factors10 where
  bucketResult := cutoffTwoSharedDAGBucket0010Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C04Edge10 :
    CheckedReorderedEliminationStep 2 47
      (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
      cutoffTwoSharedDAGTraceR04C04Factors10
      cutoffTwoSharedDAGTraceR04C04Factors11 where
  step := cutoffTwoSharedDAGTraceR04C04Step10
  after_perm := by
    have houtside :
        factorOutside 47
            cutoffTwoSharedDAGTraceR04C04Factors10 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127] := by
      rfl
    have hids : ([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 91, 105, 117, 127] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C04Step10.bucketResult.result ::
        factorOutside 47
          cutoffTwoSharedDAGTraceR04C04Factors10).Perm
        cutoffTwoSharedDAGTraceR04C04Factors11
    rw [houtside]
    change
      (([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 91, 105, 117, 127]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR04C04Step11 : CheckedScopedEliminationStep 2
    50
    (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
    cutoffTwoSharedDAGTraceR04C04Factors11 where
  bucketResult := cutoffTwoSharedDAGBucket0011Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR04C04Edge11 :
    CheckedReorderedEliminationStep 2 50
      (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
      cutoffTwoSharedDAGTraceR04C04Factors11
      cutoffTwoSharedDAGTraceR04C04Factors12 where
  step := cutoffTwoSharedDAGTraceR04C04Step11
  after_perm := by
    have houtside :
        factorOutside 50
            cutoffTwoSharedDAGTraceR04C04Factors11 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127] := by
      rfl
    have hids : ([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 92, 105, 117, 127] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR04C04Step11.bucketResult.result ::
        factorOutside 50
          cutoffTwoSharedDAGTraceR04C04Factors11).Perm
        cutoffTwoSharedDAGTraceR04C04Factors12
    rw [houtside]
    change
      (([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 105, 117, 127]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 58, 58, 62, 62, 64, 64, 70, 70, 71, 71, 73, 73, 75, 75, 92, 105, 117, 127]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR04C04Shard02_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR04C04Factors8 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR04C04Factors12 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
        cutoffTwoSharedDAGTraceR04C04Factors9 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C04Edge8.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
        cutoffTwoSharedDAGTraceR04C04Factors10 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C04Edge9.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
        cutoffTwoSharedDAGTraceR04C04Factors11 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C04Edge10.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR04C04Factors12 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR04C04Edge11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C04Shard02

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C04Shard02.cutoffTwoSharedDAGTraceR04C04Shard02_partitionSum_eqv
