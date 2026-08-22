/- Structural shared-DAG trace R00C02, shard 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard02

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR00C02Step8 : CheckedScopedEliminationStep 2
    23
    (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
    cutoffTwoSharedDAGTraceR00C02Factors8 where
  bucketResult := cutoffTwoSharedDAGBucket0025Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR00C02Edge8 :
    CheckedReorderedEliminationStep 2 23
      (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
      cutoffTwoSharedDAGTraceR00C02Factors8
      cutoffTwoSharedDAGTraceR00C02Factors9 where
  step := cutoffTwoSharedDAGTraceR00C02Step8
  after_perm := by
    have houtside :
        factorOutside 23
            cutoffTwoSharedDAGTraceR00C02Factors8 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 69, 70, 71, 72, 81, 88, 105] := by
      rfl
    have hids : ([106, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 69, 70, 71, 72, 81, 88, 105]).Perm [0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 69, 70, 71, 72, 81, 88, 105, 106] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR00C02Step8.bucketResult.result ::
        factorOutside 23
          cutoffTwoSharedDAGTraceR00C02Factors8).Perm
        cutoffTwoSharedDAGTraceR00C02Factors9
    rw [houtside]
    change
      (([106, 0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 69, 70, 71, 72, 81, 88, 105]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 13, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 69, 70, 71, 72, 81, 88, 105, 106]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR00C02Step9 : CheckedScopedEliminationStep 2
    40
    (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
    cutoffTwoSharedDAGTraceR00C02Factors9 where
  bucketResult := cutoffTwoSharedDAGBucket0038Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR00C02Edge9 :
    CheckedReorderedEliminationStep 2 40
      (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
      cutoffTwoSharedDAGTraceR00C02Factors9
      cutoffTwoSharedDAGTraceR00C02Factors10 where
  step := cutoffTwoSharedDAGTraceR00C02Step9
  after_perm := by
    have houtside :
        factorOutside 40
            cutoffTwoSharedDAGTraceR00C02Factors9 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106] := by
      rfl
    have hids : ([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106]).Perm [0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR00C02Step9.bucketResult.result ::
        factorOutside 40
          cutoffTwoSharedDAGTraceR00C02Factors9).Perm
        cutoffTwoSharedDAGTraceR00C02Factors10
    rw [houtside]
    change
      (([117, 0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 15, 16, 17, 20, 21, 22, 23, 28, 33, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR00C02Step10 : CheckedScopedEliminationStep 2
    47
    (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
    cutoffTwoSharedDAGTraceR00C02Factors10 where
  bucketResult := cutoffTwoSharedDAGBucket0010Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR00C02Edge10 :
    CheckedReorderedEliminationStep 2 47
      (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
      cutoffTwoSharedDAGTraceR00C02Factors10
      cutoffTwoSharedDAGTraceR00C02Factors11 where
  step := cutoffTwoSharedDAGTraceR00C02Step10
  after_perm := by
    have houtside :
        factorOutside 47
            cutoffTwoSharedDAGTraceR00C02Factors10 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117] := by
      rfl
    have hids : ([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 91, 105, 106, 117] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR00C02Step10.bucketResult.result ::
        factorOutside 47
          cutoffTwoSharedDAGTraceR00C02Factors10).Perm
        cutoffTwoSharedDAGTraceR00C02Factors11
    rw [houtside]
    change
      (([91, 0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 17, 20, 21, 22, 23, 33, 38, 38, 38, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 91, 105, 106, 117]).map cutoffTwoSharedDAGFactor)
    exact hmapped

def cutoffTwoSharedDAGTraceR00C02Step11 : CheckedScopedEliminationStep 2
    50
    (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
    cutoffTwoSharedDAGTraceR00C02Factors11 where
  bucketResult := cutoffTwoSharedDAGBucket0011Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTraceR00C02Edge11 :
    CheckedReorderedEliminationStep 2 50
      (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
      cutoffTwoSharedDAGTraceR00C02Factors11
      cutoffTwoSharedDAGTraceR00C02Factors12 where
  step := cutoffTwoSharedDAGTraceR00C02Step11
  after_perm := by
    have houtside :
        factorOutside 50
            cutoffTwoSharedDAGTraceR00C02Factors11 =
          cutoffTwoSharedDAGFactorList [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117] := by
      rfl
    have hids : ([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117]).Perm [0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 92, 105, 106, 117] :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTraceR00C02Step11.bucketResult.result ::
        factorOutside 50
          cutoffTwoSharedDAGTraceR00C02Factors11).Perm
        cutoffTwoSharedDAGTraceR00C02Factors12
    rw [houtside]
    change
      (([92, 0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 105, 106, 117]).map cutoffTwoSharedDAGFactor).Perm
        (([0, 1, 3, 4, 6, 9, 14, 16, 20, 21, 22, 23, 33, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 57, 58, 59, 62, 64, 66, 70, 71, 72, 92, 105, 106, 117]).map cutoffTwoSharedDAGFactor)
    exact hmapped

theorem cutoffTwoSharedDAGTraceR00C02Shard02_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        cutoffTwoSharedDAGTraceR00C02Factors8 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR00C02Factors12 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
        cutoffTwoSharedDAGTraceR00C02Factors9 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR00C02Edge8.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
        cutoffTwoSharedDAGTraceR00C02Factors10 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR00C02Edge9.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
        cutoffTwoSharedDAGTraceR00C02Factors11 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR00C02Edge10.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        cutoffTwoSharedDAGTraceR00C02Factors12 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTraceR00C02Edge11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard02

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard02.cutoffTwoSharedDAGTraceR00C02Shard02_partitionSum_eqv
