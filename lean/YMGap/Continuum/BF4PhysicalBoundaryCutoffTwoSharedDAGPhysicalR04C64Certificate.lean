/- End-to-end shared-DAG physical certificate for sector R04C64. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State64
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C64Certificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR04C64Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport64
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C64Certificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR04C64Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoCanonicalSource04TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 4))
      (cutoffTwoCanonicalSourceFactorsAt 4) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport04

theorem cutoffTwoCanonicalSource64TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 64))
      (cutoffTwoCanonicalSourceFactorsAt 64) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport64

def cutoffTwoPhysicalR04C64MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 4) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 64))

def cutoffTwoCanonicalR04C64MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt 4 ++
      cutoffTwoCanonicalSourceFactorsAt 64)

def cutoffTwoCanonicalR04C64IndexedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 57, 58, 73, 69, 61, 62, 70, 64, 74, 75, 71, 30, 55, 38, 55, 35, 32, 55, 40, 56, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 30, 55, 38, 55, 35, 32, 55, 40, 56, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]

def cutoffTwoCanonicalR04C64SortedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 58, 61, 62, 64, 69, 70, 71, 73, 74, 75]

theorem cutoffTwoPhysicalR04C64MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysicalR04C64MatchedFactors
      cutoffTwoCanonicalR04C64MatchedFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource04TransportForSharedDAG
      cutoffTwoCanonicalSource64TransportForSharedDAG)

theorem cutoffTwoCanonicalR04C64Matched_eq_indexed :
    cutoffTwoCanonicalR04C64MatchedFactors =
      cutoffTwoCanonicalR04C64IndexedFactors := by
  rfl

theorem cutoffTwoCanonicalR04C64Sorted_eq_trace :
    cutoffTwoCanonicalR04C64SortedFactors =
      cutoffTwoSharedDAGTraceR04C64Factors0 := by
  rfl

theorem cutoffTwoCanonicalR04C64Matched_perm_trace :
    cutoffTwoCanonicalR04C64MatchedFactors.Perm
      cutoffTwoSharedDAGTraceR04C64Factors0 := by
  rw [cutoffTwoCanonicalR04C64Matched_eq_indexed,
    ← cutoffTwoCanonicalR04C64Sorted_eq_trace]
  unfold cutoffTwoCanonicalR04C64IndexedFactors
    cutoffTwoCanonicalR04C64SortedFactors cutoffTwoCanonicalFactorList
  exact (natListPerm_of_check
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 57, 58, 73, 69, 61, 62, 70, 64, 74, 75, 71, 30, 55, 38, 55, 35, 32, 55, 40, 56, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 30, 55, 38, 55, 35, 32, 55, 40, 56, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 56, 57, 58, 61, 62, 64, 69, 70, 71, 73, 74, 75] (by decide)).map
      cutoffTwoCanonicalFactor

theorem cutoffTwoPhysicalR04C64MatchedPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoPhysicalR04C64MatchedFactors ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR04C64MatchedFactors := by
  simpa [cutoffTwoCanonicalTransportIdentity] using
    scopedFactorPartitionSum_eqv_of_identity_listTransport 2
      (centralFixedFaceIds 0) cutoffTwoPhysicalR04C64MatchedTransport

theorem cutoffTwoPhysicalR04C64Factors_eq_matched :
    cutoffTwoSectorPairInterfaceFactors
        (cutoffTwoSectorLocalZeroStateAt 4)
        (cutoffTwoSectorLocalZeroStateAt 64) =
      cutoffTwoPhysicalR04C64MatchedFactors := by
  simp [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoPhysicalR04C64MatchedFactors, List.append_assoc]

theorem cutoffTwoPhysicalR04C64Interface_eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 4)
          (cutoffTwoSectorLocalZeroStateAt 64)) ≈
      cutoffTwoSharedDAGTraceR04C64ExpectedInterface := by
  rw [cutoffTwoPhysicalR04C64Factors_eq_matched]
  exact Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR04C64MatchedPartitionSum_eqv
    (Q'.eqv_trans _ _ _
      (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR04C64Matched_perm_trace)
      cutoffTwoSharedDAGTraceR04C64eqv_expected)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R04C64_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 4)
      (cutoffTwoSectorLocalZeroStateAt 64) ≈
        cutoffTwoSectorRawKernel 4 64 :=
  centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (cutoffTwoSectorLocalZeroStateAt 4)
    (cutoffTwoSectorLocalZeroStateAt 64)
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    cutoffTwoSharedDAGTraceR04C64ExpectedInterface
    (⟨6561, 18446744073709551615⟩ : Q') (cutoffTwoSectorRawKernel 4 64)
    cutoffTwoPhysicalR04C64Interface_eqv_expected
    (by decide) (by decide)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R04C64_rawStateAt_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 4)
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 64) ≈
        cutoffTwoSectorRawKernel 4 64 := by
  simpa only [
    BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt,
    cutoffTwoSectorLocalZeroStateAt] using
    centralPhysicalReflectedKernel_cutoffTwo_sector_R04C64_eqv_raw_sharedDAG

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR04C64Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR04C64Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R04C64_eqv_raw_sharedDAG
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR04C64Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R04C64_rawStateAt_eqv_raw_sharedDAG
