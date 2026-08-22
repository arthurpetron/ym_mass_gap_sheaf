/- End-to-end shared-DAG physical certificate for sector R58C58. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State58
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR58C58Certificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR58C58Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport58
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR58C58Certificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR58C58Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoCanonicalSource58TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 58))
      (cutoffTwoCanonicalSourceFactorsAt 58) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport58

def cutoffTwoPhysicalR58C58MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 58) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 58))

def cutoffTwoCanonicalR58C58MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt 58 ++
      cutoffTwoCanonicalSourceFactorsAt 58)

def cutoffTwoCanonicalR58C58IndexedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 73, 47, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 73, 47, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]

def cutoffTwoCanonicalR58C58SortedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 44, 45, 45, 47, 47, 48, 48, 50, 50, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 66, 66, 71, 71, 72, 72, 73, 73, 74, 74, 76, 76, 77, 77]

theorem cutoffTwoPhysicalR58C58MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysicalR58C58MatchedFactors
      cutoffTwoCanonicalR58C58MatchedFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource58TransportForSharedDAG
      cutoffTwoCanonicalSource58TransportForSharedDAG)

theorem cutoffTwoCanonicalR58C58Matched_eq_indexed :
    cutoffTwoCanonicalR58C58MatchedFactors =
      cutoffTwoCanonicalR58C58IndexedFactors := by
  rfl

theorem cutoffTwoCanonicalR58C58Sorted_eq_trace :
    cutoffTwoCanonicalR58C58SortedFactors =
      cutoffTwoSharedDAGTraceR58C58Factors0 := by
  rfl

theorem cutoffTwoCanonicalR58C58Matched_perm_trace :
    cutoffTwoCanonicalR58C58MatchedFactors.Perm
      cutoffTwoSharedDAGTraceR58C58Factors0 := by
  rw [cutoffTwoCanonicalR58C58Matched_eq_indexed,
    ← cutoffTwoCanonicalR58C58Sorted_eq_trace]
  unfold cutoffTwoCanonicalR58C58IndexedFactors
    cutoffTwoCanonicalR58C58SortedFactors cutoffTwoCanonicalFactorList
  exact (natListPerm_of_check
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 73, 47, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 73, 47, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 44, 45, 45, 47, 47, 48, 48, 50, 50, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 66, 66, 71, 71, 72, 72, 73, 73, 74, 74, 76, 76, 77, 77] (by decide)).map
      cutoffTwoCanonicalFactor

theorem cutoffTwoPhysicalR58C58MatchedPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoPhysicalR58C58MatchedFactors ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR58C58MatchedFactors := by
  simpa [cutoffTwoCanonicalTransportIdentity] using
    scopedFactorPartitionSum_eqv_of_identity_listTransport 2
      (centralFixedFaceIds 0) cutoffTwoPhysicalR58C58MatchedTransport

theorem cutoffTwoPhysicalR58C58Factors_eq_matched :
    cutoffTwoSectorPairInterfaceFactors
        (cutoffTwoSectorLocalZeroStateAt 58)
        (cutoffTwoSectorLocalZeroStateAt 58) =
      cutoffTwoPhysicalR58C58MatchedFactors := by
  simp [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoPhysicalR58C58MatchedFactors, List.append_assoc]

theorem cutoffTwoPhysicalR58C58Interface_eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 58)
          (cutoffTwoSectorLocalZeroStateAt 58)) ≈
      cutoffTwoSharedDAGTraceR58C58ExpectedInterface := by
  rw [cutoffTwoPhysicalR58C58Factors_eq_matched]
  exact Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR58C58MatchedPartitionSum_eqv
    (Q'.eqv_trans _ _ _
      (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR58C58Matched_perm_trace)
      cutoffTwoSharedDAGTraceR58C58eqv_expected)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R58C58_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 58)
      (cutoffTwoSectorLocalZeroStateAt 58) ≈
        cutoffTwoSectorRawKernel 58 58 :=
  centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (cutoffTwoSectorLocalZeroStateAt 58)
    (cutoffTwoSectorLocalZeroStateAt 58)
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    cutoffTwoSharedDAGTraceR58C58ExpectedInterface
    (⟨6561, 18446744073709551615⟩ : Q') (cutoffTwoSectorRawKernel 58 58)
    cutoffTwoPhysicalR58C58Interface_eqv_expected
    (by decide) (by decide)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R58C58_rawStateAt_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 58)
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 58) ≈
        cutoffTwoSectorRawKernel 58 58 := by
  simpa only [
    BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt,
    cutoffTwoSectorLocalZeroStateAt] using
    centralPhysicalReflectedKernel_cutoffTwo_sector_R58C58_eqv_raw_sharedDAG

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR58C58Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR58C58Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R58C58_eqv_raw_sharedDAG
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR58C58Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R58C58_rawStateAt_eqv_raw_sharedDAG
