/- End-to-end shared-DAG physical certificate for sector R26C26. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State26
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C26Certificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR26C26Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport26
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C26Certificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR26C26Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoCanonicalSource26TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 26))
      (cutoffTwoCanonicalSourceFactorsAt 26) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport26

def cutoffTwoPhysicalR26C26MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 26) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 26))

def cutoffTwoCanonicalR26C26MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt 26 ++
      cutoffTwoCanonicalSourceFactorsAt 26)

def cutoffTwoCanonicalR26C26IndexedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 80, 78, 59, 69, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 80, 78, 59, 69, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]

def cutoffTwoCanonicalR26C26SortedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 48, 48, 50, 50, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 59, 66, 66, 69, 69, 71, 71, 72, 72, 74, 74, 76, 76, 77, 77, 78, 78, 80, 80]

theorem cutoffTwoPhysicalR26C26MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysicalR26C26MatchedFactors
      cutoffTwoCanonicalR26C26MatchedFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource26TransportForSharedDAG
      cutoffTwoCanonicalSource26TransportForSharedDAG)

theorem cutoffTwoCanonicalR26C26Matched_eq_indexed :
    cutoffTwoCanonicalR26C26MatchedFactors =
      cutoffTwoCanonicalR26C26IndexedFactors := by
  rfl

theorem cutoffTwoCanonicalR26C26Sorted_eq_trace :
    cutoffTwoCanonicalR26C26SortedFactors =
      cutoffTwoSharedDAGTraceR26C26Factors0 := by
  rfl

theorem cutoffTwoCanonicalR26C26Matched_perm_trace :
    cutoffTwoCanonicalR26C26MatchedFactors.Perm
      cutoffTwoSharedDAGTraceR26C26Factors0 := by
  rw [cutoffTwoCanonicalR26C26Matched_eq_indexed,
    ← cutoffTwoCanonicalR26C26Sorted_eq_trace]
  unfold cutoffTwoCanonicalR26C26IndexedFactors
    cutoffTwoCanonicalR26C26SortedFactors cutoffTwoCanonicalFactorList
  exact (natListPerm_of_check
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 80, 78, 59, 69, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 80, 78, 59, 69, 48, 76, 50, 77, 74, 66, 71, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 48, 48, 50, 50, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 59, 59, 66, 66, 69, 69, 71, 71, 72, 72, 74, 74, 76, 76, 77, 77, 78, 78, 80, 80] (by decide)).map
      cutoffTwoCanonicalFactor

theorem cutoffTwoPhysicalR26C26MatchedPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoPhysicalR26C26MatchedFactors ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR26C26MatchedFactors := by
  simpa [cutoffTwoCanonicalTransportIdentity] using
    scopedFactorPartitionSum_eqv_of_identity_listTransport 2
      (centralFixedFaceIds 0) cutoffTwoPhysicalR26C26MatchedTransport

theorem cutoffTwoPhysicalR26C26Factors_eq_matched :
    cutoffTwoSectorPairInterfaceFactors
        (cutoffTwoSectorLocalZeroStateAt 26)
        (cutoffTwoSectorLocalZeroStateAt 26) =
      cutoffTwoPhysicalR26C26MatchedFactors := by
  simp [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoPhysicalR26C26MatchedFactors, List.append_assoc]

theorem cutoffTwoPhysicalR26C26Interface_eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 26)
          (cutoffTwoSectorLocalZeroStateAt 26)) ≈
      cutoffTwoSharedDAGTraceR26C26ExpectedInterface := by
  rw [cutoffTwoPhysicalR26C26Factors_eq_matched]
  exact Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR26C26MatchedPartitionSum_eqv
    (Q'.eqv_trans _ _ _
      (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR26C26Matched_perm_trace)
      cutoffTwoSharedDAGTraceR26C26eqv_expected)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R26C26_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 26)
      (cutoffTwoSectorLocalZeroStateAt 26) ≈
        cutoffTwoSectorRawKernel 26 26 :=
  centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (cutoffTwoSectorLocalZeroStateAt 26)
    (cutoffTwoSectorLocalZeroStateAt 26)
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    cutoffTwoSharedDAGTraceR26C26ExpectedInterface
    (⟨729, 281474976710655⟩ : Q') (cutoffTwoSectorRawKernel 26 26)
    cutoffTwoPhysicalR26C26Interface_eqv_expected
    (by decide) (by decide)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R26C26_rawStateAt_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 26)
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 26) ≈
        cutoffTwoSectorRawKernel 26 26 := by
  simpa only [
    BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt,
    cutoffTwoSectorLocalZeroStateAt] using
    centralPhysicalReflectedKernel_cutoffTwo_sector_R26C26_eqv_raw_sharedDAG

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR26C26Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR26C26Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R26C26_eqv_raw_sharedDAG
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR26C26Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R26C26_rawStateAt_eqv_raw_sharedDAG
