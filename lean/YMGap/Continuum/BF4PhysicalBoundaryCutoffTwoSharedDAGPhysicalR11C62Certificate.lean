/- End-to-end shared-DAG physical certificate for sector R11C62. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State62
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Certificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR11C62Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport11
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport62
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Certificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR11C62Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoCanonicalSource11TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 11))
      (cutoffTwoCanonicalSourceFactorsAt 11) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport11

theorem cutoffTwoCanonicalSource62TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 62))
      (cutoffTwoCanonicalSourceFactorsAt 62) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport62

def cutoffTwoPhysicalR11C62MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 11) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 62))

def cutoffTwoCanonicalR11C62MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt 11 ++
      cutoffTwoCanonicalSourceFactorsAt 62)

def cutoffTwoCanonicalR11C62IndexedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 57, 78, 73, 60, 79, 62, 63, 77, 52, 75, 67, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 73, 47, 48, 49, 50, 51, 74, 75, 54, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]

def cutoffTwoCanonicalR11C62SortedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 47, 48, 49, 50, 51, 52, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 60, 62, 63, 67, 72, 72, 73, 73, 74, 75, 75, 77, 78, 79]

theorem cutoffTwoPhysicalR11C62MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysicalR11C62MatchedFactors
      cutoffTwoCanonicalR11C62MatchedFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource11TransportForSharedDAG
      cutoffTwoCanonicalSource62TransportForSharedDAG)

theorem cutoffTwoCanonicalR11C62Matched_eq_indexed :
    cutoffTwoCanonicalR11C62MatchedFactors =
      cutoffTwoCanonicalR11C62IndexedFactors := by
  rfl

theorem cutoffTwoCanonicalR11C62Sorted_eq_trace :
    cutoffTwoCanonicalR11C62SortedFactors =
      cutoffTwoSharedDAGTraceR11C62Factors0 := by
  rfl

theorem cutoffTwoCanonicalR11C62Matched_perm_trace :
    cutoffTwoCanonicalR11C62MatchedFactors.Perm
      cutoffTwoSharedDAGTraceR11C62Factors0 := by
  rw [cutoffTwoCanonicalR11C62Matched_eq_indexed,
    ← cutoffTwoCanonicalR11C62Sorted_eq_trace]
  unfold cutoffTwoCanonicalR11C62IndexedFactors
    cutoffTwoCanonicalR11C62SortedFactors cutoffTwoCanonicalFactorList
  exact (natListPerm_of_check
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 57, 78, 73, 60, 79, 62, 63, 77, 52, 75, 67, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 73, 47, 48, 49, 50, 51, 74, 75, 54, 30, 55, 38, 55, 35, 32, 55, 40, 72, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 47, 48, 49, 50, 51, 52, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 60, 62, 63, 67, 72, 72, 73, 73, 74, 75, 75, 77, 78, 79] (by decide)).map
      cutoffTwoCanonicalFactor

theorem cutoffTwoPhysicalR11C62MatchedPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoPhysicalR11C62MatchedFactors ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR11C62MatchedFactors := by
  simpa [cutoffTwoCanonicalTransportIdentity] using
    scopedFactorPartitionSum_eqv_of_identity_listTransport 2
      (centralFixedFaceIds 0) cutoffTwoPhysicalR11C62MatchedTransport

theorem cutoffTwoPhysicalR11C62Factors_eq_matched :
    cutoffTwoSectorPairInterfaceFactors
        (cutoffTwoSectorLocalZeroStateAt 11)
        (cutoffTwoSectorLocalZeroStateAt 62) =
      cutoffTwoPhysicalR11C62MatchedFactors := by
  simp [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoPhysicalR11C62MatchedFactors, List.append_assoc]

theorem cutoffTwoPhysicalR11C62Interface_eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 11)
          (cutoffTwoSectorLocalZeroStateAt 62)) ≈
      cutoffTwoSharedDAGTraceR11C62ExpectedInterface := by
  rw [cutoffTwoPhysicalR11C62Factors_eq_matched]
  exact Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR11C62MatchedPartitionSum_eqv
    (Q'.eqv_trans _ _ _
      (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR11C62Matched_perm_trace)
      cutoffTwoSharedDAGTraceR11C62eqv_expected)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R11C62_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 11)
      (cutoffTwoSectorLocalZeroStateAt 62) ≈
        cutoffTwoSectorRawKernel 11 62 :=
  centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (cutoffTwoSectorLocalZeroStateAt 11)
    (cutoffTwoSectorLocalZeroStateAt 62)
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    cutoffTwoSharedDAGTraceR11C62ExpectedInterface
    (⟨2187, 72057594037927935⟩ : Q') (cutoffTwoSectorRawKernel 11 62)
    cutoffTwoPhysicalR11C62Interface_eqv_expected
    (by decide) (by decide)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R11C62_rawStateAt_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 11)
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 62) ≈
        cutoffTwoSectorRawKernel 11 62 := by
  simpa only [
    BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt,
    cutoffTwoSectorLocalZeroStateAt] using
    centralPhysicalReflectedKernel_cutoffTwo_sector_R11C62_eqv_raw_sharedDAG

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR11C62Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR11C62Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R11C62_eqv_raw_sharedDAG
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR11C62Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R11C62_rawStateAt_eqv_raw_sharedDAG
