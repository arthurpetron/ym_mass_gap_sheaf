/- End-to-end shared-DAG physical certificate for sector R28C61. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State28
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransports.State61
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C61Certificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR28C61Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport28
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport61
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C61Certificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR28C61Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoCanonicalSource28TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 28))
      (cutoffTwoCanonicalSourceFactorsAt 28) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport28

theorem cutoffTwoCanonicalSource61TransportForSharedDAG :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 61))
      (cutoffTwoCanonicalSourceFactorsAt 61) := by
  simpa [cutoffTwoCanonicalTransportIdentity,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalIdentity] using
    cutoffTwoCanonicalSourceTransport61

def cutoffTwoPhysicalR28C61MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 28) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 61))

def cutoffTwoCanonicalR28C61MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt 28 ++
      cutoffTwoCanonicalSourceFactorsAt 61)

def cutoffTwoCanonicalR28C61IndexedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 80, 78, 73, 69, 48, 76, 50, 77, 52, 75, 71, 30, 55, 38, 55, 35, 32, 55, 40, 56, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 73, 69, 48, 49, 70, 51, 74, 75, 71, 30, 55, 38, 55, 35, 32, 55, 40, 68, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55]

def cutoffTwoCanonicalR28C61SortedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 48, 48, 49, 50, 51, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 69, 69, 70, 71, 71, 73, 73, 74, 75, 75, 76, 77, 78, 80]

theorem cutoffTwoPhysicalR28C61MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysicalR28C61MatchedFactors
      cutoffTwoCanonicalR28C61MatchedFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource28TransportForSharedDAG
      cutoffTwoCanonicalSource61TransportForSharedDAG)

theorem cutoffTwoCanonicalR28C61Matched_eq_indexed :
    cutoffTwoCanonicalR28C61MatchedFactors =
      cutoffTwoCanonicalR28C61IndexedFactors := by
  rfl

theorem cutoffTwoCanonicalR28C61Sorted_eq_trace :
    cutoffTwoCanonicalR28C61SortedFactors =
      cutoffTwoSharedDAGTraceR28C61Factors0 := by
  rfl

theorem cutoffTwoCanonicalR28C61Matched_perm_trace :
    cutoffTwoCanonicalR28C61MatchedFactors.Perm
      cutoffTwoSharedDAGTraceR28C61Factors0 := by
  rw [cutoffTwoCanonicalR28C61Matched_eq_indexed,
    ← cutoffTwoCanonicalR28C61Sorted_eq_trace]
  unfold cutoffTwoCanonicalR28C61IndexedFactors
    cutoffTwoCanonicalR28C61SortedFactors cutoffTwoCanonicalFactorList
  exact (natListPerm_of_check
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 80, 78, 73, 69, 48, 76, 50, 77, 52, 75, 71, 30, 55, 38, 55, 35, 32, 55, 40, 56, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 44, 45, 73, 69, 48, 49, 70, 51, 74, 75, 71, 30, 55, 38, 55, 35, 32, 55, 40, 68, 34, 55, 55, 42, 55, 43, 55, 55, 36, 39, 55, 37, 55, 41, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 44, 45, 48, 48, 49, 50, 51, 52, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 56, 68, 69, 69, 70, 71, 71, 73, 73, 74, 75, 75, 76, 77, 78, 80] (by decide)).map
      cutoffTwoCanonicalFactor

theorem cutoffTwoPhysicalR28C61MatchedPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoPhysicalR28C61MatchedFactors ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR28C61MatchedFactors := by
  simpa [cutoffTwoCanonicalTransportIdentity] using
    scopedFactorPartitionSum_eqv_of_identity_listTransport 2
      (centralFixedFaceIds 0) cutoffTwoPhysicalR28C61MatchedTransport

theorem cutoffTwoPhysicalR28C61Factors_eq_matched :
    cutoffTwoSectorPairInterfaceFactors
        (cutoffTwoSectorLocalZeroStateAt 28)
        (cutoffTwoSectorLocalZeroStateAt 61) =
      cutoffTwoPhysicalR28C61MatchedFactors := by
  simp [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoPhysicalR28C61MatchedFactors, List.append_assoc]

theorem cutoffTwoPhysicalR28C61Interface_eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 28)
          (cutoffTwoSectorLocalZeroStateAt 61)) ≈
      cutoffTwoSharedDAGTraceR28C61ExpectedInterface := by
  rw [cutoffTwoPhysicalR28C61Factors_eq_matched]
  exact Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR28C61MatchedPartitionSum_eqv
    (Q'.eqv_trans _ _ _
      (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR28C61Matched_perm_trace)
      cutoffTwoSharedDAGTraceR28C61eqv_expected)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R28C61_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 28)
      (cutoffTwoSectorLocalZeroStateAt 61) ≈
        cutoffTwoSectorRawKernel 28 61 :=
  centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (cutoffTwoSectorLocalZeroStateAt 28)
    (cutoffTwoSectorLocalZeroStateAt 61)
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    cutoffTwoSharedDAGTraceR28C61ExpectedInterface
    (⟨6561, 18446744073709551615⟩ : Q') (cutoffTwoSectorRawKernel 28 61)
    cutoffTwoPhysicalR28C61Interface_eqv_expected
    (by decide) (by decide)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R28C61_rawStateAt_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 28)
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 61) ≈
        cutoffTwoSectorRawKernel 28 61 := by
  simpa only [
    BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt,
    cutoffTwoSectorLocalZeroStateAt] using
    centralPhysicalReflectedKernel_cutoffTwo_sector_R28C61_eqv_raw_sharedDAG

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR28C61Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR28C61Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R28C61_eqv_raw_sharedDAG
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR28C61Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R28C61_rawStateAt_eqv_raw_sharedDAG
