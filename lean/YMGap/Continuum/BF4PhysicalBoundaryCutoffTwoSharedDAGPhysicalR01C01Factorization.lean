/- Production-kernel factorization specialized to sector (1,1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorState01Membership

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Factorization

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorState01Membership
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem centralPhysicalReflectedKernel_cutoffTwo_R01C01_factorization :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorLocalZeroStateAt 1)
        (cutoffTwoSectorLocalZeroStateAt 1) ≈
      (cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt 1) *
        cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt 1)) *
        scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
          (cutoffTwoSectorPairInterfaceFactors
            (cutoffTwoSectorLocalZeroStateAt 1)
            (cutoffTwoSectorLocalZeroStateAt 1)) :=
  centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
    (cutoffTwoSectorLocalZeroStateAt 1)
    (cutoffTwoSectorLocalZeroStateAt 1)
    cutoffTwoSectorState01_mem
    cutoffTwoSectorState01_mem

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Factorization

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Factorization.centralPhysicalReflectedKernel_cutoffTwo_R01C01_factorization
