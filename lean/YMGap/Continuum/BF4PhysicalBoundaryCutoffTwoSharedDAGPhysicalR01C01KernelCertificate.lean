/- Exact genuine physical reflected-kernel entry for sector (1,1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01InterfaceBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorState01Membership

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01KernelCertificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorState01Membership
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01InterfaceBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 1)
      (cutoffTwoSectorLocalZeroStateAt 1) ≈
        cutoffTwoSectorRawKernel 1 1 :=
  centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (cutoffTwoSectorLocalZeroStateAt 1)
    (cutoffTwoSectorLocalZeroStateAt 1)
    cutoffTwoSectorState01_mem cutoffTwoSectorState01_mem
    1 1 (cutoffTwoSectorRawKernel 1 1)
    cutoffTwoPhysicalR01C01Interface_eqv_one
    (by decide) (by decide)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_rawStateAt_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 1)
      (BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt 1) ≈
        cutoffTwoSectorRawKernel 1 1 := by
  simpa only [
    BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt,
    cutoffTwoSectorLocalZeroStateAt] using
    centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_eqv_raw_sharedDAG

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01KernelCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01KernelCertificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_eqv_raw_sharedDAG
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01KernelCertificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_rawStateAt_eqv_raw_sharedDAG
