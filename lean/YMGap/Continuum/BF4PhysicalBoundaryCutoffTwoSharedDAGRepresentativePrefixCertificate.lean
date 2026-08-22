/- Four-entry pilot for assembling shared-DAG physical equalities by code. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C00Certificate
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C01Certificate
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C02Certificate
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01KernelCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativePrefixCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGRepresentativePrefix : List CutoffTwoSectorPair :=
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩]

theorem cutoffTwoSharedDAGRepresentativeR00C00_checked :
    cutoffTwoSectorRepresentativePhysicalStatement ⟨0, 0⟩ :=
  BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C00Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R00C00_rawStateAt_eqv_raw_sharedDAG

theorem cutoffTwoSharedDAGRepresentativeR00C01_checked :
    cutoffTwoSectorRepresentativePhysicalStatement ⟨0, 1⟩ :=
  BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C01Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R00C01_rawStateAt_eqv_raw_sharedDAG

theorem cutoffTwoSharedDAGRepresentativeR00C02_checked :
    cutoffTwoSectorRepresentativePhysicalStatement ⟨0, 2⟩ :=
  BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C02Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R00C02_rawStateAt_eqv_raw_sharedDAG

theorem cutoffTwoSharedDAGRepresentativeR01C01_checked :
    cutoffTwoSectorRepresentativePhysicalStatement ⟨1, 1⟩ :=
  BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01KernelCertificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_rawStateAt_eqv_raw_sharedDAG

theorem cutoffTwoSharedDAGRepresentativePrefix_checked
    (pair : CutoffTwoSectorPair)
    (hpair : pair ∈ cutoffTwoSharedDAGRepresentativePrefix) :
    cutoffTwoSectorRepresentativePhysicalStatement pair := by
  simp only [cutoffTwoSharedDAGRepresentativePrefix,
    List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with hpair | hpair | hpair | hpair
  · exact cutoffTwoSectorRepresentativePhysicalStatement_of_eq hpair
      cutoffTwoSharedDAGRepresentativeR00C00_checked
  · exact cutoffTwoSectorRepresentativePhysicalStatement_of_eq hpair
      cutoffTwoSharedDAGRepresentativeR00C01_checked
  · exact cutoffTwoSectorRepresentativePhysicalStatement_of_eq hpair
      cutoffTwoSharedDAGRepresentativeR00C02_checked
  · exact cutoffTwoSectorRepresentativePhysicalStatement_of_eq hpair
      cutoffTwoSharedDAGRepresentativeR01C01_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativePrefixCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativePrefixCertificate.cutoffTwoSharedDAGRepresentativePrefix_checked
