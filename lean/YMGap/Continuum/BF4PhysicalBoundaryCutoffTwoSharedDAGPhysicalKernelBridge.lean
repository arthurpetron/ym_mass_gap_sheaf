/- Reusable bridge from an exact interface certificate to a physical entry. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- The large production factorization theorem is consumed once with abstract
states.  Concrete finite entries need provide only three small exact facts. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (left right : EdgeLabelling)
    (hleft : left ∈ cutoffTwoCubeSectorStates)
    (hright : right ∈ cutoffTwoCubeSectorStates)
    (interfaceValue lowerPair rawValue : Q')
    (hinterface :
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
          (cutoffTwoSectorPairInterfaceFactors left right) ≈
        interfaceValue)
    (hlower :
      cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right ≈
        lowerPair)
    (hraw : lowerPair * interfaceValue ≈ rawValue) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0 left right ≈
      rawValue := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      left right hleft hright)
    (Q'.eqv_trans _ _ _
      (q_mul_congr hlower hinterface)
      hraw)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge.centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
