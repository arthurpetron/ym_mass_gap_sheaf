/- Complete cube/cube replay on the genuine 140-factor graph. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardF

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardB
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardC
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardD
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardE
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardF
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem sectorCubeTerminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        sectorCubeFactors24 ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  decide

theorem sectorCubeInterfacePartitionSum_ordered_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        sectorCubeFactors0 ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  exact Q'.eqv_trans _ _ _ sectorCubeShardA_partitionSum_eqv
    (Q'.eqv_trans _ _ _ sectorCubeShardB_partitionSum_eqv
      (Q'.eqv_trans _ _ _ sectorCubeShardC_partitionSum_eqv
        (Q'.eqv_trans _ _ _ sectorCubeShardD_partitionSum_eqv
          (Q'.eqv_trans _ _ _ sectorCubeShardE_partitionSum_eqv
            (Q'.eqv_trans _ _ _ sectorCubeShardF_partitionSum_eqv
              sectorCubeTerminal_partitionSum_eqv_expected)))))

theorem sectorCubeInterfacePartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        sectorCubeFactors0 ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct sectorCubeFactors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    sectorCubeInterfacePartitionSum_ordered_eqv

theorem centralPhysicalReflectedKernel_cutoffTwo_cube_cube_eqv :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState centralLowerCubeState ≈
      ((Q'.mkPos 1 4096 (by decide) : Q') *
        (Q'.mkPos 1 4096 (by decide) : Q')) *
          cutoffTwoCubeExpectedInterfaceSum := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      centralLowerCubeState centralLowerCubeState
      (by simp [cutoffTwoCubeSectorStates])
      (by simp [cutoffTwoCubeSectorStates])) ?_
  exact q_mul_congr
    (q_mul_congr cutoffTwoLowerFaceScalar_cube_eqv
      cutoffTwoLowerFaceScalar_cube_eqv)
    sectorCubeInterfacePartitionSum_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate.sectorCubeInterfacePartitionSum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate.centralPhysicalReflectedKernel_cutoffTwo_cube_cube_eqv
