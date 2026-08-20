/- Complete sparse certificate for nonzero sector entry (1, 1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard05

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem sparseTraceR01C01Terminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        sparseTraceR01C01Factors24 ≈
      sparseTraceR01C01ExpectedInterface := by
  decide

theorem sparseTraceR01C01InterfacePartitionSum_ordered_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        sparseTraceR01C01Factors0 ≈
      sparseTraceR01C01ExpectedInterface := by
  exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ sparseTraceR01C01Shard00_partitionSum_eqv (Q'.eqv_trans _ _ _ sparseTraceR01C01Shard01_partitionSum_eqv (Q'.eqv_trans _ _ _ sparseTraceR01C01Shard02_partitionSum_eqv (Q'.eqv_trans _ _ _ sparseTraceR01C01Shard03_partitionSum_eqv (Q'.eqv_trans _ _ _ sparseTraceR01C01Shard04_partitionSum_eqv (sparseTraceR01C01Shard05_partitionSum_eqv))))))
    sparseTraceR01C01Terminal_partitionSum_eqv_expected

theorem sparseTraceR01C01InterfacePartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        sparseTraceR01C01Factors0 ≈
      sparseTraceR01C01ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct sparseTraceR01C01Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    sparseTraceR01C01InterfacePartitionSum_ordered_eqv

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_eqv_raw :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 1)
      (cutoffTwoSectorLocalZeroStateAt 1) ≈
        cutoffTwoSectorRawKernel 1 1 := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      (cutoffTwoSectorLocalZeroStateAt 1)
      (cutoffTwoSectorLocalZeroStateAt 1)
      (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
      (cutoffTwoSectorLocalZeroStateAt_mem (by decide))) ?_
  exact Q'.eqv_trans _ _ _
    (q_mul_congr
      (show cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt 1) *
          cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt 1) ≈
        sparseTraceR01C01ExpectedLowerPair by decide)
      sparseTraceR01C01InterfacePartitionSum_eqv)
    (show sparseTraceR01C01ExpectedLowerPair *
          sparseTraceR01C01ExpectedInterface ≈
        cutoffTwoSectorRawKernel 1 1 by decide)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_eqv_raw
