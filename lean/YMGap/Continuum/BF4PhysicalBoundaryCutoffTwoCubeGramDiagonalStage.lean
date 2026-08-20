import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem stage1 :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState centralLowerCubeState ≈
      weightedGram (centralBoundaryChannels 2 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
        (centralHalfAmplitude cutoffTwoHalfCoupling 2 0)
        centralLowerCubeState centralLowerCubeState := by
  have hcube : centralLowerCubeState ∈ centralHalfStates 2 0 :=
    centralLowerCubeState_mem_centralHalfStates (by decide)
  exact centralPhysicalReflectedKernel_eq_weightedGram
    cutoffTwoHalfCoupling hcube hcube

theorem stage2 :
    weightedGram (centralBoundaryChannels 2 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
        (centralHalfAmplitude cutoffTwoHalfCoupling 2 0)
        centralLowerCubeState centralLowerCubeState ≈
      listQSum
        (fun boundary =>
          cutoffTwoCubeGramScalar *
            scopedFactorProduct cutoffTwoCubeInterfaceFactors boundary)
        (boundedEdgeLabellings 2 (centralFixedFaceIds 0)) := by
  unfold weightedGram centralBoundaryChannels
  apply listQSum_congr_on
  intro boundary hboundary
  exact cutoffTwoCubePhysicalGramIntegrand_eqv_scopedProduct
    boundary hboundary

theorem stage3 :
    listQSum
        (fun boundary =>
          cutoffTwoCubeGramScalar *
            scopedFactorProduct cutoffTwoCubeInterfaceFactors boundary)
        (boundedEdgeLabellings 2 (centralFixedFaceIds 0)) ≈
      cutoffTwoCubeGramScalar *
        scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
          cutoffTwoCubeInterfaceFactors := by
  unfold scopedFactorPartitionSum
  exact listQSum_mul_left cutoffTwoCubeGramScalar
    (scopedFactorProduct cutoffTwoCubeInterfaceFactors)
    (boundedEdgeLabellings 2 (centralFixedFaceIds 0))

theorem stage4 :
    cutoffTwoCubeGramScalar *
        scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
          cutoffTwoCubeInterfaceFactors ≈
      cutoffTwoCubeGramScalar * cutoffTwoCubeExpectedInterfaceSum := by
  exact Q'.mul_eqv_congr_left _ _ _
    cutoffTwoCubeInterfacePartitionSum_eqv

theorem stage5 :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState centralLowerCubeState ≈
      cutoffTwoCubeGramScalar * cutoffTwoCubeExpectedInterfaceSum := by
  exact Q'.eqv_trans _ _ _ stage1
    (Q'.eqv_trans _ _ _ stage2
      (Q'.eqv_trans _ _ _ stage3 stage4))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage.stage1
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage.stage2
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage.stage3
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage.stage4
