/-
# Normalized mass and congestion of the all-source inward-mate OS flow

The pointwise edge-capacity theorem assigns to every successful source its
partition-normalized production weight.  Here those demands are summed and
the previously proved production-target congestion is divided by the same
positive physical partition.

The resulting finite flow carries at least `41/425` total demand.  Its first
edge is paid pointwise by the actual normalized OS joint, while all demands
colliding at one compiled target are bounded by

`globalInwardMateTransportCost * targetEdgeUnit`,

and that target unit is itself paid by the second actual OS edge.  Thus the
normalization and finite target multiplicity introduce no hidden
cutoff-dependent constant.

This is a selected-demand two-edge flow.  It is not yet an all-pairs demand
identity, posterior-variance estimate, Poincare inequality, form bound,
spectral gap, beta/lattice-spacing uniformity statement, continuum limit, or
Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem four_mul_reassociate
    (a b c d : Q') :
    (a * (b * c)) * d ≈ (a * b) * (c * d) := by
  refine Q'.eqv_trans _ (a * ((b * c) * d)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (a * (b * (c * d))) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-! ## 1. Exact normalization of the source demand list -/

theorem globalInwardMateAllSourceProductionWeights_eqv_atomWeights
    (K : Nat) (hK : 1 <= K) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) ≈
      listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        (globalInwardMateAllSourceProductionSourceAtoms K hK) := by
  refine Q'.eqv_trans _
    (listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
      (globalCubeInwardMateCertifiedTargetFullSources K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight_eqv_weight
        source
  · exact Q'.eqv_symm
      (globalInwardMateAllSourceProductionSourceAtoms_weight_eqv K hK)

theorem globalInwardMateAllSourceTraffic_eqv_divPos
    (K : Nat) (hK : 1 <= K) :
    listQSum globalInwardMateSourceTraffic
        (globalCubeInwardMateCertifiedTargetFullSources K hK) ≈
      Q'.divPos
        (listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
          (globalCubeInwardMateCertifiedTargetFullSources K hK))
        (slabParametricKPhysicalPartition anchorCoupling K 1)
        (slabParametricKPhysicalPartition_pos (by decide) K 1) := by
  unfold globalInwardMateSourceTraffic Q'.divPos
  exact listQSum_mul_right
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
    (Q'.recipPos
      (slabParametricKPhysicalPartition anchorCoupling K 1)
      (slabParametricKPhysicalPartition_pos (by decide) K 1))
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

/-- The selected normalized OS flow retains the full explicit successful
source fraction. -/
theorem globalInwardMateSuccessRate_le_allSourceTraffic
    (K : Nat) (hK : 1 <= K) :
    Q'.mkPos 41 425 (by decide) <=
      listQSum globalInwardMateSourceTraffic
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  let partition := slabParametricKPhysicalPartition anchorCoupling K 1
  let sourceMass := listQSum
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
    (globalCubeInwardMateCertifiedTargetFullSources K hK)
  have hraw : Q'.mkPos 41 425 (by decide) * partition <= sourceMass := by
    exact Q'.le_trans' _ _ _
      (globalInwardMateAllSourceFraction_partition_le_productionSources K hK)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (globalInwardMateAllSourceProductionWeights_eqv_atomWeights K hK)))
  have hdiv : Q'.mkPos 41 425 (by decide) <=
      Q'.divPos sourceMass partition
        (slabParametricKPhysicalPartition_pos (by decide) K 1) :=
    Q'.le_divPos_of_mul_le sourceMass partition
      (slabParametricKPhysicalPartition_pos (by decide) K 1) hraw
  exact Q'.le_trans' _ _ _ hdiv
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateAllSourceTraffic_eqv_divPos K hK)))

/-! ## 2. Exact normalization of target-fiber congestion -/

theorem globalInwardMateProductionTargetFiber_sourceTraffic_eqv
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateSourceTraffic
        (globalInwardMateProductionTargetFiber representative) ≈
      listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
          (globalInwardMateProductionTargetFiber representative) *
        Q'.recipPos
          (slabParametricKPhysicalPartition anchorCoupling K 1)
          (slabParametricKPhysicalPartition_pos (by decide) K 1) := by
  unfold globalInwardMateSourceTraffic Q'.divPos
  exact listQSum_mul_right
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
    (Q'.recipPos
      (slabParametricKPhysicalPartition anchorCoupling K 1)
      (slabParametricKPhysicalPartition_pos (by decide) K 1))
    (globalInwardMateProductionTargetFiber representative)

/-- Target collisions remain bounded after normalization by exactly the same
cutoff-independent transport cost. -/
theorem globalInwardMateProductionTargetFiber_sourceTraffic_le
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateSourceTraffic
        (globalInwardMateProductionTargetFiber representative) <=
      globalInwardMateTransportCost *
        globalInwardMateTargetEdgeUnit representative := by
  let partition := slabParametricKPhysicalPartition anchorCoupling K 1
  let reciprocal := Q'.recipPos partition
    (slabParametricKPhysicalPartition_pos (by decide) K 1)
  let sourceMass := listQSum
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
    (globalInwardMateProductionTargetFiber representative)
  have hraw :=
    globalInwardMateProductionTargetFiber_sourceWeight_le_sixtyFour_mateCost
      representative
  have hreciprocal : (0 : Q') <= reciprocal :=
    Q'.le_of_lt
      (Q'.recipPos_pos partition
        (slabParametricKPhysicalPartition_pos (by decide) K 1))
  have hscaled : sourceMass * reciprocal <=
      (Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
            representative)) * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hraw hreciprocal
  have hright :
      (Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
            representative)) * reciprocal ≈
      globalInwardMateTransportCost *
        globalInwardMateTargetEdgeUnit representative := by
    change
      (Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
            representative)) * reciprocal ≈
        (Q'.ofNat 64 * anchorInwardMateCost ^ 6) *
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
            representative * reciprocal)
    exact four_mul_reassociate _ _ _ _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (globalInwardMateProductionTargetFiber_sourceTraffic_eqv representative))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- The complete incoming normalized demand at a compiled target is paid by
the actual second OS edge, up to the explicit transport cost. -/
theorem globalInwardMateProductionTargetFiber_sourceTraffic_le_secondEdge
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateSourceTraffic
        (globalInwardMateProductionTargetFiber representative) <=
      globalInwardMateTransportCost *
        centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
            (commonRight representative) (targetLower representative) := by
  exact Q'.le_trans' _ _ _
    (globalInwardMateProductionTargetFiber_sourceTraffic_le representative)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (targetEdgeUnit_le_second_normalizedKernel representative)
      (Q'.le_of_lt globalInwardMateTransportCost_positive))

/-! ## 3. Witness-bearing normalized flow certificate -/

structure GlobalInwardMateAllSourceOSNormalizedFlowCertificate
    (K : Nat) (hK : 1 <= K) : Type where
  sources : List (GlobalCubeInwardMateCertifiedTargetFullSource K hK)
  traffic : GlobalCubeInwardMateCertifiedTargetFullSource K hK -> Q'
  sources_eq : sources = globalCubeInwardMateCertifiedTargetFullSources K hK
  traffic_eq : forall source, traffic source ≈ globalInwardMateSourceTraffic source
  total_lower : Q'.mkPos 41 425 (by decide) <= listQSum traffic sources
  first_capacity : forall source, source ∈ sources ->
    traffic source <=
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (sourceLower source) (commonRight source)
  target_fiber_capacity : forall representative,
    listQSum traffic (globalInwardMateProductionTargetFiber representative) <=
      globalInwardMateTransportCost *
        centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
            (commonRight representative) (targetLower representative)

def globalInwardMateAllSourceOSNormalizedFlowCertificate
    (K : Nat) (hK : 1 <= K) :
    GlobalInwardMateAllSourceOSNormalizedFlowCertificate K hK :=
  { sources := globalCubeInwardMateCertifiedTargetFullSources K hK
    traffic := globalInwardMateSourceTraffic
    sources_eq := rfl
    traffic_eq := fun _ => Q'.eqv_refl _
    total_lower := globalInwardMateSuccessRate_le_allSourceTraffic K hK
    first_capacity := sourceTraffic_le_first_normalizedKernel
    target_fiber_capacity :=
      globalInwardMateProductionTargetFiber_sourceTraffic_le_secondEdge }

#print axioms globalInwardMateAllSourceProductionWeights_eqv_atomWeights
#print axioms globalInwardMateAllSourceTraffic_eqv_divPos
#print axioms globalInwardMateSuccessRate_le_allSourceTraffic
#print axioms globalInwardMateProductionTargetFiber_sourceTraffic_eqv
#print axioms globalInwardMateProductionTargetFiber_sourceTraffic_le
#print axioms globalInwardMateProductionTargetFiber_sourceTraffic_le_secondEdge
#print axioms globalInwardMateAllSourceOSNormalizedFlowCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
