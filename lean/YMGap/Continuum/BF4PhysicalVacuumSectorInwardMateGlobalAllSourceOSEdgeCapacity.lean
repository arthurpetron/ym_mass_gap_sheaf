/-
# Quantitative OS edge capacity of every all-source inward-mate path

Every successful inward-mate source already supplies a supported two-edge
path in the physical conditional kernel.  This module keeps the normalization
at the symmetric-joint level, where the reversible edge capacity is simply
the partition-normalized reflected kernel.

The source production witness is one nonnegative term of the exact retained
fine-intertwiner fiber, hence its weight is bounded by the complete source
physical term.  The common boundary channel then embeds that term as one
nonnegative summand of the raw OS kernel.  The same argument applies to the
target production witness.  Division by the common positive physical
partition therefore gives literal lower bounds on both joint edge capacities.

This is a quantitative edge-capacity splice, not yet an all-pairs flow,
posterior-variance estimate, form bound, spectral gap, beta/lattice-spacing
uniformity statement, continuum limit, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathSupport
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathSupport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A -> Q')
    (hvalue : forall item, (0 : Q') <= value item) :
    forall (items : List A) {selected : A},
      selected ∈ items -> value selected <= listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe :
            listQSum value tail <= value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

/-! ## 1. One production witness is bounded by its physical term -/

theorem sourceProductionWeight_le_physicalTerm
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        source <=
      slabParametricKPhysicalTerm anchorCoupling K 1 source.physical := by
  let D := globalInwardMateAnchorSlabData K
  have hterm :
      retainedFineIntertwinerPhysicalFiberWeight D source.physical
          (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw
            source) <=
        D.physicalTerm source.physical := by
    exact Q'.le_trans' _ _ _
      (listQSum_member_le_nonnegative_local
        (retainedFineIntertwinerPhysicalFiberWeight D source.physical)
        (fun assignment =>
          retainedFineIntertwinerPhysicalFiberWeight_nonnegative
            (by decide) K 0 source.physical assignment)
        (slabFineFusionWitnesses D source.physical)
        (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem_allSources
          source hsource))
      (Q'.le_of_eqv
        (retainedFineIntertwinerPhysicalFiberWeight_total D source.physical))
  simpa [GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight,
    slabExpandedFineSourceWeight,
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom,
    D, globalInwardMateAnchorSlabData, SlabPhysicalData.physicalTerm,
    SlabPhysicalData.extent, centralExtent] using hterm

theorem targetProductionWeight_le_physicalTerm
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
        source <=
      slabParametricKPhysicalTerm anchorCoupling K 1
        (targetPhysical source) := by
  let D := globalInwardMateAnchorSlabData K
  have hterm :
      retainedFineIntertwinerPhysicalFiberWeight D (targetPhysical source)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw
            source) <=
        D.physicalTerm (targetPhysical source) := by
    exact Q'.le_trans' _ _ _
      (listQSum_member_le_nonnegative_local
        (retainedFineIntertwinerPhysicalFiberWeight D (targetPhysical source))
        (fun assignment =>
          retainedFineIntertwinerPhysicalFiberWeight_nonnegative
            (by decide) K 0 (targetPhysical source) assignment)
        (slabFineFusionWitnesses D (targetPhysical source))
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem_allSources
          source))
      (Q'.le_of_eqv
        (retainedFineIntertwinerPhysicalFiberWeight_total
          D (targetPhysical source)))
  simpa [GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight,
    slabExpandedFineSourceWeight,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom,
    D, globalInwardMateAnchorSlabData, SlabPhysicalData.physicalTerm,
    SlabPhysicalData.extent, centralExtent] using hterm

/-! ## 2. The selected boundary embeds those weights in the raw OS kernel -/

theorem sourceProductionWeight_le_sourceLower_commonRight_rawKernel
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        source <=
      centralPhysicalReflectedKernel
        anchorCoupling K 0 (sourceLower source) (commonRight source) := by
  apply Q'.le_trans' _ _ _
    (sourceProductionWeight_le_physicalTerm source hsource)
  unfold centralPhysicalReflectedKernel
  have hmember := listQSum_member_le_nonnegative_local
    (fun boundary =>
      slabParametricKPhysicalTerm anchorCoupling K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (sourceLower source) boundary (commonRight source)))
    (fun boundary =>
      slabParametricKPhysicalTerm_nonnegative
        (by decide) K (centralExtent 0)
          (assembleReflectedSlabLabelling 0
            (sourceLower source) boundary (commonRight source)))
    (centralBoundaryChannels K 0)
    (commonBoundary_mem source)
  change
    slabParametricKPhysicalTerm anchorCoupling K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (sourceLower source) (commonBoundary source) (commonRight source)) <=
      _ at hmember
  rw [assemble_source_path source] at hmember
  simpa [centralExtent] using hmember

theorem targetProductionWeight_le_targetLower_commonRight_rawKernel
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
        source <=
      centralPhysicalReflectedKernel
        anchorCoupling K 0 (targetLower source) (commonRight source) := by
  apply Q'.le_trans' _ _ _
    (targetProductionWeight_le_physicalTerm source)
  unfold centralPhysicalReflectedKernel
  have hmember := listQSum_member_le_nonnegative_local
    (fun boundary =>
      slabParametricKPhysicalTerm anchorCoupling K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (targetLower source) boundary (commonRight source)))
    (fun boundary =>
      slabParametricKPhysicalTerm_nonnegative
        (by decide) K (centralExtent 0)
          (assembleReflectedSlabLabelling 0
            (targetLower source) boundary (commonRight source)))
    (centralBoundaryChannels K 0)
    (commonBoundary_mem source)
  change
    slabParametricKPhysicalTerm anchorCoupling K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (targetLower source) (commonBoundary source) (commonRight source)) <=
      _ at hmember
  rw [assemble_target_path source] at hmember
  simpa [centralExtent] using hmember

/-! ## 3. Partition-normalized joint edge capacities -/

def globalInwardMateSourceTraffic
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  Q'.divPos
    (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight source)
    (slabParametricKPhysicalPartition anchorCoupling K 1)
    (slabParametricKPhysicalPartition_pos (by decide) K 1)

def globalInwardMateTargetEdgeUnit
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  Q'.divPos
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight source)
    (slabParametricKPhysicalPartition anchorCoupling K 1)
    (slabParametricKPhysicalPartition_pos (by decide) K 1)

theorem sourceTraffic_le_first_normalizedKernel
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    globalInwardMateSourceTraffic source <=
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (sourceLower source) (commonRight source) := by
  unfold globalInwardMateSourceTraffic
    centralNormalizedPhysicalReflectedKernel Q'.divPos
  simpa [centralExtent] using
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (sourceProductionWeight_le_sourceLower_commonRight_rawKernel
        source hsource)
      (Q'.le_of_lt
        (Q'.recipPos_pos
          (slabParametricKPhysicalPartition anchorCoupling K 1)
          (slabParametricKPhysicalPartition_pos (by decide) K 1))))

theorem targetEdgeUnit_le_second_normalizedKernel
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateTargetEdgeUnit source <=
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (commonRight source) (targetLower source) := by
  have hforward : globalInwardMateTargetEdgeUnit source <=
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (targetLower source) (commonRight source) := by
    unfold globalInwardMateTargetEdgeUnit
      centralNormalizedPhysicalReflectedKernel Q'.divPos
    simpa [centralExtent] using
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (targetProductionWeight_le_targetLower_commonRight_rawKernel source)
        (Q'.le_of_lt
          (Q'.recipPos_pos
            (slabParametricKPhysicalPartition anchorCoupling K 1)
            (slabParametricKPhysicalPartition_pos (by decide) K 1))))
  exact Q'.le_trans' _ _ _ hforward
    (Q'.le_of_eqv
      (centralNormalizedPhysicalReflectedKernel_symm
        (w := anchorCoupling) (hw := by decide)
        (targetLower_mem source) (commonRight_mem source)))

/-! ## 4. Witness-bearing edge-capacity certificate -/

structure GlobalInwardMateAllSourceOSEdgeCapacityCertificate
    (K : Nat) (hK : 1 <= K)
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) : Type where
  traffic : Q'
  targetUnit : Q'
  traffic_eq : traffic ≈ globalInwardMateSourceTraffic source
  targetUnit_eq : targetUnit ≈ globalInwardMateTargetEdgeUnit source
  first_capacity : traffic <=
    centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0
        (sourceLower source) (commonRight source)
  second_capacity : targetUnit <=
    centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0
        (commonRight source) (targetLower source)
  support : GlobalInwardMateAllSourceSupportedOSPathCertificate
    K hK source hsource

def globalInwardMateAllSourceOSEdgeCapacityCertificate
    (K : Nat) (hK : 1 <= K)
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalInwardMateAllSourceOSEdgeCapacityCertificate
      K hK source hsource :=
  { traffic := globalInwardMateSourceTraffic source
    targetUnit := globalInwardMateTargetEdgeUnit source
    traffic_eq := Q'.eqv_refl _
    targetUnit_eq := Q'.eqv_refl _
    first_capacity := sourceTraffic_le_first_normalizedKernel source hsource
    second_capacity := targetEdgeUnit_le_second_normalizedKernel source
    support := globalInwardMateAllSourceSupportedOSPathCertificate
      K hK source hsource }

#print axioms sourceProductionWeight_le_physicalTerm
#print axioms targetProductionWeight_le_physicalTerm
#print axioms sourceProductionWeight_le_sourceLower_commonRight_rawKernel
#print axioms targetProductionWeight_le_targetLower_commonRight_rawKernel
#print axioms globalInwardMateSourceTraffic
#print axioms globalInwardMateTargetEdgeUnit
#print axioms sourceTraffic_le_first_normalizedKernel
#print axioms targetEdgeUnit_le_second_normalizedKernel
#print axioms globalInwardMateAllSourceOSEdgeCapacityCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
