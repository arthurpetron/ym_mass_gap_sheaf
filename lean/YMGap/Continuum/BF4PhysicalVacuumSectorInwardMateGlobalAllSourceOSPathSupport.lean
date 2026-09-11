/-
# Positive OS support of every all-source inward-mate path

The preceding geometry module writes every successful source--mate pair as
two different lower-half states joined through one common reflected-upper
state and one common boundary channel.  Here the production assignments at
the two full-slab endpoints are used for their precise analytic purpose:
they make both assembled BF4 summands strictly positive.

Each positive summand is a displayed member of the boundary-channel sum
defining the raw Osterwalder--Schrader kernel.  Positivity survives partition
normalization and row conditioning.  Hence every successful source carries a
literal length-two path in the actual physical conditional kernel,

`sourceLower -> commonRight -> targetLower`,

with distinct endpoints and all three vertices in the retained positive-row
carrier.

This proves support, not a quantitative lower bound on either transition.
No edge-load comparison, posterior variance, form bound, spectral gap,
beta/lattice-spacing uniformity, continuum limit, or Clay theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. One accepted global assignment makes its physical term positive -/

private theorem qOfNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ predecessor => exact Q'.ofNat_succ_pos predecessor

private theorem slabPhysicalTerm_pos_of_fusionWitness
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (physical : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded D.cutoff D.extent physical)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical) :
    (0 : Q') < D.physicalTerm physical := by
  have hface : (0 : Q') < slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent physical :=
    slabParametricKPhysicalFaceFactor_pos_of_bounded
      D hcoupling physical hbounded
  have hlength : 0 < (slabFineFusionWitnesses D physical).length :=
    List.length_pos_of_mem hassignment
  have hmultiplicity : 0 < slabExplicitLinkMultiplicityProduct
      D.cutoff D.extent physical := by
    rwa [slabFineFusionWitnesses_length] at hlength
  unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
  exact Q'.mul_pos hface (qOfNat_pos_of_pos hmultiplicity)

theorem sourcePhysicalTerm_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    (0 : Q') <
      slabParametricKPhysicalTerm anchorCoupling K 1 source.physical := by
  have hcoupling : (0 : Q') <
      (globalInwardMateAnchorSlabData K).coupling := by
    change (0 : Q') < anchorCoupling
    decide
  have hpositive := slabPhysicalTerm_pos_of_fusionWitness
    (globalInwardMateAnchorSlabData K) hcoupling
    source.physical
    (cubeInwardMatePhysicalBoundedOfMem
      K source.physical source.physicalSource.2)
    (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem_allSources
      source hsource)
  simpa [globalInwardMateAnchorSlabData,
    SlabPhysicalData.physicalTerm, SlabPhysicalData.extent,
    centralExtent] using hpositive

theorem targetPhysicalTerm_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') <
      slabParametricKPhysicalTerm anchorCoupling K 1
        (targetPhysical source) := by
  have hcoupling : (0 : Q') <
      (globalInwardMateAnchorSlabData K).coupling := by
    change (0 : Q') < anchorCoupling
    decide
  have hpositive := slabPhysicalTerm_pos_of_fusionWitness
    (globalInwardMateAnchorSlabData K) hcoupling
    (targetPhysical source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem_allSources
      source)
  simpa [globalInwardMateAnchorSlabData,
    SlabPhysicalData.physicalTerm, SlabPhysicalData.extent,
    centralExtent] using hpositive

/-! ## 2. The common channel supplies two positive raw OS entries -/

theorem sourceLower_commonRight_rawKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    (0 : Q') < centralPhysicalReflectedKernel
      anchorCoupling K 0 (sourceLower source) (commonRight source) := by
  unfold centralPhysicalReflectedKernel
  apply listQSum_pos_of_mem
  · intro boundary
    exact slabParametricKPhysicalTerm_nonnegative
      (by decide) K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (sourceLower source) boundary (commonRight source))
  · exact commonBoundary_mem source
  · rw [assemble_source_path source]
    simpa [centralExtent] using sourcePhysicalTerm_pos source hsource

theorem targetLower_commonRight_rawKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') < centralPhysicalReflectedKernel
      anchorCoupling K 0 (targetLower source) (commonRight source) := by
  unfold centralPhysicalReflectedKernel
  apply listQSum_pos_of_mem
  · intro boundary
    exact slabParametricKPhysicalTerm_nonnegative
      (by decide) K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (targetLower source) boundary (commonRight source))
  · exact commonBoundary_mem source
  · rw [assemble_target_path source]
    simpa [centralExtent] using targetPhysicalTerm_pos source

/-! ## 3. Partition normalization, retained rows, and conditioning -/

theorem sourceLower_commonRight_normalizedKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0
        (sourceLower source) (commonRight source) := by
  unfold centralNormalizedPhysicalReflectedKernel
  exact Q'.divPos_pos _ _
    (slabParametricKPhysicalPartition_pos
      (by decide) K (centralExtent 0))
    (sourceLower_commonRight_rawKernel_pos source hsource)

theorem targetLower_commonRight_normalizedKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0
        (targetLower source) (commonRight source) := by
  unfold centralNormalizedPhysicalReflectedKernel
  exact Q'.divPos_pos _ _
    (slabParametricKPhysicalPartition_pos
      (by decide) K (centralExtent 0))
    (targetLower_commonRight_rawKernel_pos source)

theorem commonRight_targetLower_normalizedKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0
        (commonRight source) (targetLower source) := by
  have hforward := targetLower_commonRight_normalizedKernel_pos source
  have hsymm := centralNormalizedPhysicalReflectedKernel_symm
    (w := anchorCoupling) (hw := by decide)
    (targetLower_mem source) (commonRight_mem source)
  exact Q'.pos_of_lt_of_le hforward (Q'.le_of_eqv hsymm)

theorem sourceLower_rowMarginal_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    (0 : Q') < centralPhysicalRowMarginal
      anchorCoupling (by decide) K 0 (sourceLower source) := by
  unfold centralPhysicalRowMarginal
  apply listQSum_pos_of_mem
  · intro target
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) K 0 (sourceLower source) target
  · exact commonRight_mem source
  · exact sourceLower_commonRight_normalizedKernel_pos source hsource

theorem targetLower_rowMarginal_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') < centralPhysicalRowMarginal
      anchorCoupling (by decide) K 0 (targetLower source) := by
  unfold centralPhysicalRowMarginal
  apply listQSum_pos_of_mem
  · intro target
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) K 0 (targetLower source) target
  · exact commonRight_mem source
  · exact targetLower_commonRight_normalizedKernel_pos source

theorem commonRight_rowMarginal_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') < centralPhysicalRowMarginal
      anchorCoupling (by decide) K 0 (commonRight source) := by
  unfold centralPhysicalRowMarginal
  apply listQSum_pos_of_mem
  · intro target
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) K 0 (commonRight source) target
  · exact targetLower_mem source
  · exact commonRight_targetLower_normalizedKernel_pos source

theorem sourceLower_mem_positiveHalfStates
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    sourceLower source ∈ centralPositiveHalfStates
      anchorCoupling (by decide) K 0 :=
  mem_centralPositiveHalfStates_iff.mpr
    ⟨sourceLower_mem source, sourceLower_rowMarginal_pos source hsource⟩

theorem targetLower_mem_positiveHalfStates
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    targetLower source ∈ centralPositiveHalfStates
      anchorCoupling (by decide) K 0 :=
  mem_centralPositiveHalfStates_iff.mpr
    ⟨targetLower_mem source, targetLower_rowMarginal_pos source⟩

theorem commonRight_mem_positiveHalfStates
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    commonRight source ∈ centralPositiveHalfStates
      anchorCoupling (by decide) K 0 :=
  mem_centralPositiveHalfStates_iff.mpr
    ⟨commonRight_mem source, commonRight_rowMarginal_pos source⟩

theorem sourceLower_commonRight_conditionalKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    (0 : Q') < centralPhysicalConditionalKernel
      anchorCoupling (by decide) K 0
        (sourceLower source) (commonRight source) := by
  rw [centralPhysicalConditionalKernel_eq_divPos
    (sourceLower_rowMarginal_pos source hsource)]
  exact Q'.divPos_pos _ _
    (sourceLower_rowMarginal_pos source hsource)
    (sourceLower_commonRight_normalizedKernel_pos source hsource)

theorem commonRight_targetLower_conditionalKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') < centralPhysicalConditionalKernel
      anchorCoupling (by decide) K 0
        (commonRight source) (targetLower source) := by
  rw [centralPhysicalConditionalKernel_eq_divPos
    (commonRight_rowMarginal_pos source)]
  exact Q'.divPos_pos _ _
    (commonRight_rowMarginal_pos source)
    (commonRight_targetLower_normalizedKernel_pos source)

/-! ## 4. The supported two-edge path certificate -/

structure GlobalInwardMateAllSourceSupportedOSPathCertificate
    (K : Nat) (hK : 1 ≤ K)
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) : Type where
  source_mem : sourceLower source ∈ centralPositiveHalfStates
    anchorCoupling (by decide) K 0
  middle_mem : commonRight source ∈ centralPositiveHalfStates
    anchorCoupling (by decide) K 0
  target_mem : targetLower source ∈ centralPositiveHalfStates
    anchorCoupling (by decide) K 0
  first_edge_pos : (0 : Q') < centralPhysicalConditionalKernel
    anchorCoupling (by decide) K 0
      (sourceLower source) (commonRight source)
  second_edge_pos : (0 : Q') < centralPhysicalConditionalKernel
    anchorCoupling (by decide) K 0
      (commonRight source) (targetLower source)
  endpoints_ne : sourceLower source ≠ targetLower source

def globalInwardMateAllSourceSupportedOSPathCertificate
    (K : Nat) (hK : 1 ≤ K)
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalInwardMateAllSourceSupportedOSPathCertificate
      K hK source hsource :=
  { source_mem := sourceLower_mem_positiveHalfStates source hsource
    middle_mem := commonRight_mem_positiveHalfStates source
    target_mem := targetLower_mem_positiveHalfStates source
    first_edge_pos :=
      sourceLower_commonRight_conditionalKernel_pos source hsource
    second_edge_pos := commonRight_targetLower_conditionalKernel_pos source
    endpoints_ne := sourceLower_ne_targetLower source }

#print axioms sourcePhysicalTerm_pos
#print axioms targetPhysicalTerm_pos
#print axioms sourceLower_commonRight_rawKernel_pos
#print axioms targetLower_commonRight_rawKernel_pos
#print axioms sourceLower_commonRight_normalizedKernel_pos
#print axioms targetLower_commonRight_normalizedKernel_pos
#print axioms commonRight_targetLower_normalizedKernel_pos
#print axioms sourceLower_rowMarginal_pos
#print axioms targetLower_rowMarginal_pos
#print axioms commonRight_rowMarginal_pos
#print axioms sourceLower_mem_positiveHalfStates
#print axioms targetLower_mem_positiveHalfStates
#print axioms commonRight_mem_positiveHalfStates
#print axioms sourceLower_commonRight_conditionalKernel_pos
#print axioms commonRight_targetLower_conditionalKernel_pos
#print axioms globalInwardMateAllSourceSupportedOSPathCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathSupport
