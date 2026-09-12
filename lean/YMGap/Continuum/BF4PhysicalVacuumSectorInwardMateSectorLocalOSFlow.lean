/-
# The inward-mate OS flow restricted to the exact vacuum sector

The exact sector-local source classifier can now restrict the already
partition-normalized inward-mate traffic.  Filtering preserves nonnegativity,
the first-edge capacity estimate, and the production-target-fiber second-edge
congestion estimate.  Every path carrying this traffic is internal to the
canonical finite vacuum component.

The global `41/425` lower bound is intentionally absent: a lower bound for the
filtered traffic relative to the vacuum-sector mass has not yet been proved.
That sector-relative demand estimate, followed by separating moves, is the
next mathematical obligation.  No Poincare, spectral-gap, continuum, or Clay
claim is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion
import YMGap.Continuum.FiniteDependentKernelFirstSourceThinning

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Restricted traffic and its exact target fibers -/

/-- Total partition-normalized inward-mate traffic whose source endpoint lies
in the canonical finite vacuum component. -/
def globalInwardMateVacuumSectorTotalTraffic
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  listQSum globalInwardMateSourceTraffic
    (globalInwardMateVacuumSectorSources K hK)

/-- The production-target fiber restricted by the exact vacuum-sector source
classifier. -/
def globalInwardMateVacuumSectorProductionTargetFiber
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  (globalInwardMateProductionTargetFiber representative).filter
    (fun source =>
      centralPhysicalFiniteVacuumSectorStateB
        anchorCoupling (by decide) K 0 (sourceLower source))

/-- Exact membership specification for a restricted production-target
fiber. -/
theorem mem_globalInwardMateVacuumSectorProductionTargetFiber_iff
    {K : Nat} {hK : 1 ≤ K}
    {representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK} :
    source ∈ globalInwardMateVacuumSectorProductionTargetFiber representative ↔
      source ∈ globalInwardMateProductionTargetFiber representative ∧
        sourceLower source ∈
          centralPhysicalFiniteVacuumSectorStates
            anchorCoupling (by decide) K 0 := by
  unfold globalInwardMateVacuumSectorProductionTargetFiber
  rw [List.mem_filter]
  constructor
  · intro hparts
    exact ⟨hparts.1,
      (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
        anchorCoupling (by decide) K 0 (sourceLower_mem source)).mp
        hparts.2⟩
  · intro hparts
    exact ⟨hparts.1,
      (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
        anchorCoupling (by decide) K 0 (sourceLower_mem source)).mpr
        hparts.2⟩

theorem globalInwardMateVacuumSectorProductionTargetFiber_mem_sources
    {K : Nat} {hK : 1 ≤ K}
    {representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈
      globalInwardMateVacuumSectorProductionTargetFiber representative) :
    source ∈ globalInwardMateVacuumSectorSources K hK := by
  have hparts :=
    mem_globalInwardMateVacuumSectorProductionTargetFiber_iff.mp hsource
  apply mem_globalInwardMateVacuumSectorSources_iff.mpr
  refine ⟨?_, hparts.2⟩
  unfold globalInwardMateProductionTargetFiber at hparts
  exact (List.mem_filter.mp hparts.1).1

/-! ## 2. The capacity bounds survive exact restriction -/

theorem globalInwardMateVacuumSectorSourceTraffic_nonnegative
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') ≤ globalInwardMateSourceTraffic source := by
  unfold globalInwardMateSourceTraffic Q'.divPos
  exact Q'.mul_nonneg _ _
    (slabExpandedFineSourceWeight_nonnegative
      (globalInwardMateAnchorSlabData K)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
        source))
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (slabParametricKPhysicalPartition_pos (by decide) K 1)))

theorem globalInwardMateVacuumSectorTotalTraffic_nonnegative
    (K : Nat) (hK : 1 ≤ K) :
    (0 : Q') ≤ globalInwardMateVacuumSectorTotalTraffic K hK := by
  unfold globalInwardMateVacuumSectorTotalTraffic
  apply listQSum_nonnegative_on
  intro source _
  exact globalInwardMateVacuumSectorSourceTraffic_nonnegative source

/-- Restriction can only decrease the total nonnegative traffic. -/
theorem globalInwardMateVacuumSectorTotalTraffic_le_allSourceTraffic
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateVacuumSectorTotalTraffic K hK ≤
      listQSum globalInwardMateSourceTraffic
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  unfold globalInwardMateVacuumSectorTotalTraffic
    globalInwardMateVacuumSectorSources
  exact listQSum_filter_le_of_nonnegative
    globalInwardMateSourceTraffic
    (fun source =>
      centralPhysicalFiniteVacuumSectorStateB
        anchorCoupling (by decide) K 0 (sourceLower source))
    globalInwardMateVacuumSectorSourceTraffic_nonnegative
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

/-- Every restricted source demand is paid pointwise by its first actual
normalized OS edge. -/
theorem globalInwardMateVacuumSectorSourceTraffic_le_firstEdge
    {K : Nat} {hK : 1 ≤ K}
    {source : GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈ globalInwardMateVacuumSectorSources K hK) :
    globalInwardMateSourceTraffic source ≤
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (sourceLower source) (commonRight source) := by
  exact sourceTraffic_le_first_normalizedKernel source
    (globalInwardMateVacuumSectorSource_mem_allSources hsource)

/-- Restricting a production-target fiber preserves its previously proved
second-edge congestion bound. -/
theorem globalInwardMateVacuumSectorProductionTargetFiber_traffic_le_secondEdge
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateSourceTraffic
        (globalInwardMateVacuumSectorProductionTargetFiber representative) ≤
      globalInwardMateTransportCost *
        centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
            (commonRight representative) (targetLower representative) := by
  refine Q'.le_trans' _ _ _ ?_
    (globalInwardMateProductionTargetFiber_sourceTraffic_le_secondEdge
      representative)
  unfold globalInwardMateVacuumSectorProductionTargetFiber
  exact listQSum_filter_le_of_nonnegative
    globalInwardMateSourceTraffic
    (fun source =>
      centralPhysicalFiniteVacuumSectorStateB
        anchorCoupling (by decide) K 0 (sourceLower source))
    globalInwardMateVacuumSectorSourceTraffic_nonnegative
    (globalInwardMateProductionTargetFiber representative)

/-! ## 3. Witness-bearing restricted flow -/

/-- Exact sector-local normalized flow data.  There is deliberately no
positive `total_lower` field until a sector-relative demand theorem exists. -/
structure GlobalInwardMateVacuumSectorOSFlowCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  sources : List (GlobalCubeInwardMateCertifiedTargetFullSource K hK)
  traffic : GlobalCubeInwardMateCertifiedTargetFullSource K hK → Q'
  targetFiber : GlobalCubeInwardMateCertifiedTargetFullSource K hK →
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK)
  sources_eq : sources = globalInwardMateVacuumSectorSources K hK
  traffic_eq : ∀ source, traffic source ≈ globalInwardMateSourceTraffic source
  targetFiber_eq : ∀ representative,
    targetFiber representative =
      globalInwardMateVacuumSectorProductionTargetFiber representative
  total_nonnegative : (0 : Q') ≤ listQSum traffic sources
  path_internal : ∀ source, source ∈ sources →
    sourceLower source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 ∧
      commonRight source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 ∧
      targetLower source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0
  first_capacity : ∀ source, source ∈ sources →
    traffic source ≤
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (sourceLower source) (commonRight source)
  target_fiber_capacity : ∀ representative,
    listQSum traffic (targetFiber representative) ≤
      globalInwardMateTransportCost *
        centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
            (commonRight representative) (targetLower representative)

def globalInwardMateVacuumSectorOSFlowCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalInwardMateVacuumSectorOSFlowCertificate K hK where
  sources := globalInwardMateVacuumSectorSources K hK
  traffic := globalInwardMateSourceTraffic
  targetFiber := globalInwardMateVacuumSectorProductionTargetFiber
  sources_eq := rfl
  traffic_eq := fun _ => Q'.eqv_refl _
  targetFiber_eq := fun _ => rfl
  total_nonnegative :=
    globalInwardMateVacuumSectorTotalTraffic_nonnegative K hK
  path_internal := fun _ hsource =>
    globalInwardMateVacuumSectorSource_path_internal hsource
  first_capacity := fun _ hsource =>
    globalInwardMateVacuumSectorSourceTraffic_le_firstEdge hsource
  target_fiber_capacity :=
    globalInwardMateVacuumSectorProductionTargetFiber_traffic_le_secondEdge

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.mem_globalInwardMateVacuumSectorProductionTargetFiber_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.globalInwardMateVacuumSectorTotalTraffic_le_allSourceTraffic
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.globalInwardMateVacuumSectorProductionTargetFiber_traffic_le_secondEdge
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.globalInwardMateVacuumSectorOSFlowCertificate
