/-
# Inward-mate observable energy inside the exact vacuum sector

Every restricted source path stays in the canonical finite vacuum component.
Zero-extending a sector observable preserves its values on all three path
vertices and preserves exactly its physical Dirichlet energy. Consequently
the global first-edge, second-edge and endpoint estimates descend to the
canonical indexed sector with their original factors 1, transportCost and
2*(1+transportCost). No source/target fiber is counted a second time.

These are actual unconditional comparisons for every rational observable,
not a supplied coverage certificate. The missing reverse inequality is a
cutoff-uniform lower bound controlling every centered sector norm by a
separating move family's energy. Positive scalar successful demand alone
does not provide it. No all-vector gap or continuum theorem is claimed.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy
import YMGap.Continuum.FiniteDependentKernelFirstSourceThinning

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- First-edge energy with the previously constructed sector source list. -/
def sectorSelectedFirstEnergy (K : Nat) (hK : 1 ≤ K)
    (coefficient : EdgeLabelling → Q') : Q' :=
  listQSum (globalInwardMateSelectedFirstObservableEnergyTerm coefficient)
    (globalInwardMateVacuumSectorSources K hK)

/-- Second-edge energy with exactly the same restricted traffic. -/
def sectorSelectedSecondEnergy (K : Nat) (hK : 1 ≤ K)
    (coefficient : EdgeLabelling → Q') : Q' :=
  listQSum (globalInwardMateSelectedSecondObservableEnergyTerm coefficient)
    (globalInwardMateVacuumSectorSources K hK)

/-- Endpoint oscillation carried by the exact restricted source list. -/
def sectorSelectedEndpointEnergy (K : Nat) (hK : 1 ≤ K)
    (coefficient : EdgeLabelling → Q') : Q' :=
  listQSum (globalInwardMateSelectedEndpointObservableEnergyTerm coefficient)
    (globalInwardMateVacuumSectorSources K hK)

/-- Restricting a nonnegative gradient energy is bounded by the global energy
of the zero extension whenever its two evaluated vertices are internal. -/
theorem sectorGradientEnergy_le_globalZeroExtension
    (K : Nat) (hK : 1 ≤ K) (coefficient : EdgeLabelling → Q')
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK → EdgeLabelling)
    (hinternal : ∀ source, source ∈ globalInwardMateVacuumSectorSources K hK →
      left source ∈ centralPhysicalFiniteVacuumSectorStates anchorCoupling (by decide) K 0 ∧
      right source ∈ centralPhysicalFiniteVacuumSectorStates anchorCoupling (by decide) K 0) :
    listQSum (fun source => globalInwardMateSourceTraffic source *
        observableSquaredDifference coefficient (left source) (right source))
        (globalInwardMateVacuumSectorSources K hK) ≤
      listQSum (fun source => globalInwardMateSourceTraffic source *
        observableSquaredDifference
          (vacuumSectorZeroExtension anchorCoupling (by decide) K 0 coefficient)
          (left source) (right source))
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  let extended := vacuumSectorZeroExtension anchorCoupling (by decide) K 0 coefficient
  let term := fun source => globalInwardMateSourceTraffic source *
    observableSquaredDifference extended (left source) (right source)
  have hagree : listQSum (fun source => globalInwardMateSourceTraffic source *
      observableSquaredDifference coefficient (left source) (right source))
        (globalInwardMateVacuumSectorSources K hK) ≈
      listQSum term (globalInwardMateVacuumSectorSources K hK) := by
    apply listQSum_congr_on
    intro source hs
    have hvertices := hinternal source hs
    unfold term extended observableSquaredDifference
    rw [vacuumSectorZeroExtension_on_sector anchorCoupling (by decide) K 0 coefficient hvertices.1,
      vacuumSectorZeroExtension_on_sector anchorCoupling (by decide) K 0 coefficient hvertices.2]
    exact Q'.eqv_refl _
  have hnonnegative : ∀ source, (0 : Q') ≤ term source := fun source =>
    Q'.mul_nonneg _ _ (globalInwardMateSourceTraffic_nonnegative source)
      (observableSquaredDifference_nonnegative extended (left source) (right source))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hagree)
    (listQSum_filter_le_of_nonnegative term _ hnonnegative
      (globalCubeInwardMateCertifiedTargetFullSources K hK))

/-- First-edge restriction embeds in the actual sector energy with factor one. -/
theorem sectorSelectedFirstEnergy_le_Dirichlet
    (K : Nat) (hK : 1 ≤ K) (coefficient : EdgeLabelling → Q') :
    sectorSelectedFirstEnergy K hK coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) K 0)
        (centralPhysicalFiniteCoefficient anchorCoupling (by decide) K 0 coefficient)
        (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0) := by
  have hrestriction := sectorGradientEnergy_le_globalZeroExtension K hK coefficient
    sourceLower commonRight (fun _ hs => by
      have hp := globalInwardMateVacuumSectorSource_path_internal hs
      exact ⟨hp.1, hp.2.1⟩)
  exact Q'.le_trans' _ _ _ hrestriction
    (Q'.le_trans' _ _ _
      (globalInwardMateSelectedFirstObservableEnergy_le_Dirichlet K hK
        (vacuumSectorZeroExtension anchorCoupling (by decide) K 0 coefficient))
      (Q'.le_of_eqv (vacuumSectorZeroExtension_Dirichlet_eq_indexed
        anchorCoupling (by decide) K 0 coefficient)))

/-- The second edge retains exactly the previously proved transport cost. -/
theorem sectorSelectedSecondEnergy_le_cost_mul_Dirichlet
    (K : Nat) (hK : 1 ≤ K) (coefficient : EdgeLabelling → Q') :
    sectorSelectedSecondEnergy K hK coefficient ≤
      globalInwardMateTransportCost * finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) K 0)
        (centralPhysicalFiniteCoefficient anchorCoupling (by decide) K 0 coefficient)
        (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0) := by
  have hrestriction := sectorGradientEnergy_le_globalZeroExtension K hK coefficient
    commonRight targetLower (fun _ hs => by
      have hp := globalInwardMateVacuumSectorSource_path_internal hs
      exact hp.2)
  exact Q'.le_trans' _ _ _ hrestriction
    (Q'.le_trans' _ _ _
      (globalInwardMateSelectedSecondObservableEnergy_le_cost_mul_Dirichlet K hK
        (vacuumSectorZeroExtension anchorCoupling (by decide) K 0 coefficient))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (vacuumSectorZeroExtension_Dirichlet_eq_indexed
          anchorCoupling (by decide) K 0 coefficient))))

/-- **Unconditional sector-local comparison for every observable.** The same
factor `2*(1+transportCost)` bounds restricted endpoint energy by the genuine
indexed vacuum-sector OS Dirichlet form. The reverse coverage bound is open. -/
theorem sectorSelectedEndpointEnergy_le_scale_mul_Dirichlet
    (K : Nat) (hK : 1 ≤ K) (coefficient : EdgeLabelling → Q') :
    sectorSelectedEndpointEnergy K hK coefficient ≤
      globalInwardMateObservablePathScale * finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) K 0)
        (centralPhysicalFiniteCoefficient anchorCoupling (by decide) K 0 coefficient)
        (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0) := by
  have hrestriction := sectorGradientEnergy_le_globalZeroExtension K hK coefficient
    sourceLower targetLower (fun _ hs => by
      have hp := globalInwardMateVacuumSectorSource_path_internal hs
      exact ⟨hp.1, hp.2.2⟩)
  exact Q'.le_trans' _ _ _ hrestriction
    (Q'.le_trans' _ _ _
      (globalInwardMateSelectedEndpointObservableEnergy_le_scale_mul_Dirichlet K hK
        (vacuumSectorZeroExtension anchorCoupling (by decide) K 0 coefficient))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (vacuumSectorZeroExtension_Dirichlet_eq_indexed
          anchorCoupling (by decide) K 0 coefficient))))

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.sectorGradientEnergy_le_globalZeroExtension
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.sectorSelectedFirstEnergy_le_Dirichlet
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.sectorSelectedSecondEnergy_le_cost_mul_Dirichlet
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.sectorSelectedEndpointEnergy_le_scale_mul_Dirichlet
