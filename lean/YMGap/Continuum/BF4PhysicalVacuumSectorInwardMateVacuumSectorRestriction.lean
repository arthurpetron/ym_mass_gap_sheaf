/-
# The inward-mate OS path stays in the exact finite vacuum sector

The positive-row physical carrier can have several exact support components.
The canonical finite vacuum sector is the component containing the all-zero
state, so a path intended for a vacuum-sector Poincare argument must remain in
that component.

This module first records the general closure principle at the state level:
a strictly positive raw Osterwalder--Schrader kernel entry cannot leave the
canonical support component.  It then applies that principle to the two
positive entries already supplied by every certified inward-mate source.  Thus

`sourceLower -> commonRight <- targetLower`

lies entirely in the exact finite vacuum sector whenever `sourceLower` does.

This is sector closure only.  It proves neither that the selected paths connect
or separate the whole sector nor a uniform congestion, form, spectral-gap,
continuum, or Clay bound.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathSupport

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathSupport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. State-level closure under positive raw OS support -/

/-- A strictly positive directed raw OS-kernel entry whose source lies in the
canonical finite vacuum component keeps its positive-carrier target in that
component. -/
theorem centralPhysicalFiniteVacuumSectorState_mem_of_rawKernel_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {source target : EdgeLabelling}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorStates w hw K half)
    (htarget : target ∈ centralPositiveHalfStates w hw K half)
    (hpos : (0 : Q') <
      centralPhysicalReflectedKernel w K half source target) :
    target ∈ centralPhysicalFiniteVacuumSectorStates w hw K half := by
  rcases List.mem_map.mp hsource with
    ⟨sourceIndex, hsourceIndex, hsourceEq⟩
  obtain ⟨targetIndex, htargetIndex, htargetEq⟩ :=
    centralPhysicalFiniteStateAt_exists w hw K half htarget
  have htargetVertex : targetIndex ∈
      centralPhysicalFiniteIndexCarrier w hw K half :=
    List.mem_range.mpr htargetIndex
  have hedge : centralPhysicalFiniteSupportAdjacentB
      w hw K half sourceIndex targetIndex = true :=
    centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
      w hw K half hsourceEq htargetEq hpos
  have htargetSector : targetIndex ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half :=
    rootComponent_closed_under_edge
      (centralPhysicalFiniteSupportAdjacentB w hw K half)
      (centralPhysicalFiniteSupportAdjacentB_symmetric w hw K half)
      (zero_mem_centralPhysicalFiniteIndexCarrier w hw K half)
      hsourceIndex htargetVertex hedge
  exact centralPhysicalFiniteVacuumSectorState_mem_of_index
    w hw K half htargetSector htargetEq

/-- Reverse-directed version of state-level vacuum-component closure.  The
finite support graph is symmetric, so positivity of `target -> source` also
keeps `target` in the component containing `source`. -/
theorem centralPhysicalFiniteVacuumSectorState_mem_of_reverse_rawKernel_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {source target : EdgeLabelling}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorStates w hw K half)
    (htarget : target ∈ centralPositiveHalfStates w hw K half)
    (hpos : (0 : Q') <
      centralPhysicalReflectedKernel w K half target source) :
    target ∈ centralPhysicalFiniteVacuumSectorStates w hw K half := by
  rcases List.mem_map.mp hsource with
    ⟨sourceIndex, hsourceIndex, hsourceEq⟩
  obtain ⟨targetIndex, htargetIndex, htargetEq⟩ :=
    centralPhysicalFiniteStateAt_exists w hw K half htarget
  have htargetVertex : targetIndex ∈
      centralPhysicalFiniteIndexCarrier w hw K half :=
    List.mem_range.mpr htargetIndex
  have hedge : centralPhysicalFiniteSupportAdjacentB
      w hw K half sourceIndex targetIndex = true :=
    centralPhysicalFiniteSupportAdjacentB_reverse_true_of_kernel_pos
      w hw K half htargetEq hsourceEq hpos
  have htargetSector : targetIndex ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half :=
    rootComponent_closed_under_edge
      (centralPhysicalFiniteSupportAdjacentB w hw K half)
      (centralPhysicalFiniteSupportAdjacentB_symmetric w hw K half)
      (zero_mem_centralPhysicalFiniteIndexCarrier w hw K half)
      hsourceIndex htargetVertex hedge
  exact centralPhysicalFiniteVacuumSectorState_mem_of_index
    w hw K half htargetSector htargetEq

/-! ## 2. The certified inward-mate path is sector preserving -/

/-- The common reflected-upper state remains in the exact vacuum component
whenever the path's source endpoint belongs to it. -/
theorem commonRight_mem_vacuumSector_of_sourceLower_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK)
    (hsourceSector : sourceLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0) :
    commonRight source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 := by
  exact centralPhysicalFiniteVacuumSectorState_mem_of_rawKernel_pos
    anchorCoupling (by decide) K 0 hsourceSector
      (commonRight_mem_positiveHalfStates source)
      (sourceLower_commonRight_rawKernel_pos source hsource)

/-- Once the common state is in the vacuum component, the reverse-oriented
positive endpoint entry puts the inward-mate target in the same component. -/
theorem targetLower_mem_vacuumSector_of_commonRight_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hcommonSector : commonRight source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0) :
    targetLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 := by
  exact centralPhysicalFiniteVacuumSectorState_mem_of_reverse_rawKernel_pos
    anchorCoupling (by decide) K 0 hcommonSector
      (targetLower_mem_positiveHalfStates source)
      (targetLower_commonRight_rawKernel_pos source)

/-- Every certified inward-mate path that starts in the exact finite vacuum
component has both its hub and its endpoint in that same component. -/
theorem inwardMatePath_stays_in_vacuumSector
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK)
    (hsourceSector : sourceLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0) :
    commonRight source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 ∧
      targetLower source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 := by
  have hcommon := commonRight_mem_vacuumSector_of_sourceLower_mem
    source hsource hsourceSector
  exact ⟨hcommon,
    targetLower_mem_vacuumSector_of_commonRight_mem source hcommon⟩

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.centralPhysicalFiniteVacuumSectorState_mem_of_rawKernel_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.centralPhysicalFiniteVacuumSectorState_mem_of_reverse_rawKernel_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.inwardMatePath_stays_in_vacuumSector
