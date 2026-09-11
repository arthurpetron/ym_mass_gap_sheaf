/-
# The all-source inward mate is a literal two-edge OS path

The multiplicity-faithful inward-mate transport was constructed on complete
extent-one slab configurations.  This module identifies its first genuinely
Osterwalder--Schrader geometric content.

The mate changes only the six faces of the central lower cube.  Consequently
the source and target have exactly the same fixed-plane restriction and the
same reflected upper restriction.  Their lower restrictions are distinct.
Thus every successful full-slab source--mate pair is the assembly of two
different lower states against one common boundary channel and one common
reflected-upper state: the geometric support of a length-two OS path.

No positivity, transition lower bound, posterior variance, form bound,
spectral gap, beta/lattice-spacing uniformity, continuum limit, or Clay
theorem is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry

set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

/-! ## 1. The three OS coordinates of the source--mate pair -/

def sourceLower
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling :=
  centralLowerRestriction 0 source.physical

/-- Local name for the already constructed full-slab mate. -/
abbrev targetPhysical
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling :=
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical.GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
    source

theorem targetPhysical_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    targetPhysical source ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) :=
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical.GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem
    source

theorem targetPhysical_parity_ne
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    {faceId : Nat} (hface : faceId ∈ centralLowerCubeFaceIds) :
    targetPhysical source faceId % 2 ≠ source.physical faceId % 2 :=
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical.GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_parity_ne
    source hface

def targetLower
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling :=
  centralLowerRestriction 0 (targetPhysical source)

def commonBoundary
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling :=
  centralBoundaryRestriction 0 source.physical

def commonRight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling :=
  centralReflectedUpperRestriction 0 source.physical

/-! ## 2. The inward mate fixes the boundary and upper restrictions -/

/-- Since every selected cube face is lower, the inward mate fixes every
fixed-plane coordinate. -/
theorem targetBoundary_eq_common
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    centralBoundaryRestriction 0 (targetPhysical source) =
      commonBoundary source := by
  funext faceId
  by_cases hfixed : faceId ∈ centralFixedFaceIds 0
  · have hnotCube : faceId ∉ centralLowerCubeFaceIds := by
      intro hcube
      have hlower := mem_centralLowerFaceIds.mp
        (centralLowerCubeFaceIds_subset_lower faceId hcube)
      have hfixedParts := mem_centralFixedFaceIds.mp hfixed
      rw [hfixedParts.2] at hlower
      cases hlower.2
    simp only [centralBoundaryRestriction, if_pos hfixed, commonBoundary]
    change centralLowerCubeEvenInwardMatePhysical source.physical faceId =
      source.physical faceId
    exact centralLowerCubeEvenInwardMatePhysical_off_cube
      source.physical hnotCube
  · simp [centralBoundaryRestriction, hfixed, commonBoundary]

/-- Reading the upper half through reflection also sees no changed cube face. -/
theorem targetRight_eq_common
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    centralReflectedUpperRestriction 0 (targetPhysical source) =
      commonRight source := by
  funext faceId
  by_cases hlower : faceId ∈ centralLowerFaceIds 0
  · have hlowerParts := mem_centralLowerFaceIds.mp hlower
    have hreflectedSide := slabFaceReflectId_side hlowerParts.1
    rw [hlowerParts.2] at hreflectedSide
    have hnotCube :
        slabFaceReflectId (centralExtent 0) faceId ∉
          centralLowerCubeFaceIds := by
      intro hcube
      have hreflectedLower := mem_centralLowerFaceIds.mp
        (centralLowerCubeFaceIds_subset_lower
          (slabFaceReflectId (centralExtent 0) faceId) hcube)
      rw [hreflectedSide] at hreflectedLower
      cases hreflectedLower.2
    simp only [centralReflectedUpperRestriction, if_pos hlower, commonRight]
    change centralLowerCubeEvenInwardMatePhysical source.physical
        (slabFaceReflectId (centralExtent 0) faceId) =
      source.physical (slabFaceReflectId (centralExtent 0) faceId)
    exact centralLowerCubeEvenInwardMatePhysical_off_cube
      source.physical hnotCube
  · simp [centralReflectedUpperRestriction, hlower, commonRight]

/-! ## 3. Both lower endpoints and the shared data are physical -/

theorem sourceLower_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    sourceLower source ∈ centralHalfStates K 0 := by
  unfold sourceLower centralHalfStates
  apply centralLowerRestriction_mem
  simpa [centralExtent] using source.physicalSource.2

theorem targetLower_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    targetLower source ∈ centralHalfStates K 0 := by
  unfold targetLower centralHalfStates
  apply centralLowerRestriction_mem
  simpa [centralExtent] using targetPhysical_mem source

theorem commonBoundary_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    commonBoundary source ∈ centralBoundaryChannels K 0 := by
  unfold commonBoundary centralBoundaryChannels
  apply centralBoundaryRestriction_mem
  simpa [centralExtent] using source.physicalSource.2

theorem commonRight_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    commonRight source ∈ centralHalfStates K 0 := by
  unfold commonRight centralHalfStates
  apply centralReflectedUpperRestriction_mem
  simpa [centralExtent] using source.physicalSource.2

/-! ## 4. Exact assembly and nontriviality of the OS path -/

theorem assemble_source_path
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    assembleReflectedSlabLabelling 0 (sourceLower source)
        (commonBoundary source) (commonRight source) = source.physical := by
  exact assembleReflectedSlabLabelling_restrictions
    (by simpa [centralExtent] using source.physicalSource.2)

theorem assemble_target_path
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    assembleReflectedSlabLabelling 0 (targetLower source)
        (commonBoundary source) (commonRight source) = targetPhysical source := by
  have hassemble := assembleReflectedSlabLabelling_restrictions
    (K := K) (half := 0) (targetPhysical_mem source)
  rw [targetBoundary_eq_common source,
    targetRight_eq_common source] at hassemble
  exact hassemble

/-- The two OS endpoints differ already at central-cube face zero. -/
theorem sourceLower_ne_targetLower
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    sourceLower source ≠ targetLower source := by
  intro heq
  have hcube : 0 ∈ centralLowerCubeFaceIds := by
    simp [centralLowerCubeFaceIds]
  have hlower : 0 ∈ centralLowerFaceIds 0 :=
    centralLowerCubeFaceIds_subset_lower 0 hcube
  have hvalue := congrFun heq 0
  change centralLowerRestriction 0 source.physical 0 =
    centralLowerRestriction 0 (targetPhysical source) 0 at hvalue
  simp only [centralLowerRestriction, if_pos hlower] at hvalue
  exact targetPhysical_parity_ne source hcube
    (congrArg (fun spin => spin % 2) hvalue.symm)

/-- Type-level package of the literal two-edge OS geometry. -/
structure GlobalInwardMateAllSourceOSPathGeometryCertificate
    (K : Nat) (hK : 1 ≤ K)
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Type where
  sourceLower_mem : sourceLower source ∈ centralHalfStates K 0
  targetLower_mem : targetLower source ∈ centralHalfStates K 0
  commonRight_mem : commonRight source ∈ centralHalfStates K 0
  commonBoundary_mem :
    commonBoundary source ∈ centralBoundaryChannels K 0
  source_assembly :
    assembleReflectedSlabLabelling 0 (sourceLower source)
      (commonBoundary source) (commonRight source) = source.physical
  target_assembly :
    assembleReflectedSlabLabelling 0 (targetLower source)
      (commonBoundary source) (commonRight source) = targetPhysical source
  endpoints_ne : sourceLower source ≠ targetLower source

def globalInwardMateAllSourceOSPathGeometryCertificate
    (K : Nat) (hK : 1 ≤ K)
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalInwardMateAllSourceOSPathGeometryCertificate K hK source :=
  { sourceLower_mem := sourceLower_mem source
    targetLower_mem := targetLower_mem source
    commonRight_mem := commonRight_mem source
    commonBoundary_mem := commonBoundary_mem source
    source_assembly := assemble_source_path source
    target_assembly := assemble_target_path source
    endpoints_ne := sourceLower_ne_targetLower source }

#print axioms targetBoundary_eq_common
#print axioms targetRight_eq_common
#print axioms sourceLower_mem
#print axioms targetLower_mem
#print axioms commonBoundary_mem
#print axioms commonRight_mem
#print axioms assemble_source_path
#print axioms assemble_target_path
#print axioms sourceLower_ne_targetLower
#print axioms globalInwardMateAllSourceOSPathGeometryCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
