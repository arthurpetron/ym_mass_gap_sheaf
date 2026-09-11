/-
# The global all-target event has a literal parity-flipped physical target

The global `41/425` event is useful for an observable argument only after its
classified target is tied to a genuine physical state.  This module records
that first bridge.  Every successful source has the central-cube inward mate
as an explicit bounded extent-one physical target, and the mate reverses the
parity of each of the six selected lower faces.

This is not yet a posterior transport: no complete target intertwiner
assignment, target-column capacity, conditional-variance estimate, or
spectral gap is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSuccessFraction

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Parity reversal of the scalar inward mate -/

/-- The inward mate reverses the parity of every natural-number label. -/
theorem evenInwardMateLabel_mod_two_ne (spin : Nat) :
    evenInwardMateLabel spin % 2 ≠ spin % 2 := by
  unfold evenInwardMateLabel
  by_cases hzero : spin = 0
  · subst spin
    decide
  · rw [if_neg hzero]
    omega

/-! ## 2. The physical target carried by every successful global source -/

/-- The literal extent-one physical target of a successful global source. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling :=
  centralLowerCubeEvenInwardMatePhysical source.physical

/-- The successful target stays inside the same representation cutoff. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabFaceLabellingBounded K 1 (targetPhysical source) := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
  exact centralLowerCubeEvenInwardMatePhysical_bounded
    hK (cubeInwardMatePhysicalBoundedOfMem
      K source.physical source.physicalSource.2)

/-- Hence the target is a literal member of the full extent-one physical
carrier used by the BF4 partition. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    targetPhysical source ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) := by
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    exact Nat.lt_succ_iff.mpr
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded
        source faceId hface)
  · intro faceId hface
    unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
    rw [centralLowerCubeEvenInwardMatePhysical_off_cube source.physical]
    · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
        source.physical source.physicalSource.2).2 faceId hface
    · intro hcube
      have hlower := centralLowerCubeFaceIds_subset_lower faceId hcube
      have hphysical := (mem_centralLowerFaceIds.mp hlower).1
      exact hface (by simpa [centralExtent] using hphysical)

/-- On every selected central-cube face, the successful target has the
opposite parity from its physical source. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_parity_ne
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    {faceId : Nat} (hface : faceId ∈ centralLowerCubeFaceIds) :
    targetPhysical source faceId % 2 ≠ source.physical faceId % 2 := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
  rw [centralLowerCubeEvenInwardMatePhysical_on_cube source.physical hface]
  exact evenInwardMateLabel_mod_two_ne (source.physical faceId)

#print axioms evenInwardMateLabel_mod_two_ne
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_parity_ne

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
