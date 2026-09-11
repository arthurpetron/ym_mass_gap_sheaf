/-
# Physical admissibility of complete-source lowered targets

The deterministic component peel lowers only supported slab faces.  Hence a
lowered target of an enumerated physical source remains bounded by the same
cutoff and vanishes off the complete extent-one face carrier.  Its root is
one of the six literal central cube faces, and its presented weight is the
same unit-Haar atom used by the fixed-order target carrier.

These facts connect the realized representative sum to the whole physical
target normalization.  They do not yet prove the root/size congestion
injection.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The lowered physical field remains in the finite carrier -/

/-- Component removal can only decrease each physical face, so the cutoff
bound is preserved. -/
theorem EnumeratedCubeInwardMateFullSource.lowerPhysical_bounded
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    SlabFaceLabellingBounded K 1
      entry.adaptiveInverseData.lowerPhysical := by
  intro faceId hface
  change physical faceId -
      slabFaceStrandSelectionCount
        (certifiedStretchedComponentUnionSupportedSelection
          entry.source.1 entry.source.toPresented).closed.selected faceId ≤ K
  exact Nat.le_trans (Nat.sub_le _ _) (hbounded faceId hface)

/-- A source in the genuine extent-one physical carrier lowers to another
member of that same carrier. -/
theorem EnumeratedCubeInwardMateFullSource.lowerPhysical_mem
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded)
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    entry.adaptiveInverseData.lowerPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) := by
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    exact Nat.lt_succ_iff.mpr
      (YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical.EnumeratedCubeInwardMateFullSource.lowerPhysical_bounded
        entry faceId hface)
  · intro faceId hface
    rw [YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey.EnumeratedCubeInwardMateFullSource.lowerPhysical_eq_physical_of_not_mem
      entry faceId hface]
    exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      physical hphysical).2 faceId hface

/-! ## 2. Presented target weight equals the carrier atom -/

/-- The flat inverse record retains the literal left cube-face root selected
by the certified first-stretched source. -/
theorem EnumeratedCubeInwardMateFullSource.rootFaceId_eq_sourceLeft
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    entry.adaptiveInverseData.rootFaceId =
      centralLowerCubeFaceId entry.source.1.root.1.1.left := by
  rfl

/-- Consequently every deterministic peel root is one of the literal six
central cube faces. -/
theorem EnumeratedCubeInwardMateFullSource.rootFaceId_mem_cube
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    entry.adaptiveInverseData.rootFaceId ∈ centralLowerCubeFaceIds := by
  rw [YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical.EnumeratedCubeInwardMateFullSource.rootFaceId_eq_sourceLeft
    entry]
  exact centralLowerCubeFaceId_mem entry.source.1.root.1.1.left

/-- The representative's presented target and its fixed-order carrier atom
have the same exact BF4 weight. -/
theorem EnumeratedCubeInwardMateFullSource.presentedTargetWeight_eqv_fixedOrderAtom
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    presentedSlabFusionWitnessAssignmentFiberWeight D
        entry.adaptiveInverseData.lowerPhysical
        entry.adaptiveInverseData.lowerAssignment ≈
      cubeInwardMateFixedOrderTargetBlockEntryWeight
        anchorCoupling K entry.adaptiveInverseData.lowerPhysical := by
  dsimp only
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor anchorCoupling K 1
      entry.adaptiveInverseData.lowerPhysical) _
    (presentedSlabFusionWitnessAssignmentFiberWeight_eqv_faceFactor
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
      entry.adaptiveInverseData.lowerPhysical
      entry.adaptiveInverseData.lowerAssignment) ?_
  unfold cubeInwardMateFixedOrderTargetBlockEntryWeight
  exact Q'.eqv_symm (Q'.mul_one_eqv _)

#print axioms EnumeratedCubeInwardMateFullSource.lowerPhysical_bounded
#print axioms EnumeratedCubeInwardMateFullSource.lowerPhysical_mem
#print axioms EnumeratedCubeInwardMateFullSource.rootFaceId_eq_sourceLeft
#print axioms EnumeratedCubeInwardMateFullSource.rootFaceId_mem_cube
#print axioms EnumeratedCubeInwardMateFullSource.presentedTargetWeight_eqv_fixedOrderAtom

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical
