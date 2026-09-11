/-
# Finite common-order word for complete-source lowered targets

The pointwise source-independent order theorem is serialized here into the
finite word used by downstream target-block codes.  Isolating this projection
behind its own checked declaration keeps consumers from normalizing the full
adaptive inverse record while comparing order words.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrderWords

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- The one common finite order word for all lowered targets. -/
def cubeInwardMateFixedOrderTargetOrderWords : List (List Nat) :=
  (boundaryCompleteSlabLinks 1).attach.map fun linked =>
    (cubeInwardMateCompleteSourceFaceOrder linked).faceIds

/-- The order and auxiliary words that remain after fixing root, size, and
physical target. -/
def cubeInwardMateFullPeelRepresentativeResidualCode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    List (List Nat) × List (List Nat) :=
  (cubeInwardMateFixedOrderTargetOrderWords,
    presentedSlabFusionWitnessAssignmentAuxiliaryWords
      (boundaryCompleteSlabLinks 1)
      representative.adaptiveInverseData.lowerAssignment)

/-- Every lowered assignment has the common source-independent order word. -/
theorem enumeratedCubeInwardMateFullSource_lowerOrderWords_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    presentedSlabFusionWitnessAssignmentOrderWords
        (boundaryCompleteSlabLinks 1)
        representative.adaptiveInverseData.lowerAssignment =
      cubeInwardMateFixedOrderTargetOrderWords := by
  unfold presentedSlabFusionWitnessAssignmentOrderWords
    cubeInwardMateFixedOrderTargetOrderWords
  apply List.map_congr_left
  intro linked _hlinked
  exact congrArg (fun order => order.faceIds)
    (EnumeratedCubeInwardMateFullSource.adaptiveInverseData_lowerAssignment_order
      representative linked)

/-- Reverse orientation used when a target-carrier code is compared with a
realized source code. -/
theorem cubeInwardMateFixedOrderTargetOrderWords_eq_enumerated
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    cubeInwardMateFixedOrderTargetOrderWords =
      presentedSlabFusionWitnessAssignmentOrderWords
        (boundaryCompleteSlabLinks 1)
        representative.adaptiveInverseData.lowerAssignment :=
  (enumeratedCubeInwardMateFullSource_lowerOrderWords_eq representative).symm

#print axioms cubeInwardMateFixedOrderTargetOrderWords
#print axioms cubeInwardMateFullPeelRepresentativeResidualCode
#print axioms enumeratedCubeInwardMateFullSource_lowerOrderWords_eq
#print axioms cubeInwardMateFixedOrderTargetOrderWords_eq_enumerated

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrderWords
