/-
# The active cube root enters its collapsed SU(2) strand continuation

This file joins the geometric and representation-theoretic root compilers.
The two positive cube-face copies become the input ports of the stretched
trivalent vertex.  Their canonical mates are the two disjoint ports in the
summed channel.  Independently, the auxiliary stored by the active carrier is
proved to be an accepted canonical witness for the collapsed spin word whose
head is exactly that summed channel.

The remaining local bridge is to transplant the collapsed witness's internal
coordinates behind this new stretched vertex, producing a complete accepted
source auxiliary labelling.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
import YMGap.Continuum.SU2StretchedTrivalentStrandContinuation

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2StretchedTrivalentStrandContinuation
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

/-! ## 1. Root labels and their stretched input ports -/

def rootLeftSpin
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : Nat :=
  physical (leftRootCopy carrier).faceId

def rootRightSpin
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : Nat :=
  physical (rightRootCopy carrier).faceId

def rootLeftInputPort
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    TrivalentStrandPort (rootLeftSpin carrier) (rootRightSpin carrier)
      (rootLeftSpin carrier + rootRightSpin carrier) :=
  leftInputPort (right := rootRightSpin carrier)
    (leftRootCopy carrier).slot

def rootRightInputPort
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    TrivalentStrandPort (rootLeftSpin carrier) (rootRightSpin carrier)
      (rootLeftSpin carrier + rootRightSpin carrier) :=
  rightInputPort (left := rootLeftSpin carrier)
    (rightRootCopy carrier).slot

def rootLeftSummedPort
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    TrivalentStrandPort (rootLeftSpin carrier) (rootRightSpin carrier)
      (rootLeftSpin carrier + rootRightSpin carrier) :=
  leftSummedPort (right := rootRightSpin carrier)
    (leftRootCopy carrier).slot

def rootRightSummedPort
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    TrivalentStrandPort (rootLeftSpin carrier) (rootRightSpin carrier)
      (rootLeftSpin carrier + rootRightSpin carrier) :=
  rightSummedPort (left := rootLeftSpin carrier)
    (rightRootCopy carrier).slot

theorem rootLeftInputPort_mate
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    canonicalTrivalentPortMate
        (rootLeftSpin carrier) (rootRightSpin carrier)
        (rootLeftSpin carrier + rootRightSpin carrier)
        (fusionOK_stretched (rootLeftSpin carrier) (rootRightSpin carrier))
        (rootLeftInputPort carrier) = rootLeftSummedPort carrier := by
  exact canonicalTrivalentPortMate_stretched_left
    (leftRootCopy carrier).slot

theorem rootRightInputPort_mate
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    canonicalTrivalentPortMate
        (rootLeftSpin carrier) (rootRightSpin carrier)
        (rootLeftSpin carrier + rootRightSpin carrier)
        (fusionOK_stretched (rootLeftSpin carrier) (rootRightSpin carrier))
        (rootRightInputPort carrier) = rootRightSummedPort carrier := by
  exact canonicalTrivalentPortMate_stretched_right
    (rightRootCopy carrier).slot

theorem rootSummedPorts_ne
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootLeftSummedPort carrier ≠ rootRightSummedPort carrier := by
  exact leftSummedPort_ne_rightSummedPort
    (leftRootCopy carrier).slot (rightRootCopy carrier).slot

/-! ## 2. The stored auxiliary accepts the matching collapsed word -/

theorem rootAuxiliary_mem_stretchedFusionWitnesses
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    carrier.rootAuxiliary ∈ cubeInwardMateStretchedFusionWitnesses
      K physical hK hbounded (cubeDebtRootIncidence carrier.word) := by
  have hmem := carrier.rootAuxiliary_mem
  have hpositive := carrier.root_faces_positive
  unfold cubeInwardMateActiveStretchedFusionWitnesses at hmem
  simp only [decide_eq_true hpositive, if_true] at hmem
  exact hmem

theorem rootAuxiliary_mem_collapsedSpins
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    carrier.rootAuxiliary ∈ fusionWitnessesForSpins
      (linkAuxiliaryCutoff K)
      (cubeInwardMateStretchedSpins K physical hK hbounded
        (cubeDebtRootIncidence carrier.word)) := by
  exact rootAuxiliary_mem_stretchedFusionWitnesses carrier

@[simp] theorem rootCollapsedSpins_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    cubeInwardMateStretchedSpins K physical hK hbounded
        (cubeDebtRootIncidence carrier.word) =
      (rootLeftSpin carrier + rootRightSpin carrier) ::
        cubeInwardMateLinkRest K physical hK hbounded
          (cubeDebtRootIncidence carrier.word) := by
  rfl

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.rootLeftInputPort_mate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.rootRightInputPort_mate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.rootSummedPorts_ne
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.rootAuxiliary_mem_collapsedSpins
