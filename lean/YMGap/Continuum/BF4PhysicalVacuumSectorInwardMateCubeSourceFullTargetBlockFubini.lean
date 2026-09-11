/-
# Exact Fubini across physical-target/root/size blocks

The preceding module constructs a duplicate-free finite carrier of coarse
block keys, proves that it covers every realized target representative, and
identifies each deterministic key fiber with the literal block.  This module
contracts those interfaces through the generic finite pushforward theorem.

The module boundary is deliberate: it keeps the large dependent source
compiler opaque while the final exact partition is assembled.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockFubini

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Opaque strict-rate scalar boundaries -/

/-- Sum of the strict-rate target weight over all literal coarse blocks. -/
def cubeInwardMateFullPeelTargetBlocksStrictRateWeight
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Q' :=
  cubeInwardMateFullPeelTargetBlocksWeight
    (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
    (cubeInwardMateFullPeelRepresentativeTargetWeight
      K (physical := physical) (hK := hK) (hbounded := hbounded))

/-- Sum of the same strict-rate target weight over realized representatives. -/
def cubeInwardMateFullPeelRepresentativesStrictRateWeight
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Q' :=
  cubeInwardMateFullPeelRepresentativesWeight
    (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
    (cubeInwardMateFullPeelRepresentativeTargetWeight
      K (physical := physical) (hK := hK) (hbounded := hbounded))

/-! ## 2. Exact deterministic Fubini -/

/-- **Exact target/root/size partition for the strict-rate target weight.**
Summing all literal coarse blocks recovers the entire realized representative
target weight. -/
theorem cubeInwardMateFullPeelTargetBlocks_weight_total
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    cubeInwardMateFullPeelTargetBlocksStrictRateWeight
        K physical hK hbounded ≈
      cubeInwardMateFullPeelRepresentativesStrictRateWeight
        K physical hK hbounded := by
  let weight := cubeInwardMateFullPeelRepresentativeTargetWeight
    K (physical := physical) (hK := hK) (hbounded := hbounded)
  apply finiteCoordinateFiberWeight_total
    (cubeInwardMateFullPeelTargetRepresentatives
      K physical hK hbounded)
    weight (cubeInwardMateFullPeelBlockCoordinates K)
    cubeInwardMateFullPeelRepresentativeBlockKey
    cubeInwardMateFullPeelBlockCoordinateKey
    (cubeInwardMateFullPeelTargetBlockWeight weight)
  · exact
    (cubeInwardMateFullPeelBlockCoordinateKeys_nodup K)
  · exact fun representative _ =>
      cubeInwardMateFullPeelRepresentativeBlockKey_mem
        hphysical representative
  · intro coordinate _
    exact Q'.eqv_of_eq
      (cubeInwardMateFullPeelBlock_fiberWeight_eq
        weight coordinate.1 coordinate.2.1 coordinate.2.2).symm

#print axioms cubeInwardMateFullPeelTargetBlocksStrictRateWeight
#print axioms cubeInwardMateFullPeelRepresentativesStrictRateWeight
#print axioms cubeInwardMateFullPeelTargetBlocks_weight_total

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockFubini
