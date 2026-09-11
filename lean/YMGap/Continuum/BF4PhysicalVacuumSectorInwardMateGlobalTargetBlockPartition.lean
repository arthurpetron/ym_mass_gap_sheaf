/-
# Exact global partition by physical target, root, and peel size

The distinct all-physical target representatives are pushed forward to three
coarse coordinates: bounded lowered physical field, literal cube root, and
peel size.  The established finite coordinate carrier covers every global
representative, its serialized keys are duplicate-free, and its deterministic
fibers are exactly the global blocks from the preceding residual-code module.

For the strict-rate target weight this gives exact finite Fubini across all
global target/root/size blocks.  No block-weight or geometric-tail inequality
is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockInjection
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Global coarse keys and coverage -/

/-- The coarse target/root/size key of one global representative. -/
def globalCubeInwardMateFullPeelRepresentativeBlockKey
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    CubeInwardMateFullPeelBlockKey :=
  (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
      representative.adaptiveInverseData.lowerPhysical,
    (representative.adaptiveInverseData.rootFaceId,
      representative.adaptiveInverseData.peelSize))

/-- Every global deterministic peel lies below the established total
physical-strand ceiling. -/
theorem globalCubeInwardMateFullPeelRepresentative_peelSize_le
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    representative.adaptiveInverseData.peelSize ≤
      cubeInwardMateFullPeelMaxSize K :=
  EnumeratedCubeInwardMateFullSource.adaptiveInverseData_peelSize_le
    representative.entry

/-- Every global representative key occurs in the complete bounded
physical-target/root/size coordinate carrier. -/
theorem globalCubeInwardMateFullPeelRepresentativeBlockKey_mem
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    globalCubeInwardMateFullPeelRepresentativeBlockKey representative ∈
      (cubeInwardMateFullPeelBlockCoordinates K).map
        cubeInwardMateFullPeelBlockCoordinateKey := by
  apply List.mem_map.mpr
  let coordinate : CubeInwardMateFullPeelBlockCoordinate :=
    (representative.adaptiveInverseData.lowerPhysical,
      (representative.adaptiveInverseData.rootFaceId,
        representative.adaptiveInverseData.peelSize))
  refine ⟨coordinate, ?_, rfl⟩
  unfold cubeInwardMateFullPeelBlockCoordinates
  exact (YMGap.Continuum.FiniteWeightedCartesianInjection.mem_cartesian_iff
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (YMGap.Continuum.FiniteWeightedCartesianInjection.cartesian
      centralLowerCubeFaceIds
      (List.range (cubeInwardMateFullPeelMaxSize K + 1))) coordinate).mpr
    ⟨representative.lowerPhysical_mem,
      (YMGap.Continuum.FiniteWeightedCartesianInjection.mem_cartesian_iff
        centralLowerCubeFaceIds
        (List.range (cubeInwardMateFullPeelMaxSize K + 1)) coordinate.2).mpr
        ⟨representative.rootFaceId_mem_cube,
          List.mem_range.mpr (Nat.lt_succ_of_le
            (globalCubeInwardMateFullPeelRepresentative_peelSize_le
              representative))⟩⟩

/-! ## 2. Literal fibers and scalar boundaries -/

/-- The deterministic global coarse-key fiber is literally the global
physical-target/root/size block. -/
theorem globalCubeInwardMateFullPeelBlock_fiberWeight_eq
    {K : Nat} {hK : 1 ≤ K}
    (weight : GlobalEnumeratedCubeInwardMateFullSource K hK -> Q')
    (target : EdgeLabelling) (rootFaceId peelSize : Nat) :
    fiberWeight
        (globalCubeInwardMateFullPeelTargetRepresentatives K hK)
        weight globalCubeInwardMateFullPeelRepresentativeBlockKey
        (cubeInwardMateFullPeelBlockCoordinateKey
          (target, (rootFaceId, peelSize))) =
      listQSum weight
        (globalCubeInwardMateFullPeelTargetBlockRepresentatives
          K hK target rootFaceId peelSize) := by
  unfold fiberWeight
    globalCubeInwardMateFullPeelTargetBlockRepresentatives
  apply congrArg (listQSum weight)
  apply List.filter_congr
  intro representative _
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hkey
    have hkey' := of_decide_eq_true hkey
    have hword := congrArg Prod.fst hkey'
    have hrootSize := congrArg Prod.snd hkey'
    have hroot := congrArg Prod.fst hrootSize
    have hsize := congrArg Prod.snd hrootSize
    apply decide_eq_true
    exact ⟨hroot.symm, hsize.symm, hword.symm⟩
  · intro hblock
    have hblock' := of_decide_eq_true hblock
    apply decide_eq_true
    apply Prod.ext
    · exact hblock'.2.2.symm
    · apply Prod.ext
      · exact hblock'.1.symm
      · exact hblock'.2.1.symm

/-- Exact weight of one global coarse coordinate block. -/
def globalCubeInwardMateFullPeelTargetBlockWeight
    {K : Nat} {hK : 1 ≤ K}
    (weight : GlobalEnumeratedCubeInwardMateFullSource K hK -> Q')
    (coordinate : CubeInwardMateFullPeelBlockCoordinate) : Q' :=
  listQSum weight
    (globalCubeInwardMateFullPeelTargetBlockRepresentatives
      K hK coordinate.1 coordinate.2.1 coordinate.2.2)

/-- Total weight of all global target/root/size blocks. -/
def globalCubeInwardMateFullPeelTargetBlocksWeight
    {K : Nat} {hK : 1 ≤ K}
    (weight : GlobalEnumeratedCubeInwardMateFullSource K hK -> Q') : Q' :=
  listQSum (globalCubeInwardMateFullPeelTargetBlockWeight weight)
    (cubeInwardMateFullPeelBlockCoordinates K)

/-- Total weight of the distinct global target representatives. -/
def globalCubeInwardMateFullPeelRepresentativesWeight
    {K : Nat} {hK : 1 ≤ K}
    (weight : GlobalEnumeratedCubeInwardMateFullSource K hK -> Q') : Q' :=
  listQSum weight (globalCubeInwardMateFullPeelTargetRepresentatives K hK)

/-- Strict-rate target weight summed over all literal global coarse blocks. -/
def globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  globalCubeInwardMateFullPeelTargetBlocksWeight
    (globalCubeInwardMateFullPeelRepresentativeTargetWeight K (hK := hK))

/-- The same strict-rate target weight summed over distinct global
representatives. -/
def globalCubeInwardMateFullPeelRepresentativesStrictRateWeight
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  globalCubeInwardMateFullPeelRepresentativesWeight
    (globalCubeInwardMateFullPeelRepresentativeTargetWeight K (hK := hK))

/-! ## 3. Exact global coarse-block Fubini -/

/-- **Exact global target/root/size partition.**  Summing every literal
coarse block recovers the full distinct-representative target weight. -/
theorem globalCubeInwardMateFullPeelTargetBlocks_weight_total
    (K : Nat) (hK : 1 ≤ K) :
    globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight K hK ≈
      globalCubeInwardMateFullPeelRepresentativesStrictRateWeight K hK := by
  let weight :=
    globalCubeInwardMateFullPeelRepresentativeTargetWeight K (hK := hK)
  apply finiteCoordinateFiberWeight_total
    (globalCubeInwardMateFullPeelTargetRepresentatives K hK)
    weight (cubeInwardMateFullPeelBlockCoordinates K)
    globalCubeInwardMateFullPeelRepresentativeBlockKey
    cubeInwardMateFullPeelBlockCoordinateKey
    (globalCubeInwardMateFullPeelTargetBlockWeight weight)
  · exact cubeInwardMateFullPeelBlockCoordinateKeys_nodup K
  · exact fun representative _ =>
      globalCubeInwardMateFullPeelRepresentativeBlockKey_mem representative
  · intro coordinate _
    exact Q'.eqv_of_eq
      (globalCubeInwardMateFullPeelBlock_fiberWeight_eq
        weight coordinate.1 coordinate.2.1 coordinate.2.2).symm

#print axioms globalCubeInwardMateFullPeelRepresentativeBlockKey
#print axioms globalCubeInwardMateFullPeelRepresentative_peelSize_le
#print axioms globalCubeInwardMateFullPeelRepresentativeBlockKey_mem
#print axioms globalCubeInwardMateFullPeelBlock_fiberWeight_eq
#print axioms globalCubeInwardMateFullPeelTargetBlockWeight
#print axioms globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight
#print axioms globalCubeInwardMateFullPeelTargetBlocks_weight_total

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockPartition
