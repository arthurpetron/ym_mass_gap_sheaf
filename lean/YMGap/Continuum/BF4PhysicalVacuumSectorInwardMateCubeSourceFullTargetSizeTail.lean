/-
# Exact size-two tail for one physical target and root

Every realized deterministic peel removes at least its two distinct certified
root faces.  Hence the coarse blocks at sizes zero and one are empty.  For one
fixed bounded physical target and one fixed root, the weighted block-capacity
theorem can therefore be summed with the exact adaptive anchor tail beginning
at size two.  The resulting factor is `64/425`, independently of the cutoff.

This module does not yet sum over the six roots or over physical targets.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound
import YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetSizeTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two impossible size blocks -/

/-- A coarse block below size two is empty. -/
theorem cubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (target : EdgeLabelling) (rootFaceId peelSize : Nat)
    (hsize : peelSize < 2) :
    cubeInwardMateFullPeelTargetBlockRepresentatives
      K physical hK hbounded target rootFaceId peelSize = [] := by
  cases hblock : cubeInwardMateFullPeelTargetBlockRepresentatives
      K physical hK hbounded target rootFaceId peelSize with
  | nil => rfl
  | cons representative rest =>
      have hrepresentative : representative ∈
          cubeInwardMateFullPeelTargetBlockRepresentatives
            K physical hK hbounded target rootFaceId peelSize := by
        rw [hblock]
        exact List.mem_cons_self
      have hspec := cubeInwardMateFullPeelTargetBlockRepresentatives_spec
        representative hrepresentative
      have htwo :=
        EnumeratedCubeInwardMateFullSource.two_le_adaptiveInverseData_peelSize
          representative
      rw [hspec.2.1] at htwo
      omega

/-! ## 2. The fixed-target/root size sum -/

/-- Opaque scalar boundary for the strict-rate sum over every allowed peel
size at one fixed physical target and root. -/
def cubeInwardMateFullPeelTargetRootSizesStrictRateWeight
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (target : EdgeLabelling) (rootFaceId : Nat) : Q' :=
  listQSum
    (fun peelSize =>
      cubeInwardMateFullPeelTargetBlockWeight
        (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
        (cubeInwardMateFullPeelRepresentativeTargetWeight
          K (physical := physical) (hK := hK) (hbounded := hbounded))
        (target, (rootFaceId, peelSize)))
    (List.range (cubeInwardMateFullPeelMaxSize K + 1))

/-- The exact physical target-block weight is nonnegative. -/
theorem cubeInwardMateFixedOrderTargetBlockWeight_nonnegative
    (K : Nat) (target : EdgeLabelling) :
    (0 : Q') <= cubeInwardMateFixedOrderTargetBlockWeight
      anchorCoupling K target := by
  unfold cubeInwardMateFixedOrderTargetBlockWeight
  apply listQSum_nonnegative_on
  intro _ _
  exact cubeInwardMateFixedOrderTargetBlockEntryWeight_nonnegative K target

/-- **Fixed target/root size-tail contraction.**  Summing all allowed size
blocks costs at most `64/425` of the exact physical target-block weight. -/
theorem cubeInwardMateFullPeelTargetRootSizesStrictRateWeight_le
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (target : EdgeLabelling) (rootFaceId : Nat)
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    cubeInwardMateFullPeelTargetRootSizesStrictRateWeight
        K physical hK hbounded target rootFaceId <=
      Q'.mkPos 64 425 (by decide) *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let value : Nat -> Q' := fun peelSize =>
    cubeInwardMateFullPeelTargetBlockWeight
      (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
      (cubeInwardMateFullPeelRepresentativeTargetWeight
        K (physical := physical) (hK := hK) (hbounded := hbounded))
      (target, (rootFaceId, peelSize))
  let scalar := cubeInwardMateFixedOrderTargetBlockWeight
    anchorCoupling K target
  unfold cubeInwardMateFullPeelTargetRootSizesStrictRateWeight
  change listQSum value
      (List.range (cubeInwardMateFullPeelMaxSize K + 1)) <=
    Q'.mkPos 64 425 (by decide) * scalar
  apply listQSum_range_succ_le_componentAdaptiveEntropyAnchor_twoTail
    value scalar
  · unfold value cubeInwardMateFullPeelTargetBlockWeight
    rw [cubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
      target rootFaceId 0 (by omega)]
    exact Q'.eqv_refl 0
  · unfold value cubeInwardMateFullPeelTargetBlockWeight
    rw [cubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
      target rootFaceId 1 (by omega)]
    exact Q'.eqv_refl 0
  · exact cubeInwardMateFixedOrderTargetBlockWeight_nonnegative K target
  · intro index
    exact cubeInwardMateFullPeelTargetBlockWeight_le_physicalBlock
      hphysical target rootFaceId (index + 2) htarget

#print axioms cubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
#print axioms cubeInwardMateFullPeelTargetRootSizesStrictRateWeight
#print axioms cubeInwardMateFixedOrderTargetBlockWeight_nonnegative
#print axioms cubeInwardMateFullPeelTargetRootSizesStrictRateWeight_le

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetSizeTail
