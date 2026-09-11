/-
# Exact size-two tail for one global target and root

Every global first-stretched peel removes at least its two certified root
faces, so the size-zero and size-one coarse blocks are empty.  Summing the
weighted global block bound from size two onward therefore gives the exact
cutoff-independent factor `64/425` for one bounded lowered physical target and
one cube root.

This module does not yet sum the six roots or the bounded physical targets.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockWeightBound
import YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSizeTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetSizeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockWeightBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini
open YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The two impossible global size blocks -/

/-- A global coarse block below size two is empty. -/
theorem globalCubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
    {K : Nat} {hK : 1 ≤ K}
    (target : EdgeLabelling) (rootFaceId peelSize : Nat)
    (hsize : peelSize < 2) :
    globalCubeInwardMateFullPeelTargetBlockRepresentatives
      K hK target rootFaceId peelSize = [] := by
  cases hblock : globalCubeInwardMateFullPeelTargetBlockRepresentatives
      K hK target rootFaceId peelSize with
  | nil => rfl
  | cons representative rest =>
      have hrepresentative : representative ∈
          globalCubeInwardMateFullPeelTargetBlockRepresentatives
            K hK target rootFaceId peelSize := by
        rw [hblock]
        exact List.mem_cons_self
      have hspec :=
        globalCubeInwardMateFullPeelTargetBlockRepresentatives_spec
          representative hrepresentative
      have htwo := representative.two_le_peelSize
      rw [hspec.2.1] at htwo
      omega

/-! ## 2. The fixed global target/root size sum -/

/-- Strict-rate sum over every allowed peel size at one fixed global target
and root. -/
def globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight
    (K : Nat) (hK : 1 ≤ K)
    (target : EdgeLabelling) (rootFaceId : Nat) : Q' :=
  listQSum
    (fun peelSize =>
      globalCubeInwardMateFullPeelTargetBlockWeight
        (globalCubeInwardMateFullPeelRepresentativeTargetWeight
          K (hK := hK))
        (target, (rootFaceId, peelSize)))
    (List.range (cubeInwardMateFullPeelMaxSize K + 1))

/-- **Global fixed target/root size-tail contraction.**  Summing all allowed
global size blocks costs at most `64/425` of the exact physical target-block
weight. -/
theorem globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight_le
    {K : Nat} {hK : 1 ≤ K}
    (target : EdgeLabelling) (rootFaceId : Nat)
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight
        K hK target rootFaceId ≤
      Q'.mkPos 64 425 (by decide) *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let value : Nat -> Q' := fun peelSize =>
    globalCubeInwardMateFullPeelTargetBlockWeight
      (globalCubeInwardMateFullPeelRepresentativeTargetWeight
        K (hK := hK))
      (target, (rootFaceId, peelSize))
  let scalar := cubeInwardMateFixedOrderTargetBlockWeight
    anchorCoupling K target
  unfold globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight
  change listQSum value
      (List.range (cubeInwardMateFullPeelMaxSize K + 1)) ≤
    Q'.mkPos 64 425 (by decide) * scalar
  apply listQSum_range_succ_le_componentAdaptiveEntropyAnchor_twoTail
    value scalar
  · unfold value globalCubeInwardMateFullPeelTargetBlockWeight
    rw [globalCubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
      target rootFaceId 0 (by omega)]
    exact Q'.eqv_refl 0
  · unfold value globalCubeInwardMateFullPeelTargetBlockWeight
    rw [globalCubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
      target rootFaceId 1 (by omega)]
    exact Q'.eqv_refl 0
  · exact cubeInwardMateFixedOrderTargetBlockWeight_nonnegative K target
  · intro index
    exact globalCubeInwardMateFullPeelTargetBlockWeight_le_physicalBlock
      target rootFaceId (index + 2) htarget

#print axioms globalCubeInwardMateFullPeelTargetBlockRepresentatives_eq_nil_of_lt_two
#print axioms globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight
#print axioms globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight_le

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSizeTail
