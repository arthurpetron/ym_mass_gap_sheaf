/-
# Complete global SU(2) first-stretched congestion contraction

The exact global coarse-key Fubini uses a flat Cartesian coordinate carrier,
while the geometric estimate uses the nested order physical target, cube root,
then peel size.  Finite Cartesian Fubini identifies these totals.  Composing
that identity with the all-physical target-fiber contraction proves that the
entire global first-stretched source mass is at most `384/425` of the genuine
extent-one BF4 physical partition.

This is a partition-relative global bad-event estimate.  It is not a
pointwise conditional row estimate.  Exact total-source normalization and the
complementary all-target event are still required before a `41/425` success
fraction can be inferred; posterior, transfer-operator, completed-gap, and
continuum conclusions remain downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetRootSum

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetCongestion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetRootSum
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSizeTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Flat Cartesian sum equals the nested global sum -/

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B -> Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum (fun a => listQSum (fun b => value (a, b)) right) left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr_on
  intro a _
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- **Exact reconciliation of global summation orders.**  The flat coarse-
block total is the nested physical-target/root/size total used by the
geometric estimate. -/
theorem globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight_eqv_nested
    (K : Nat) (hK : 1 ≤ K) :
    globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight K hK ≈
      globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight K hK := by
  let weight :=
    globalCubeInwardMateFullPeelRepresentativeTargetWeight K (hK := hK)
  let targets := boundedEdgeLabellings K (slabPhysicalFaceEdges 1)
  let roots := centralLowerCubeFaceIds
  let sizes := List.range (cubeInwardMateFullPeelMaxSize K + 1)
  unfold globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight
    globalCubeInwardMateFullPeelTargetBlocksWeight
    cubeInwardMateFullPeelBlockCoordinates
    globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
    globalCubeInwardMateFullPeelTargetRootsStrictRateWeight
    globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight
  change
    listQSum (globalCubeInwardMateFullPeelTargetBlockWeight weight)
        (cartesian targets (cartesian roots sizes)) ≈
      listQSum
        (fun target =>
          listQSum
            (fun rootFaceId =>
              listQSum
                (fun peelSize =>
                  globalCubeInwardMateFullPeelTargetBlockWeight weight
                    (target, (rootFaceId, peelSize))) sizes)
            roots)
        targets
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun rootSize =>
            globalCubeInwardMateFullPeelTargetBlockWeight weight
              (target, rootSize))
          (cartesian roots sizes))
      targets) _
    (listQSum_cartesian_eq_nested_local
      (globalCubeInwardMateFullPeelTargetBlockWeight weight)
      targets (cartesian roots sizes)) ?_
  apply listQSum_congr_on
  intro target _
  exact listQSum_cartesian_eq_nested_local
    (fun rootSize =>
      globalCubeInwardMateFullPeelTargetBlockWeight weight
        (target, rootSize))
    roots sizes

/-! ## 2. The global partition-relative contraction -/

/-- The distinct global realized target sum is bounded by `384/425` of the
genuine physical BF4 partition. -/
theorem globalCubeInwardMateFullPeelRepresentativesStrictRateWeight_le_partition
    {K : Nat} {hK : 1 ≤ K} :
    globalCubeInwardMateFullPeelRepresentativesStrictRateWeight K hK ≤
      Q'.mkPos 384 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 := by
  have hpartition :=
    globalCubeInwardMateFullPeelTargetBlocks_weight_total K hK
  have hnested :=
    globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight_eqv_nested K hK
  have hbound :=
    globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight_le_partition
      (K := K) (hK := hK)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hnested) hbound)

/-- **Complete global first-stretched source contraction.**  The
all-physical first-stretched source mass is at most `384/425` of the physical
partition. -/
theorem globalCubeInwardMateFullSources_weight_sum_le_physicalPartition
    (K : Nat) (hK : 1 ≤ K) :
    listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSources K hK) ≤
      Q'.mkPos 384 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 := by
  have hsources :=
    globalCubeInwardMateFullSources_weight_sum_le_representativeTargets K hK
  have htargets :=
    globalCubeInwardMateFullPeelRepresentativesStrictRateWeight_le_partition
      (K := K) (hK := hK)
  refine Q'.le_trans' _ _ _ hsources ?_
  unfold globalCubeInwardMateFullPeelRepresentativesStrictRateWeight
    globalCubeInwardMateFullPeelRepresentativesWeight at htargets
  exact htargets

/-! ## 3. Witness-bearing global contraction certificate -/

/-- Type-level certificate carrying the strict global finite-volume bad-mass
rate and its checked partition-relative inequality. -/
structure GlobalCubeInwardMateFullPeelPhysicalContractionCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  completeSourceWeight_le :
    listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSources K hK) ≤
      rate * slabParametricKPhysicalPartition anchorCoupling K 1

/-- The explicit global certificate has rate `384/425`, leaving exact
partition-relative slack `41/425` below one. -/
def globalCubeInwardMateFullPeelPhysicalContractionCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalCubeInwardMateFullPeelPhysicalContractionCertificate K hK where
  rate := Q'.mkPos 384 425 (by decide)
  rate_nonnegative := by decide
  rate_lt_one := by decide
  completeSourceWeight_le :=
    globalCubeInwardMateFullSources_weight_sum_le_physicalPartition K hK

#print axioms globalCubeInwardMateFullPeelTargetBlocksStrictRateWeight_eqv_nested
#print axioms globalCubeInwardMateFullPeelRepresentativesStrictRateWeight_le_partition
#print axioms globalCubeInwardMateFullSources_weight_sum_le_physicalPartition
#print axioms GlobalCubeInwardMateFullPeelPhysicalContractionCertificate
#print axioms globalCubeInwardMateFullPeelPhysicalContractionCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetCongestion
