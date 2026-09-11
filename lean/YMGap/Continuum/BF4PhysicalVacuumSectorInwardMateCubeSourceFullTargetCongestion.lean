/-
# Complete SU(2) target congestion contraction

The exact coarse-key Fubini theorem sums blocks over a flat Cartesian carrier.
The geometric argument sums the same blocks in the nested order
physical-target, literal root, then peel size.  Finite Cartesian Fubini proves
those totals equal.  Consequently the entire realized strict-rate target sum,
and hence the complete first-stretched source mass, is bounded by
`384/425` of the genuine extent-one physical BF4 partition.

The final result is packaged as Type-level data carrying its strict rate.  It
is a finite-volume SU(2) contraction at the named strong-coupling anchor; it
is not yet a posterior-variance, transfer-operator, completed spectral-gap,
thermodynamic, continuum, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetRootSum

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCongestion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetRootSum
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetSizeTail
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

/-! ## 1. Flat Cartesian sum equals the nested sum -/

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

/-- **Exact reconciliation of summation orders.**  The flat block total from
the deterministic key partition is the nested target/root/size total used by
the geometric estimate. -/
theorem cubeInwardMateFullPeelTargetBlocksStrictRateWeight_eqv_nested
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    cubeInwardMateFullPeelTargetBlocksStrictRateWeight
        K physical hK hbounded ≈
      cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
        K physical hK hbounded := by
  let weight := cubeInwardMateFullPeelRepresentativeTargetWeight
    K (physical := physical) (hK := hK) (hbounded := hbounded)
  let targets := boundedEdgeLabellings K (slabPhysicalFaceEdges 1)
  let roots := centralLowerCubeFaceIds
  let sizes := List.range (cubeInwardMateFullPeelMaxSize K + 1)
  unfold cubeInwardMateFullPeelTargetBlocksStrictRateWeight
    cubeInwardMateFullPeelTargetBlocksWeight
    cubeInwardMateFullPeelBlockCoordinates
    cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
    cubeInwardMateFullPeelTargetRootsStrictRateWeight
    cubeInwardMateFullPeelTargetRootSizesStrictRateWeight
  change
    listQSum (cubeInwardMateFullPeelTargetBlockWeight weight)
        (cartesian targets (cartesian roots sizes)) ≈
      listQSum
        (fun target =>
          listQSum
            (fun rootFaceId =>
              listQSum
                (fun peelSize =>
                  cubeInwardMateFullPeelTargetBlockWeight weight
                    (target, (rootFaceId, peelSize))) sizes)
            roots)
        targets
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun rootSize =>
            cubeInwardMateFullPeelTargetBlockWeight weight
              (target, rootSize))
          (cartesian roots sizes))
      targets) _
    (listQSum_cartesian_eq_nested_local
      (cubeInwardMateFullPeelTargetBlockWeight weight)
      targets (cartesian roots sizes)) ?_
  apply listQSum_congr_on
  intro target _
  exact listQSum_cartesian_eq_nested_local
    (fun rootSize =>
      cubeInwardMateFullPeelTargetBlockWeight weight (target, rootSize))
    roots sizes

/-! ## 2. The strict physical-partition contraction -/

/-- The distinct realized strict-rate target sum is bounded by `384/425` of
the genuine physical BF4 partition. -/
theorem cubeInwardMateFullPeelRepresentativesStrictRateWeight_le_partition
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    cubeInwardMateFullPeelRepresentativesStrictRateWeight
        K physical hK hbounded <=
      Q'.mkPos 384 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 := by
  have hpartition := cubeInwardMateFullPeelTargetBlocks_weight_total
    K physical hK hbounded hphysical
  have hnested :=
    cubeInwardMateFullPeelTargetBlocksStrictRateWeight_eqv_nested
      K physical hK hbounded
  have hbound :=
    cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight_le_partition
      (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
      hphysical
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hnested) hbound)

/-- **Complete first-stretched source contraction.**  All enumerated
complete-source mass is bounded by the strict physical factor `384/425`. -/
theorem cubeInwardMateFullSources_weight_sum_le_physicalPartition
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    listQSum (cubeInwardMateFullSourceEntryWeight K)
        (enumeratedCubeInwardMateFullSources K physical hK hbounded) <=
      Q'.mkPos 384 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 := by
  have hsources :=
    cubeInwardMateFullSources_weight_sum_le_representativeTargets
      K physical hK hbounded
  have htargets :=
    cubeInwardMateFullPeelRepresentativesStrictRateWeight_le_partition
      (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
      hphysical
  refine Q'.le_trans' _ _ _ hsources ?_
  unfold cubeInwardMateFullPeelRepresentativesStrictRateWeight
    cubeInwardMateFullPeelRepresentativesWeight at htargets
  exact htargets

/-! ## 3. Witness-bearing strict contraction certificate -/

/-- Type-level certificate carrying the strict finite-volume physical
contraction rate and its checked inequality. -/
structure CubeInwardMateFullPeelPhysicalContractionCertificate
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Type where
  rate : Q'
  rate_nonnegative : (0 : Q') <= rate
  rate_lt_one : rate < (1 : Q')
  completeSourceWeight_le :
    listQSum (cubeInwardMateFullSourceEntryWeight K)
        (enumeratedCubeInwardMateFullSources K physical hK hbounded) <=
      rate * slabParametricKPhysicalPartition anchorCoupling K 1

/-- The explicit certificate has rate `384/425`, leaving exact slack
`41/425` below one. -/
def cubeInwardMateFullPeelPhysicalContractionCertificate
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    CubeInwardMateFullPeelPhysicalContractionCertificate
      K physical hK hbounded where
  rate := Q'.mkPos 384 425 (by decide)
  rate_nonnegative := by decide
  rate_lt_one := by decide
  completeSourceWeight_le :=
    cubeInwardMateFullSources_weight_sum_le_physicalPartition
      K physical hK hbounded hphysical

#print axioms cubeInwardMateFullPeelTargetBlocksStrictRateWeight_eqv_nested
#print axioms cubeInwardMateFullPeelRepresentativesStrictRateWeight_le_partition
#print axioms cubeInwardMateFullSources_weight_sum_le_physicalPartition
#print axioms CubeInwardMateFullPeelPhysicalContractionCertificate
#print axioms cubeInwardMateFullPeelPhysicalContractionCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCongestion
