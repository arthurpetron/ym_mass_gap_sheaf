/-
# Weighted raw-row replication gate for the matched spin-cube ray

The exact replication compiler asks every replica row to dominate its source
row.  That factor-one condition is stronger than the available slab geometry:
disjoint support factorisation controls individual production terms, but does
not compare the complete reflected row sums.  This file isolates the precise
weaker certificate that is sufficient.

For every excited spin-cube source, inject `R` distinct physical lower states
whose raw rows dominate `lambda` times the source row.  The physical partition
then pays the effective multiplicity `R * lambda`:

  exactRawRayNumerator * (R * lambda) <= physicalPartition.

Consequently the normalized ray mass is at most `1 / (R * lambda)`.  A matched
family only needs that effective reciprocal, rather than `1 / R`, to have a
located zero tail.  Factor-one replication embeds as the special case
`lambda = 1`.

No weighted replica family is constructed here.  The remaining producer is a
literal injection plus a quantitative raw-row floor whose effective
multiplicity diverges.  No finite gap, continuum theory, or Clay conclusion is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.FiniteBistochasticCarrierBalance
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_pos_of_pos_local {value : Nat}
    (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  cases value with
  | zero => contradiction
  | succ predecessor => exact Q'.ofNat_succ_pos predecessor

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

/-! ## 1. Finite weighted replication certificate -/

/-- `replicaCount` distinct physical rows for every excited spin-cube source,
each carrying at least `replicaFloor` times that source's raw row mass. -/
structure CentralLowerExcitedSpinCubeWeightedRawReplication
    (w : Q') (hw0 : (0 : Q') < w) (K : Nat) : Type where
  replicaCount : Nat
  replicaCount_pos : 0 < replicaCount
  replicaFloor : Q'
  replicaFloor_pos : (0 : Q') < replicaFloor
  encode : Nat × Nat → EdgeLabelling
  encode_mem : ∀ offset replica,
    offset < K → replica < replicaCount →
      encode (offset, replica) ∈ centralHalfStates K 0
  encode_injective : ∀ left right,
    left.1 < K → left.2 < replicaCount →
    right.1 < K → right.2 < replicaCount →
    encode left = encode right → left = right
  scaledRawRow_le : ∀ offset replica,
    offset < K → replica < replicaCount →
      centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K 0
          (centralLowerSpinCubeState (offset + 1)) * replicaFloor ≤
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K 0
          (encode (offset, replica))

namespace CentralLowerExcitedSpinCubeWeightedRawReplication

/-- The number of replicas multiplied by their common raw-row floor. -/
def effectiveMultiplicity
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K) : Q' :=
  Q'.ofNat replication.replicaCount * replication.replicaFloor

theorem effectiveMultiplicity_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K) :
    (0 : Q') < replication.effectiveMultiplicity := by
  exact Q'.mul_pos
    (ofNat_pos_of_pos_local replication.replicaCount_pos)
    replication.replicaFloor_pos

/-- A weighted Cartesian injection makes the full physical partition pay the
exact ray numerator times the effective multiplicity `R * lambda`. -/
theorem exactRawNumerator_mul_effectiveMultiplicity_le_partition
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K) :
    centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K *
        replication.effectiveMultiplicity ≤
      slabParametricKPhysicalPartition w K (centralExtent 0) := by
  let offsets := List.range K
  let replicas := List.range replication.replicaCount
  let source := cartesian offsets replicas
  let target := centralHalfStates K 0
  let leftWeight := fun offset =>
    centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0
      (centralLowerSpinCubeState (offset + 1))
  let scaledLeftWeight := fun offset =>
    leftWeight offset * replication.replicaFloor
  let sourceWeight := fun pair : Nat × Nat => scaledLeftWeight pair.1
  let targetWeight :=
    centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0
  have hinjected : listQSum sourceWeight source ≤
      centralPhysicalPositiveRawSourceMass
        w (Q'.le_of_lt hw0) K 0 := by
    unfold centralPhysicalPositiveRawSourceMass
    apply listQSum_le_of_injective_nodup
      source target sourceWeight targetWeight replication.encode
    · exact cartesian_nodup offsets replicas
        (rangeNodupLocal K)
        (rangeNodupLocal replication.replicaCount)
    · exact centralHalfStates_nodup K 0
    · intro pair hpair
      have hparts := (mem_cartesian_iff offsets replicas pair).mp hpair
      exact replication.encode_mem pair.1 pair.2
        (List.mem_range.mp hparts.1)
        (List.mem_range.mp hparts.2)
    · intro left hleft right hright heq
      have hleftParts :=
        (mem_cartesian_iff offsets replicas left).mp hleft
      have hrightParts :=
        (mem_cartesian_iff offsets replicas right).mp hright
      exact replication.encode_injective left right
        (List.mem_range.mp hleftParts.1)
        (List.mem_range.mp hleftParts.2)
        (List.mem_range.mp hrightParts.1)
        (List.mem_range.mp hrightParts.2) heq
    · intro pair hpair
      have hparts := (mem_cartesian_iff offsets replicas pair).mp hpair
      exact replication.scaledRawRow_le pair.1 pair.2
        (List.mem_range.mp hparts.1)
        (List.mem_range.mp hparts.2)
    · intro state _hstate
      exact centralPhysicalPositiveRawRowMass_nonnegative
        (Q'.le_of_lt hw0) K 0 state
  have hsource :
      listQSum sourceWeight source ≈
        (centralLowerExcitedSpinCubeExactRawNumerator
            w (Q'.le_of_lt hw0) K * replication.replicaFloor) *
          Q'.ofNat replication.replicaCount := by
    refine Q'.eqv_trans _
      (listQSum
        (fun pair : Nat × Nat => scaledLeftWeight pair.1 * (1 : Q'))
        source) _ ?_ ?_
    · apply listQSum_congr_on
      intro pair _hpair
      exact Q'.eqv_symm (Q'.mul_one_eqv (scaledLeftWeight pair.1))
    · refine Q'.eqv_trans _
        (listQSum scaledLeftWeight offsets *
          listQSum (fun _ : Nat => (1 : Q')) replicas) _
        (listQSum_cartesian_product
          scaledLeftWeight (fun _ : Nat => (1 : Q')) offsets replicas) ?_
      have hleft :
          listQSum scaledLeftWeight offsets ≈
            centralLowerExcitedSpinCubeExactRawNumerator
                w (Q'.le_of_lt hw0) K * replication.replicaFloor := by
        exact Q'.eqv_trans _ _ _
          (listQSum_mul_right leftWeight replication.replicaFloor offsets)
          (Q'.mul_eqv_congr_right _ _ replication.replicaFloor (by
            unfold leftWeight offsets
            unfold centralLowerExcitedSpinCubeExactRawNumerator
            exact Q'.eqv_refl _))
      have hright :
          listQSum (fun _ : Nat => (1 : Q')) replicas ≈
            Q'.ofNat replication.replicaCount :=
        Q'.eqv_trans _ _ _
          (listQSum_one_eqv_ofNat_length replicas)
          (by
            unfold replicas
            simp only [List.length_range]
            exact Q'.eqv_refl _)
      exact Q'.eqv_trans _
        ((centralLowerExcitedSpinCubeExactRawNumerator
            w (Q'.le_of_lt hw0) K * replication.replicaFloor) *
          listQSum (fun _ : Nat => (1 : Q')) replicas) _
        (Q'.mul_eqv_congr_right _ _ _ hleft)
        (Q'.mul_eqv_congr_left _ _ _ hright)
  have hsourceBound :
      (centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K * replication.replicaFloor) *
          Q'.ofNat replication.replicaCount ≤
        centralPhysicalPositiveRawSourceMass
          w (Q'.le_of_lt hw0) K 0 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource) hinjected
  have hreassociate :
      centralLowerExcitedSpinCubeExactRawNumerator
            w (Q'.le_of_lt hw0) K *
          replication.effectiveMultiplicity ≈
        (centralLowerExcitedSpinCubeExactRawNumerator
            w (Q'.le_of_lt hw0) K * replication.replicaFloor) *
          Q'.ofNat replication.replicaCount := by
    unfold effectiveMultiplicity
    exact Q'.eqv_trans _
      (centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K *
        (replication.replicaFloor *
          Q'.ofNat replication.replicaCount)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv
          (Q'.ofNat replication.replicaCount)
          replication.replicaFloor))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hreassociate)
    (Q'.le_trans' _ _ _ hsourceBound
      (Q'.le_of_eqv
        (centralPhysicalPositiveRawSourceMass_eqv_partition
          w (Q'.le_of_lt hw0) K 0)))

/-- Weighted replication bounds normalized ray mass by the reciprocal of the
effective multiplicity, not merely by the reciprocal replica count. -/
theorem rayMass_le_reciprocalEffectiveMultiplicity
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K) :
    centralLowerExcitedSpinCubeRayMass
        w (Q'.le_of_lt hw0) K ≤
      Q'.divPos 1 replication.effectiveMultiplicity
        replication.effectiveMultiplicity_pos := by
  let numerator := centralLowerExcitedSpinCubeExactRawNumerator
    w (Q'.le_of_lt hw0) K
  let partition := slabParametricKPhysicalPartition w K (centralExtent 0)
  let effective := replication.effectiveMultiplicity
  let heffective : (0 : Q') < effective :=
    replication.effectiveMultiplicity_pos
  let epsilon := Q'.divPos 1 effective heffective
  have hmul : numerator * effective ≤ partition :=
    replication.exactRawNumerator_mul_effectiveMultiplicity_le_partition
  have hdiv : numerator ≤ Q'.divPos partition effective heffective :=
    Q'.le_divPos_of_mul_le partition effective heffective hmul
  have hreassociate :
      Q'.divPos partition effective heffective ≈
        epsilon * partition := by
    unfold epsilon Q'.divPos
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv partition (Q'.recipPos effective heffective))
      (Q'.eqv_symm
        (Q'.mul_eqv_congr_right
          (1 * Q'.recipPos effective heffective)
          (Q'.recipPos effective heffective) partition
          (Q'.one_mul_eqv (Q'.recipPos effective heffective))))
  apply
    (centralLowerExcitedSpinCubeRayMass_le_iff_exactPartitionDomination
      hw0 K epsilon).mpr
  exact Q'.le_trans' _ _ _ hdiv (Q'.le_of_eqv hreassociate)

end CentralLowerExcitedSpinCubeWeightedRawReplication

/-! ## 2. Factor-one replication is the unit-floor special case -/

def CentralLowerExcitedSpinCubeExactRawReplication.toWeighted
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubeExactRawReplication w hw0 K) :
    CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K where
  replicaCount := replication.replicaCount
  replicaCount_pos := replication.replicaCount_pos
  replicaFloor := 1
  replicaFloor_pos := by decide
  encode := replication.encode
  encode_mem := replication.encode_mem
  encode_injective := replication.encode_injective
  scaledRawRow_le := by
    intro offset replica hoffset hreplica
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
      (replication.rawRow_le offset replica hoffset hreplica)

/-! ## 3. Matched weighted replication family -/

/-- A matched finite-replica family whose reciprocal effective multiplicity
has a located zero tail. -/
structure MatchedDyadicExcitedSpinCubeWeightedRawReplicationFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  replication : ∀ scale,
    CentralLowerExcitedSpinCubeWeightedRawReplication
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
  rate : Q' → Nat
  reciprocalEffectiveMultiplicity_le :
    ∀ epsilon, (0 : Q') < epsilon →
      ∀ scale, rate epsilon ≤ scale →
        Q'.divPos 1
            (replication scale).effectiveMultiplicity
            (replication scale).effectiveMultiplicity_pos ≤
          epsilon

def MatchedDyadicExcitedSpinCubeWeightedRawReplicationFamily.toRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (replicas :
      MatchedDyadicExcitedSpinCubeWeightedRawReplicationFamily bridge) :
    MatchedDyadicExcitedSpinCubeRayMassTailZero bridge where
  rate := replicas.rate
  rayMass_le := by
    intro epsilon hepsilon scale hscale
    exact Q'.le_trans' _ _ _
      ((replicas.replication scale).rayMass_le_reciprocalEffectiveMultiplicity)
      (replicas.reciprocalEffectiveMultiplicity_le
        epsilon hepsilon scale hscale)

/-- Divergent effective multiplicity excludes the cutoff-uniform assigned
stationary-ratio route. -/
theorem weightedReplicationFamily_excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (replicas :
      MatchedDyadicExcitedSpinCubeWeightedRawReplicationFamily bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  tailZero_excludes_cofinalAssignedRatio replicas.toRayMassTailZero

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate.CentralLowerExcitedSpinCubeWeightedRawReplication.exactRawNumerator_mul_effectiveMultiplicity_le_partition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate.CentralLowerExcitedSpinCubeWeightedRawReplication.rayMass_le_reciprocalEffectiveMultiplicity
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate.CentralLowerExcitedSpinCubeExactRawReplication.toWeighted
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate.MatchedDyadicExcitedSpinCubeWeightedRawReplicationFamily.toRayMassTailZero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate.weightedReplicationFamily_excludes_cofinalAssignedRatio
