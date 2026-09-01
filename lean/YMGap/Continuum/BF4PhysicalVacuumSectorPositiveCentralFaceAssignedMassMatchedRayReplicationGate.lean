/-
# Raw-row replication gate for the matched spin-cube ray

The exact ray numerator is a sum of raw reflected row masses, while the full
physical partition is the sum of all raw source-row masses.  This file proves
that identity and gives a concrete finite mechanism for making the ray rare:
inject `R` distinct, raw-row-dominating replicas of every excited spin-cube
source into the complete lower-state carrier.  Such a replication forces

  R * exactRawRayNumerator <= physicalPartition

and hence `rayMass <= 1/R`.

A matched family whose located replica reciprocals tend to zero therefore
constructs ray-mass tail zero and excludes the cutoff-uniform assigned-ratio
route.  No replica family is constructed here; the remaining work is the
geometric/representation-theoretic construction of those literal states and
their raw-row comparisons.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate
import YMGap.Continuum.FiniteBistochasticCarrierBalance

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBistochasticCarrierBalance
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
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

/-! ## 1. The full raw source budget is the physical partition -/

/-- Sum of the literal positive raw-row masses over every lower state. -/
def centralPhysicalPositiveRawSourceMass
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Q' :=
  listQSum
    (centralPhysicalPositiveRawRowMass w hw K half)
    (centralHalfStates K half)

/-- The complete raw source-row mass is exactly the corrected-slab physical
partition. -/
theorem centralPhysicalPositiveRawSourceMass_eqv_partition
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    centralPhysicalPositiveRawSourceMass w hw K half ≈
      slabParametricKPhysicalPartition w K (centralExtent half) := by
  let states := centralHalfStates K half
  let raw := centralPhysicalPositiveRawRowMass w hw K half
  let partition := slabParametricKPhysicalPartition
    w K (centralExtent half)
  let hpartition := slabParametricKPhysicalPartition_pos
    hw K (centralExtent half)
  let reciprocal := centralPhysicalFiniteVacuumSectorPartitionReciprocal
    w hw K half
  have hrows :
      listQSum (centralPhysicalRowMarginal w hw K half) states ≈
        listQSum (fun source => raw source * reciprocal) states := by
    apply listQSum_congr_on
    intro source hsource
    exact centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      (w := w) (hw := hw) (K := K) (half := half)
      (source := source) hsource
  have hfactor :
      listQSum (fun source => raw source * reciprocal) states ≈
        centralPhysicalPositiveRawSourceMass w hw K half * reciprocal := by
    exact Q'.eqv_trans _ _ _
      (listQSum_mul_right raw reciprocal states)
      (Q'.mul_eqv_congr_right _ _ reciprocal (by
        unfold centralPhysicalPositiveRawSourceMass
        exact Q'.eqv_refl _))
  have hnormalized :
      centralPhysicalPositiveRawSourceMass w hw K half * reciprocal ≈
        1 := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm hfactor)
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm hrows)
        (centralPhysicalRowMarginal_total_one w hw K half))
  have hreciprocal : reciprocal * partition ≈ 1 := by
    unfold reciprocal
      centralPhysicalFiniteVacuumSectorPartitionReciprocal
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (Q'.recipPos partition hpartition) partition)
      (Q'.mul_recipPos_eqv partition hpartition)
  have hleft :
      (centralPhysicalPositiveRawSourceMass w hw K half * reciprocal) *
          partition ≈
        centralPhysicalPositiveRawSourceMass w hw K half := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv
        (centralPhysicalPositiveRawSourceMass w hw K half)
        reciprocal partition)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hreciprocal)
        (Q'.mul_one_eqv _))
  have hscaled := Q'.mul_eqv_congr_right _ _ partition hnormalized
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hscaled (Q'.one_mul_eqv partition))

/-! ## 2. A finite raw-row replication certificate -/

/-- `replicaCount` distinct target states for every excited spin-cube source,
all lying in the complete lower carrier and each carrying at least the raw row
mass of its source. -/
structure CentralLowerExcitedSpinCubeExactRawReplication
    (w : Q') (hw0 : (0 : Q') < w) (K : Nat) : Type where
  replicaCount : Nat
  replicaCount_pos : 0 < replicaCount
  encode : Nat × Nat → EdgeLabelling
  encode_mem : ∀ offset replica,
    offset < K → replica < replicaCount →
      encode (offset, replica) ∈ centralHalfStates K 0
  encode_injective : ∀ left right,
    left.1 < K → left.2 < replicaCount →
    right.1 < K → right.2 < replicaCount →
    encode left = encode right → left = right
  rawRow_le : ∀ offset replica,
    offset < K → replica < replicaCount →
      centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K 0
          (centralLowerSpinCubeState (offset + 1)) ≤
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K 0
          (encode (offset, replica))

namespace CentralLowerExcitedSpinCubeExactRawReplication

/-- The injected Cartesian replica family pays `replicaCount` copies of the
complete exact ray numerator from the one physical partition. -/
theorem replicaCount_mul_exactRawNumerator_le_partition
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubeExactRawReplication w hw0 K) :
    Q'.ofNat replication.replicaCount *
        centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K ≤
      slabParametricKPhysicalPartition w K (centralExtent 0) := by
  let offsets := List.range K
  let replicas := List.range replication.replicaCount
  let source := cartesian offsets replicas
  let target := centralHalfStates K 0
  let leftWeight := fun offset =>
    centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0
      (centralLowerSpinCubeState (offset + 1))
  let sourceWeight := fun pair : Nat × Nat => leftWeight pair.1
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
      exact replication.rawRow_le pair.1 pair.2
        (List.mem_range.mp hparts.1)
        (List.mem_range.mp hparts.2)
    · intro state _hstate
      exact centralPhysicalPositiveRawRowMass_nonnegative
        (Q'.le_of_lt hw0) K 0 state
  have hsource :
      listQSum sourceWeight source ≈
        centralLowerExcitedSpinCubeExactRawNumerator
            w (Q'.le_of_lt hw0) K *
          Q'.ofNat replication.replicaCount := by
    refine Q'.eqv_trans _
      (listQSum
        (fun pair : Nat × Nat => leftWeight pair.1 * (1 : Q'))
        source) _ ?_ ?_
    · apply listQSum_congr_on
      intro pair _hpair
      exact Q'.eqv_symm (Q'.mul_one_eqv (leftWeight pair.1))
    · refine Q'.eqv_trans _
        (listQSum leftWeight offsets *
          listQSum (fun _ : Nat => (1 : Q')) replicas) _
        (listQSum_cartesian_product
          leftWeight (fun _ : Nat => (1 : Q')) offsets replicas) ?_
      let exactNumerator :=
        centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K
      have hleft : listQSum leftWeight offsets ≈ exactNumerator := by
        unfold leftWeight offsets exactNumerator
        unfold centralLowerExcitedSpinCubeExactRawNumerator
        exact Q'.eqv_refl _
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
        (exactNumerator *
          listQSum (fun _ : Nat => (1 : Q')) replicas) _
        (Q'.mul_eqv_congr_right _ _ _ hleft)
        (Q'.mul_eqv_congr_left _ _ _ hright)
  have hsourceBound :
      centralLowerExcitedSpinCubeExactRawNumerator
            w (Q'.le_of_lt hw0) K *
          Q'.ofNat replication.replicaCount ≤
        centralPhysicalPositiveRawSourceMass
          w (Q'.le_of_lt hw0) K 0 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource) hinjected
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv
        (Q'.ofNat replication.replicaCount)
        (centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K)))
      hsourceBound)
    (Q'.le_of_eqv
      (centralPhysicalPositiveRawSourceMass_eqv_partition
        w (Q'.le_of_lt hw0) K 0))

/-- A finite replication certificate bounds the normalized ray mass by the
reciprocal of its positive replica count. -/
theorem rayMass_le_reciprocalReplicaCount
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubeExactRawReplication w hw0 K) :
    centralLowerExcitedSpinCubeRayMass
        w (Q'.le_of_lt hw0) K ≤
      Q'.divPos 1 (Q'.ofNat replication.replicaCount)
        (ofNat_pos_of_pos_local replication.replicaCount_pos) := by
  let numerator := centralLowerExcitedSpinCubeExactRawNumerator
    w (Q'.le_of_lt hw0) K
  let partition := slabParametricKPhysicalPartition w K (centralExtent 0)
  let count := Q'.ofNat replication.replicaCount
  let hcount : (0 : Q') < count :=
    ofNat_pos_of_pos_local replication.replicaCount_pos
  let epsilon := Q'.divPos 1 count hcount
  have hcountBound := replication.replicaCount_mul_exactRawNumerator_le_partition
  have hmul : numerator * count ≤ partition :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv numerator count))
      hcountBound
  have hdiv : numerator ≤ Q'.divPos partition count hcount :=
    Q'.le_divPos_of_mul_le partition count hcount hmul
  have hreassociate :
      Q'.divPos partition count hcount ≈ epsilon * partition := by
    unfold epsilon Q'.divPos
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv partition (Q'.recipPos count hcount))
      (Q'.eqv_symm
        (Q'.mul_eqv_congr_right
          (1 * Q'.recipPos count hcount)
          (Q'.recipPos count hcount) partition
          (Q'.one_mul_eqv (Q'.recipPos count hcount))))
  apply
    (centralLowerExcitedSpinCubeRayMass_le_iff_exactPartitionDomination
      hw0 K epsilon).mpr
  exact Q'.le_trans' _ _ _ hdiv (Q'.le_of_eqv hreassociate)

end CentralLowerExcitedSpinCubeExactRawReplication

/-! ## 3. Matched replication family -/

/-- A matched family of concrete finite replications whose reciprocal counts
have a located zero tail. -/
structure MatchedDyadicExcitedSpinCubeExactRawReplicationFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  replication : ∀ scale,
    CentralLowerExcitedSpinCubeExactRawReplication
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
  rate : Q' → Nat
  reciprocal_le : ∀ epsilon, (0 : Q') < epsilon →
    ∀ scale, rate epsilon ≤ scale →
      Q'.divPos 1
          (Q'.ofNat (replication scale).replicaCount)
          (ofNat_pos_of_pos_local
            (replication scale).replicaCount_pos) ≤
        epsilon

def MatchedDyadicExcitedSpinCubeExactRawReplicationFamily.toRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (replicas :
      MatchedDyadicExcitedSpinCubeExactRawReplicationFamily bridge) :
    MatchedDyadicExcitedSpinCubeRayMassTailZero bridge where
  rate := replicas.rate
  rayMass_le := by
    intro epsilon hepsilon scale hscale
    exact Q'.le_trans' _ _ _
      ((replicas.replication scale).rayMass_le_reciprocalReplicaCount)
      (replicas.reciprocal_le epsilon hepsilon scale hscale)

/-- Any matched raw-row replication family with divergent located count
excludes the cutoff-uniform assigned-ratio producer. -/
theorem replicationFamily_excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (replicas :
      MatchedDyadicExcitedSpinCubeExactRawReplicationFamily bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  tailZero_excludes_cofinalAssignedRatio replicas.toRayMassTailZero

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate.centralPhysicalPositiveRawSourceMass_eqv_partition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate.CentralLowerExcitedSpinCubeExactRawReplication.replicaCount_mul_exactRawNumerator_le_partition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate.CentralLowerExcitedSpinCubeExactRawReplication.rayMass_le_reciprocalReplicaCount
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate.MatchedDyadicExcitedSpinCubeExactRawReplicationFamily.toRayMassTailZero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate.replicationFamily_excludes_cofinalAssignedRatio
