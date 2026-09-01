/-
# A growing positive-row replication certificate at every cutoff

The disjoint closed-surface grid supplies an independent second row
coordinate.  For an excited source offset `offset < K`, put spin
`offset + 1` on the first surface and let the second surface carry any
`replica < K + 1`.  Both spins are admitted by cutoff `K`, every encoded row
is in the literal positive carrier, and faces zero and nine make the entire
Cartesian encoding injective.

Thus the geometric replica count is exactly `K + 1`, rather than the previous
fixed count two.  The computed finite row-floor compiler gives the associated
positive effective multiplicity and exact partition budget.  Because that
floor itself depends on `K`, growth of the replica count alone does not prove
that effective multiplicity diverges.  No ray-tail, cutoff-uniform spectral
gap, continuum theory, or Clay mass-gap conclusion is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## 1. The cutoff-growing Cartesian encoding -/

/-- The source offset is recorded by the first surface spin, and the replica
coordinate by the second surface spin. -/
def growingGridPositiveReplicaEncode (pair : Nat × Nat) : EdgeLabelling :=
  centralGridRowState (pair.1 + 1) pair.2

theorem growingGridPositiveReplicaEncode_mem
    {w : Q'} (hw : (0 : Q') < w)
    {K offset replica : Nat}
    (hoffset : offset < K) (hreplica : replica < K + 1) :
    growingGridPositiveReplicaEncode (offset, replica) ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 := by
  apply centralGridRowState_mem_centralPositiveHalfStates hw
  · omega
  · omega

theorem growingGridPositiveReplicaEncode_injective :
    Function.Injective growingGridPositiveReplicaEncode := by
  intro left right heq
  rcases left with ⟨leftOffset, leftReplica⟩
  rcases right with ⟨rightOffset, rightReplica⟩
  have hpairs :
      (leftOffset + 1, leftReplica) =
        (rightOffset + 1, rightReplica) :=
    centralGridRowState_injective heq
  have hfirst : leftOffset + 1 = rightOffset + 1 :=
    congrArg Prod.fst hpairs
  have hsecond : leftReplica = rightReplica :=
    congrArg Prod.snd hpairs
  exact Prod.ext (Nat.add_right_cancel hfirst) hsecond

/-! ## 2. Compilation through the exact finite partition gate -/

/-- At every cutoff, the two-surface grid gives exactly `K + 1` distinct
positive rows for each excited spin-cube source. -/
def growingGridPositiveRawReplication
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    CentralLowerExcitedSpinCubePositiveRawReplication w hw K where
  replicaCount := K + 1
  replicaCount_pos := by omega
  encode := growingGridPositiveReplicaEncode
  encode_mem := by
    intro offset replica hoffset hreplica
    exact growingGridPositiveReplicaEncode_mem hw hoffset hreplica
  encode_injective := by
    intro left right _hleftOffset _hleftReplica
      _hrightOffset _hrightReplica heq
    exact growingGridPositiveReplicaEncode_injective heq

theorem growingGridPositiveRawReplication_count
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    (growingGridPositiveRawReplication w hw K).replicaCount = K + 1 := rfl

/-- The geometric replica count is strictly larger than the cutoff and hence
is unbounded along the cutoff sequence. -/
theorem growingGridPositiveRawReplication_count_gt_cutoff
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    K < (growingGridPositiveRawReplication w hw K).replicaCount := by
  change K < K + 1
  omega

theorem growingGridPositiveRawReplication_floor_pos
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') <
      (growingGridPositiveRawReplication w hw K).rawRowRatioFloor :=
  (growingGridPositiveRawReplication w hw K).rawRowRatioFloor_pos

/-- The exact form records why the remaining asymptotic problem is analytic:
the growing factor `K + 1` is multiplied by a cutoff-dependent positive row
floor. -/
theorem growingGridComputedEffectiveMultiplicity_eq
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    (growingGridPositiveRawReplication w hw K).toWeighted.effectiveMultiplicity =
      Q'.ofNat (K + 1) *
        (growingGridPositiveRawReplication w hw K).rawRowRatioFloor := rfl

theorem growingGridExactRawNumerator_mul_effectiveMultiplicity_le_partition
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeExactRawNumerator w (Q'.le_of_lt hw) K *
        (growingGridPositiveRawReplication w hw K).toWeighted.effectiveMultiplicity ≤
      slabParametricKPhysicalPartition w K (centralExtent 0) := by
  let replication :=
    (growingGridPositiveRawReplication w hw K).toWeighted
  exact replication.exactRawNumerator_mul_effectiveMultiplicity_le_partition

theorem growingGridRayMass_le_reciprocalComputedEffectiveMultiplicity
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw) K ≤
      Q'.divPos 1
        (growingGridPositiveRawReplication w hw K).toWeighted.effectiveMultiplicity
        (growingGridPositiveRawReplication w hw K).toWeighted.effectiveMultiplicity_pos := by
  let replication := growingGridPositiveRawReplication w hw K
  exact replication.rayMass_le_reciprocalComputedEffectiveMultiplicity

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness.growingGridPositiveReplicaEncode_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness.growingGridPositiveReplicaEncode_injective
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness.growingGridPositiveRawReplication_count_gt_cutoff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness.growingGridPositiveRawReplication_floor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness.growingGridExactRawNumerator_mul_effectiveMultiplicity_le_partition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness.growingGridRayMass_le_reciprocalComputedEffectiveMultiplicity
