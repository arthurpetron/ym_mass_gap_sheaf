/-
# A literal two-ray positive-row certificate at every cutoff

The lower spatial spin cube and the transverse reflected spin cube give two
distinct retained positive-row states for every nonzero spin admitted by the
production cutoff.  Pairing each excited lower-cube source with these two
states produces an injective two-replica encoding at every finite cutoff.
The computed-floor compiler therefore yields a positive effective
multiplicity and a finite reciprocal ray-mass estimate uniformly in the
sense that the same construction exists for every cutoff.

The replica count is the fixed value two.  It does not grow with cutoff, so
this theorem does not prove a vanishing ray tail, a cutoff-uniform spectral
gap, a continuum theory, or the Clay mass-gap statement.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayAllCutoffTwoRayReplicationWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## 1. Two geometric replicas for every admitted spin -/

/-- Replica zero is the lower spatial cube and replica one is the transverse
reflected cube.  The spin is the excited-source offset plus one. -/
def allCutoffTwoRayPositiveReplicaEncode (pair : Nat × Nat) : EdgeLabelling :=
  if pair.2 = 0 then
    centralLowerSpinCubeState (pair.1 + 1)
  else
    centralTransverseSpinSingleFaceState (pair.1 + 1)

theorem allCutoffTwoRayPositiveReplicaEncode_at_zero (pair : Nat × Nat) :
    allCutoffTwoRayPositiveReplicaEncode pair 0 =
      if pair.2 = 0 then pair.1 + 1 else 0 := by
  by_cases hreplica : pair.2 = 0
  · simp [allCutoffTwoRayPositiveReplicaEncode, hreplica,
      centralLowerSpinCubeState, centralLowerCubeFaceIds]
  · simp [allCutoffTwoRayPositiveReplicaEncode, hreplica,
      centralTransverseSpinSingleFaceState]

theorem allCutoffTwoRayPositiveReplicaEncode_at_thirtyNine
    (pair : Nat × Nat) :
    allCutoffTwoRayPositiveReplicaEncode pair 39 = pair.1 + 1 := by
  by_cases hreplica : pair.2 = 0
  · simp [allCutoffTwoRayPositiveReplicaEncode, hreplica,
      centralLowerSpinCubeState, centralLowerCubeFaceIds]
  · simp [allCutoffTwoRayPositiveReplicaEncode, hreplica,
      centralTransverseSpinSingleFaceState]

theorem allCutoffTwoRayPositiveReplicaEncode_mem
    {w : Q'} (hw : (0 : Q') < w)
    {K offset replica : Nat}
    (hoffset : offset < K) (hreplica : replica < 2) :
    allCutoffTwoRayPositiveReplicaEncode (offset, replica) ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 := by
  have hreplicaCases : replica = 0 ∨ replica = 1 := by omega
  rcases hreplicaCases with rfl | rfl
  · exact centralLowerSpinCubeState_mem_centralPositiveHalfStates
      hw (by omega)
  · exact centralTransverseSpinSingleFaceState_mem_centralPositiveHalfStates
      hw (by omega)

private theorem predecessor_eq_zero_of_succ_lt_two
    {predecessor : Nat} (h : predecessor + 1 < 2) :
    predecessor = 0 := by
  have hsucc : Nat.succ predecessor < Nat.succ 1 := by
    simpa using h
  have hltOne : predecessor < 1 := Nat.lt_of_succ_lt_succ hsucc
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hltOne)

/-- Faces thirty-nine and zero respectively recover the spin offset and
separate the two geometric rays. -/
theorem allCutoffTwoRayPositiveReplicaEncode_injective_on
    (left right : Nat × Nat)
    (hleftReplica : left.2 < 2) (hrightReplica : right.2 < 2)
    (heq : allCutoffTwoRayPositiveReplicaEncode left =
      allCutoffTwoRayPositiveReplicaEncode right) :
    left = right := by
  rcases left with ⟨leftOffset, leftReplica⟩
  rcases right with ⟨rightOffset, rightReplica⟩
  change leftReplica < 2 at hleftReplica
  change rightReplica < 2 at hrightReplica
  have hfaceZero := congrFun heq 0
  have hfaceThirtyNine := congrFun heq 39
  rw [allCutoffTwoRayPositiveReplicaEncode_at_zero,
    allCutoffTwoRayPositiveReplicaEncode_at_zero] at hfaceZero
  rw [allCutoffTwoRayPositiveReplicaEncode_at_thirtyNine,
    allCutoffTwoRayPositiveReplicaEncode_at_thirtyNine] at hfaceThirtyNine
  have hoffset : leftOffset = rightOffset :=
    Nat.add_right_cancel hfaceThirtyNine
  have hreplica : leftReplica = rightReplica := by
    cases leftReplica with
    | zero =>
        cases rightReplica with
        | zero => rfl
        | succ rightPredecessor =>
            have hrightPredecessor : rightPredecessor = 0 :=
              predecessor_eq_zero_of_succ_lt_two hrightReplica
            subst rightPredecessor
            change leftOffset + 1 = 0 at hfaceZero
            have hpositive : 0 < leftOffset + 1 :=
              Nat.zero_lt_succ leftOffset
            exact False.elim ((Nat.ne_of_gt hpositive) hfaceZero)
    | succ leftPredecessor =>
        have hleftPredecessor : leftPredecessor = 0 :=
          predecessor_eq_zero_of_succ_lt_two hleftReplica
        subst leftPredecessor
        cases rightReplica with
        | zero =>
            change 0 = rightOffset + 1 at hfaceZero
            have hpositive : 0 < rightOffset + 1 :=
              Nat.zero_lt_succ rightOffset
            exact False.elim ((Nat.ne_of_gt hpositive) hfaceZero.symm)
        | succ rightPredecessor =>
            have hrightPredecessor : rightPredecessor = 0 :=
              predecessor_eq_zero_of_succ_lt_two hrightReplica
            subst rightPredecessor
            rfl
  exact Prod.ext hoffset hreplica

/-! ## 2. All-cutoff compilation through the computed finite floor -/

/-- A genuine two-replica positive-row certificate for every positive
coupling and every finite cutoff.  At cutoff zero the source domain is empty,
but the geometric replica count remains two. -/
def allCutoffTwoRayPositiveRawReplication
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    CentralLowerExcitedSpinCubePositiveRawReplication w hw K where
  replicaCount := 2
  replicaCount_pos := by omega
  encode := allCutoffTwoRayPositiveReplicaEncode
  encode_mem := by
    intro offset replica hoffset hreplica
    exact allCutoffTwoRayPositiveReplicaEncode_mem hw hoffset hreplica
  encode_injective := by
    intro left right _hleftOffset hleftReplica
      _hrightOffset hrightReplica heq
    exact allCutoffTwoRayPositiveReplicaEncode_injective_on
      left right hleftReplica hrightReplica heq

theorem allCutoffTwoRayPositiveRawReplication_count
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    (allCutoffTwoRayPositiveRawReplication w hw K).replicaCount = 2 := rfl

theorem allCutoffTwoRayPositiveRawReplication_floor_pos
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') <
      (allCutoffTwoRayPositiveRawReplication w hw K).rawRowRatioFloor :=
  (allCutoffTwoRayPositiveRawReplication w hw K).rawRowRatioFloor_pos

/-- The computed-floor compiler gives an exact finite partition budget with
the effective multiplicity generated by the two-ray injection. -/
theorem allCutoffTwoRayExactRawNumerator_mul_effectiveMultiplicity_le_partition
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeExactRawNumerator w (Q'.le_of_lt hw) K *
        (allCutoffTwoRayPositiveRawReplication w hw K).toWeighted.effectiveMultiplicity ≤
      slabParametricKPhysicalPartition w K (centralExtent 0) := by
  let replication :=
    (allCutoffTwoRayPositiveRawReplication w hw K).toWeighted
  exact replication.exactRawNumerator_mul_effectiveMultiplicity_le_partition

/-- The resulting direct finite ray estimate.  Its denominator is positive
at every cutoff, but no cutoff-independent lower bound is asserted. -/
theorem allCutoffTwoRayRayMass_le_reciprocalComputedEffectiveMultiplicity
    (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw) K ≤
      Q'.divPos 1
        (allCutoffTwoRayPositiveRawReplication w hw K).toWeighted.effectiveMultiplicity
        (allCutoffTwoRayPositiveRawReplication w hw K).toWeighted.effectiveMultiplicity_pos := by
  let replication := allCutoffTwoRayPositiveRawReplication w hw K
  exact replication.rayMass_le_reciprocalComputedEffectiveMultiplicity

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayAllCutoffTwoRayReplicationWitness

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayAllCutoffTwoRayReplicationWitness.allCutoffTwoRayPositiveReplicaEncode_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayAllCutoffTwoRayReplicationWitness.allCutoffTwoRayPositiveReplicaEncode_injective_on
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayAllCutoffTwoRayReplicationWitness.allCutoffTwoRayPositiveRawReplication_floor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayAllCutoffTwoRayReplicationWitness.allCutoffTwoRayExactRawNumerator_mul_effectiveMultiplicity_le_partition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayAllCutoffTwoRayReplicationWitness.allCutoffTwoRayRayMass_le_reciprocalComputedEffectiveMultiplicity
