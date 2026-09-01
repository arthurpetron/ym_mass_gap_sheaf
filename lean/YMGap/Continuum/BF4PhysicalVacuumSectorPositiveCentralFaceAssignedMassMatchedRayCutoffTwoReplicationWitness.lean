/-
# A literal two-replica positive-row certificate at cutoff two

The positive-replication compiler is not merely inhabited by its identity
certificate.  At cutoff two the retained central carrier contains four
explicitly distinct states:

* the spin-one lower cube;
* the transverse single-face state;
* the spin-two lower cube; and
* the vacuum.

Assigning those four states to the two excited spin-cube sources and two
replica indices gives a literal injective positive-carrier encoding.  The
computed-floor compiler therefore produces a weighted certificate with
replica count two and a strictly positive finite row floor.

This is a fixed-cutoff nontriviality witness.  Its replica count does not grow
with cutoff and it supplies no asymptotic lower bound on the computed floor;
in particular it proves no cutoff-uniform, continuum, or Clay mass gap.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## 1. The four-state encoder -/

/-- Two replicas for each of the two excited spin-cube sources. -/
def cutoffTwoPositiveReplicaEncode (pair : Nat × Nat) : EdgeLabelling :=
  if pair.2 = 0 then
    centralLowerSpinCubeState (pair.1 + 1)
  else if pair.1 = 0 then
    cutoffTwoTransverseSingleFaceState
  else
    zeroEdgeLabelling

theorem cutoffTwoPositiveReplicaEncode_at_zero (pair : Nat × Nat) :
    cutoffTwoPositiveReplicaEncode pair 0 =
      if pair.2 = 0 then pair.1 + 1 else 0 := by
  by_cases hreplica : pair.2 = 0
  · simp [cutoffTwoPositiveReplicaEncode, hreplica,
      centralLowerSpinCubeState, centralLowerCubeFaceIds]
  · by_cases hoffset : pair.1 = 0
    · simp [cutoffTwoPositiveReplicaEncode, hreplica, hoffset,
        cutoffTwoTransverseSingleFaceState]
    · simp [cutoffTwoPositiveReplicaEncode, hreplica, hoffset,
        zeroEdgeLabelling]

theorem cutoffTwoPositiveReplicaEncode_at_thirtyNine
    (pair : Nat × Nat) :
    cutoffTwoPositiveReplicaEncode pair 39 =
      if pair.2 = 0 then pair.1 + 1
      else if pair.1 = 0 then 1 else 0 := by
  by_cases hreplica : pair.2 = 0
  · simp [cutoffTwoPositiveReplicaEncode, hreplica,
      centralLowerSpinCubeState, centralLowerCubeFaceIds]
  · by_cases hoffset : pair.1 = 0
    · simp [cutoffTwoPositiveReplicaEncode, hreplica, hoffset,
        cutoffTwoTransverseSingleFaceState]
    · simp [cutoffTwoPositiveReplicaEncode, hreplica, hoffset,
        zeroEdgeLabelling]

theorem cutoffTwoPositiveReplicaEncode_mem
    (offset replica : Nat) (hoffset : offset < 2)
    (hreplica : replica < 2) :
    cutoffTwoPositiveReplicaEncode (offset, replica) ∈
      centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 := by
  have hcasesOffset : offset = 0 ∨ offset = 1 := by omega
  have hcasesReplica : replica = 0 ∨ replica = 1 := by omega
  rcases hcasesOffset with rfl | rfl <;>
    rcases hcasesReplica with rfl | rfl
  · exact centralLowerSpinCubeState_mem_centralPositiveHalfStates
      (by decide : (0 : Q') < cutoffTwoHalfCoupling) (by omega)
  · exact cutoffTwoTransverseSingleFaceState_mem_carrier
  · exact centralLowerSpinCubeState_mem_centralPositiveHalfStates
      (by decide : (0 : Q') < cutoffTwoHalfCoupling) (by omega)
  · exact zeroEdgeLabelling_mem_centralPositiveHalfStates
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0

/-- Evaluation at faces zero and thirty-nine separates the four encoded
states. -/
theorem cutoffTwoPositiveReplicaEncode_injective_on
    (left right : Nat × Nat)
    (hleftOffset : left.1 < 2) (hleftReplica : left.2 < 2)
    (hrightOffset : right.1 < 2) (hrightReplica : right.2 < 2)
    (heq : cutoffTwoPositiveReplicaEncode left =
      cutoffTwoPositiveReplicaEncode right) :
    left = right := by
  rcases left with ⟨leftOffset, leftReplica⟩
  rcases right with ⟨rightOffset, rightReplica⟩
  change leftOffset < 2 at hleftOffset
  change leftReplica < 2 at hleftReplica
  change rightOffset < 2 at hrightOffset
  change rightReplica < 2 at hrightReplica
  have hfaceZero := congrFun heq 0
  have hfaceThirtyNine := congrFun heq 39
  rw [cutoffTwoPositiveReplicaEncode_at_zero,
    cutoffTwoPositiveReplicaEncode_at_zero] at hfaceZero
  rw [cutoffTwoPositiveReplicaEncode_at_thirtyNine,
    cutoffTwoPositiveReplicaEncode_at_thirtyNine] at hfaceThirtyNine
  have hleftOffsetCases : leftOffset = 0 ∨ leftOffset = 1 := by omega
  have hleftReplicaCases : leftReplica = 0 ∨ leftReplica = 1 := by omega
  have hrightOffsetCases : rightOffset = 0 ∨ rightOffset = 1 := by omega
  have hrightReplicaCases : rightReplica = 0 ∨ rightReplica = 1 := by omega
  rcases hleftOffsetCases with rfl | rfl <;>
    rcases hleftReplicaCases with rfl | rfl <;>
    rcases hrightOffsetCases with rfl | rfl <;>
    rcases hrightReplicaCases with rfl | rfl <;>
    simp at hfaceZero hfaceThirtyNine ⊢

/-! ## 2. Compilation through the computed finite floor -/

/-- The genuine cutoff-two geometric input to the positive-row compiler. -/
def cutoffTwoPositiveRawReplication :
    CentralLowerExcitedSpinCubePositiveRawReplication
      cutoffTwoHalfCoupling
      (by decide : (0 : Q') < cutoffTwoHalfCoupling) 2 where
  replicaCount := 2
  replicaCount_pos := by omega
  encode := cutoffTwoPositiveReplicaEncode
  encode_mem := cutoffTwoPositiveReplicaEncode_mem
  encode_injective := cutoffTwoPositiveReplicaEncode_injective_on

theorem cutoffTwoPositiveRawReplication_count :
    cutoffTwoPositiveRawReplication.replicaCount = 2 := rfl

theorem cutoffTwoPositiveRawReplication_floor_pos :
    (0 : Q') < cutoffTwoPositiveRawReplication.rawRowRatioFloor :=
  cutoffTwoPositiveRawReplication.rawRowRatioFloor_pos

/-- The computed-floor compiler yields a quantitative weighted certificate
with two replicas at this fixed cutoff. -/
def cutoffTwoWeightedRawReplication :=
  cutoffTwoPositiveRawReplication.toWeighted

theorem cutoffTwoWeightedRawReplication_count :
    cutoffTwoWeightedRawReplication.replicaCount = 2 := rfl

/-- The four-state injection makes the literal cutoff-two physical partition
pay the exact excited-ray numerator times its computed effective
multiplicity. -/
theorem cutoffTwoExactRawNumerator_mul_effectiveMultiplicity_le_partition :
    centralLowerExcitedSpinCubeExactRawNumerator cutoffTwoHalfCoupling
          (Q'.le_of_lt
            (by decide : (0 : Q') < cutoffTwoHalfCoupling)) 2 *
        cutoffTwoWeightedRawReplication.effectiveMultiplicity ≤
      slabParametricKPhysicalPartition cutoffTwoHalfCoupling 2
        (centralExtent 0) := by
  exact cutoffTwoWeightedRawReplication.exactRawNumerator_mul_effectiveMultiplicity_le_partition

/-- Direct finite ray estimate obtained from the computed positive floor and
the two literal replicas. -/
theorem cutoffTwoRayMass_le_reciprocalComputedEffectiveMultiplicity :
    centralLowerExcitedSpinCubeRayMass cutoffTwoHalfCoupling
          (Q'.le_of_lt
            (by decide : (0 : Q') < cutoffTwoHalfCoupling)) 2 ≤
      Q'.divPos 1 cutoffTwoWeightedRawReplication.effectiveMultiplicity
        cutoffTwoWeightedRawReplication.effectiveMultiplicity_pos := by
  exact cutoffTwoPositiveRawReplication.rayMass_le_reciprocalComputedEffectiveMultiplicity

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness.cutoffTwoPositiveReplicaEncode_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness.cutoffTwoPositiveReplicaEncode_injective_on
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness.cutoffTwoPositiveRawReplication_floor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness.cutoffTwoWeightedRawReplication_count
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness.cutoffTwoExactRawNumerator_mul_effectiveMultiplicity_le_partition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayCutoffTwoReplicationWitness.cutoffTwoRayMass_le_reciprocalComputedEffectiveMultiplicity
