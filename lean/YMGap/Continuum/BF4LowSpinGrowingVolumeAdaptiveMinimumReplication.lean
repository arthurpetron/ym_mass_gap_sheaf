/-
# Adaptive minimum-row replication for the growing low-spin carrier

At each finite volume the literal low-spin replica list is nonempty.  The
repository's constructive rational finite arg-min therefore selects an
actual low-spin index whose complete positive raw row is no larger than the
row of any other replica.  Using that selected state as the replication
reference makes every clipped replica/reference row ratio exactly one.

Consequently the computed effective multiplicity is exactly `volume + 1`,
and the adaptive reference stationary marginal is bounded by its reciprocal.
This is a constructive finite-volume entropy theorem.  The selected
reference may change with volume, so it does not yet identify a fixed
observable, the prescribed spin-cube ray, a conductance bottleneck, a
cofinal gap, a continuum limit, or the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
import YMGap.Continuum.BF4ObservableMatchedOneStep

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive minimum raw-row index -/

def lowSpinCentralRawRowScore
    (w : Q') (hw : (0 : Q') < w) (volume : Nat)
    (index : LowSpinCentralIndex volume) : Q' :=
  centralPhysicalPositiveRawRowMass
    w (Q'.le_of_lt hw) 1 (volume + 1)
    (lowSpinCentralLowerState volume index)

def lowSpinCentralRawRowArgmin
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    FiniteArgmin
      (lowSpinCentralRawRowScore w hw volume)
      (lowSpinCentralReferenceIndex volume ::
        lowSpinCentralIndices volume) :=
  finiteArgmin
    (lowSpinCentralRawRowScore w hw volume)
    (lowSpinCentralReferenceIndex volume)
    (lowSpinCentralIndices volume)

def lowSpinCentralAdaptiveReferenceIndex
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    LowSpinCentralIndex volume :=
  (lowSpinCentralRawRowArgmin w hw volume).choice

theorem lowSpinCentralAdaptiveReferenceIndex_mem
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    lowSpinCentralAdaptiveReferenceIndex w hw volume ∈
      lowSpinCentralIndices volume := by
  unfold lowSpinCentralAdaptiveReferenceIndex lowSpinCentralRawRowArgmin
  have hchoice := finiteArgmin_choice_mem
    (lowSpinCentralRawRowScore w hw volume)
    (lowSpinCentralReferenceIndex volume)
    (lowSpinCentralIndices volume)
  rcases List.mem_cons.mp hchoice with hreference | htail
  · rw [hreference]
    unfold lowSpinCentralIndices
    exact List.mem_attach _ (lowSpinCentralReferenceIndex volume)
  · exact htail

theorem lowSpinCentralAdaptiveReferenceIndex_minimal
    (w : Q') (hw : (0 : Q') < w) (volume : Nat)
    (index : LowSpinCentralIndex volume)
    (hindex : index ∈ lowSpinCentralIndices volume) :
    lowSpinCentralRawRowScore w hw volume
        (lowSpinCentralAdaptiveReferenceIndex w hw volume) ≤
      lowSpinCentralRawRowScore w hw volume index := by
  exact finiteArgmin_minimal
    (lowSpinCentralRawRowScore w hw volume)
    (lowSpinCentralReferenceIndex volume)
    (lowSpinCentralIndices volume) index
    (List.mem_cons_of_mem _ hindex)

def lowSpinCentralAdaptiveReferenceState
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) : EdgeLabelling :=
  lowSpinCentralLowerState volume
    (lowSpinCentralAdaptiveReferenceIndex w hw volume)

/-! ## 2. Factor-one adaptive replication -/

def lowSpinCentralAdaptivePositiveRawReplication
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    CentralPositiveRawReplicationListAt w hw 1 (volume + 1) where
  reference := lowSpinCentralAdaptiveReferenceState w hw volume
  reference_mem := by
    unfold lowSpinCentralAdaptiveReferenceState
    exact lowSpinCentralLowerState_mem_positive hw
      (lowSpinCentralAdaptiveReferenceIndex w hw volume)
  replicas := lowSpinCentralLowerStates volume
  replicas_nodup := lowSpinCentralLowerStates_nodup volume
  replicas_nonempty := by
    intro hempty
    have hlength := lowSpinCentralLowerStates_length volume
    rw [hempty] at hlength
    simp only [List.length_nil] at hlength
    omega
  replicas_mem := by
    intro state hstate
    unfold lowSpinCentralLowerStates at hstate
    obtain ⟨index, _hindex, rfl⟩ := List.mem_map.mp hstate
    exact lowSpinCentralLowerState_mem_positive hw index

theorem lowSpinCentralAdaptiveReferenceRawRow_le_replica
    (w : Q') (hw : (0 : Q') < w) (volume : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈ lowSpinCentralLowerStates volume) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralAdaptiveReferenceState w hw volume) ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1) state := by
  unfold lowSpinCentralLowerStates at hstate
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hstate
  change
    lowSpinCentralRawRowScore w hw volume
        (lowSpinCentralAdaptiveReferenceIndex w hw volume) ≤
      lowSpinCentralRawRowScore w hw volume index
  exact lowSpinCentralAdaptiveReferenceIndex_minimal
    w hw volume index hindex

theorem lowSpinCentralAdaptiveRawRowRatioFloor_eq_one
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    (lowSpinCentralAdaptivePositiveRawReplication
      w hw volume).rawRowRatioFloor = 1 := by
  apply
    (lowSpinCentralAdaptivePositiveRawReplication
      w hw volume).rawRowRatioFloor_eq_one_of_reference_le
  intro state hstate
  exact lowSpinCentralAdaptiveReferenceRawRow_le_replica
    w hw volume hstate

/-! ## 3. Exact linear effective multiplicity -/

def lowSpinCentralAdaptiveEffectiveMultiplicity
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) : Q' :=
  (lowSpinCentralAdaptivePositiveRawReplication
    w hw volume).effectiveMultiplicity

theorem lowSpinCentralAdaptiveEffectiveMultiplicity_eqv_count
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    lowSpinCentralAdaptiveEffectiveMultiplicity w hw volume ≈
      Q'.ofNat (volume + 1) := by
  unfold lowSpinCentralAdaptiveEffectiveMultiplicity
    effectiveMultiplicity
  rw [lowSpinCentralAdaptiveRawRowRatioFloor_eq_one w hw volume]
  change
    Q'.ofNat (lowSpinCentralLowerStates volume).length * 1 ≈
      Q'.ofNat (volume + 1)
  rw [lowSpinCentralLowerStates_length]
  exact Q'.mul_one_eqv _

theorem lowSpinCentralAdaptiveReferenceRawRow_mul_effective_le_partition
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralAdaptiveReferenceState w hw volume) *
        lowSpinCentralAdaptiveEffectiveMultiplicity w hw volume ≤
      slabParametricKPhysicalPartition
        w 1 (centralExtent (volume + 1)) := by
  exact
    (lowSpinCentralAdaptivePositiveRawReplication
      w hw volume).referenceRawRow_mul_effectiveMultiplicity_le_partition

theorem lowSpinCentralAdaptiveReferenceMarginal_le_reciprocalEffective
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralAdaptiveReferenceState w hw volume) ≤
      Q'.divPos 1
        (lowSpinCentralAdaptiveEffectiveMultiplicity w hw volume)
        ((lowSpinCentralAdaptivePositiveRawReplication
          w hw volume).effectiveMultiplicity_pos) := by
  exact
    (lowSpinCentralAdaptivePositiveRawReplication
      w hw volume).referenceMarginal_le_reciprocalEffectiveMultiplicity

end YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication.lowSpinCentralAdaptiveReferenceIndex_minimal
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication.lowSpinCentralAdaptiveReferenceRawRow_le_replica
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication.lowSpinCentralAdaptiveRawRowRatioFloor_eq_one
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication.lowSpinCentralAdaptiveEffectiveMultiplicity_eqv_count
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication.lowSpinCentralAdaptiveReferenceMarginal_le_reciprocalEffective
