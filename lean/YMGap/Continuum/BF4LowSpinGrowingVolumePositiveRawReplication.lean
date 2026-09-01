/-
# Low-spin growing-volume positive raw-row replication

This file instantiates the arbitrary-volume positive replication gate with
the literal `volume + 1` reflected low-spin states.  The slice-zero state is
the reference row and the complete duplicate-free low-spin list is the
replica carrier.  The compiler computes the exact finite minimum of the
clipped replica/reference positive raw-row ratios.

The resulting effective multiplicity is exactly

  `(volume + 1) * computedRatioFloor(volume)`

and the corrected-slab physical partition pays the reference raw row times
that factor.  Positivity is proved at every finite volume.  Divergence of the
computed factor remains the precise analytic obligation; no cofinal gap,
continuum limit, or Clay conclusion is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeAggregateRawMass
import YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate

namespace YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal reference and replica data -/

def lowSpinCentralReferenceIndex (volume : Nat) :
    LowSpinCentralIndex volume :=
  ⟨0, List.mem_range.mpr (by omega)⟩

def lowSpinCentralReferenceState (volume : Nat) : EdgeLabelling :=
  lowSpinCentralLowerState volume
    (lowSpinCentralReferenceIndex volume)

/-- The volume-parametric positive replication datum supplied by the literal
low-spin carrier. -/
def lowSpinCentralPositiveRawReplication
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    CentralPositiveRawReplicationListAt w hw 1 (volume + 1) where
  reference := lowSpinCentralReferenceState volume
  reference_mem := by
    unfold lowSpinCentralReferenceState
    exact lowSpinCentralLowerState_mem_positive hw
      (lowSpinCentralReferenceIndex volume)
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

theorem lowSpinCentralPositiveRawReplication_count
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    (lowSpinCentralPositiveRawReplication w hw volume).replicas.length =
      volume + 1 := by
  exact lowSpinCentralLowerStates_length volume

/-! ## 2. Computed ratio floor and effective multiplicity -/

def lowSpinCentralComputedRawRowRatioFloor
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) : Q' :=
  (lowSpinCentralPositiveRawReplication w hw volume).rawRowRatioFloor

theorem lowSpinCentralComputedRawRowRatioFloor_pos
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    (0 : Q') < lowSpinCentralComputedRawRowRatioFloor w hw volume := by
  exact (lowSpinCentralPositiveRawReplication w hw volume).rawRowRatioFloor_pos

def lowSpinCentralComputedEffectiveMultiplicity
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) : Q' :=
  (lowSpinCentralPositiveRawReplication w hw volume).effectiveMultiplicity

theorem lowSpinCentralComputedEffectiveMultiplicity_eqv
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    lowSpinCentralComputedEffectiveMultiplicity w hw volume ≈
      Q'.ofNat (volume + 1) *
        lowSpinCentralComputedRawRowRatioFloor w hw volume := by
  unfold lowSpinCentralComputedEffectiveMultiplicity
    lowSpinCentralComputedRawRowRatioFloor effectiveMultiplicity
  rw [lowSpinCentralPositiveRawReplication_count w hw volume]
  exact Q'.eqv_refl _

theorem lowSpinCentralComputedEffectiveMultiplicity_pos
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    (0 : Q') <
      lowSpinCentralComputedEffectiveMultiplicity w hw volume := by
  exact (lowSpinCentralPositiveRawReplication w hw volume).effectiveMultiplicity_pos

/-! ## 3. The exact volume-parametric partition gate -/

/-- The corrected-slab partition pays the literal reference raw row times the
computed low-spin effective multiplicity. -/
theorem lowSpinCentralReferenceRawRow_mul_effectiveMultiplicity_le_partition
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralReferenceState volume) *
        lowSpinCentralComputedEffectiveMultiplicity w hw volume ≤
      slabParametricKPhysicalPartition
        w 1 (centralExtent (volume + 1)) := by
  exact
    (lowSpinCentralPositiveRawReplication w hw volume).referenceRawRow_mul_effectiveMultiplicity_le_partition

/-- The normalized stationary marginal of the literal slice-zero reference
state is at most the reciprocal computed low-spin effective multiplicity. -/
theorem lowSpinCentralReferenceMarginal_le_reciprocalEffectiveMultiplicity
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralReferenceState volume) ≤
      Q'.divPos 1
        (lowSpinCentralComputedEffectiveMultiplicity w hw volume)
        (lowSpinCentralComputedEffectiveMultiplicity_pos w hw volume) := by
  exact
    (lowSpinCentralPositiveRawReplication w hw volume).referenceMarginal_le_reciprocalEffectiveMultiplicity

end YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication.lowSpinCentralComputedRawRowRatioFloor_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication.lowSpinCentralComputedEffectiveMultiplicity_eqv
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication.lowSpinCentralComputedEffectiveMultiplicity_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication.lowSpinCentralReferenceRawRow_mul_effectiveMultiplicity_le_partition
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication.lowSpinCentralReferenceMarginal_le_reciprocalEffectiveMultiplicity
