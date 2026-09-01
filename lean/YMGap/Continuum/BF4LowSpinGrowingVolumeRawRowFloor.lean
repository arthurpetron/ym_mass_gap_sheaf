/-
# A common raw-row floor for the low-spin growing-volume carrier

The reflected carrier adapter supplies `volume + 1` distinct cutoff-one lower
states.  Here the existing corrected-slab/ambient summand identity transports
the exact common-box cube weight to each of those slab states.  The vacuum
boundary channel then embeds that exact term into the complete reflected
kernel entry to the vacuum target, and hence into the complete positive-row
mass.

Thus every replica has the same strictly positive raw-row floor
`(coeffW w 1)^6`, independent of the volume and the replica index.  This is
the production-side floor required by a volume-parametric replication gate.
It is not yet a comparison with a common reference raw numerator, a
stationary-mass bound, a cofinal gap, a continuum limit, or the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
import YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor

set_option maxRecDepth 300000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry
open YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HKPos
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Lower-only assembly and the exact slab production term -/

private theorem assembleLowerOnly_eq
    {K half : Nat} {state : EdgeLabelling}
    (hstate : state ∈ boundedEdgeLabellings K
      (centralLowerFaceIds half)) :
    assembleReflectedSlabLabelling half state
        zeroEdgeLabelling zeroEdgeLabelling = state := by
  have hsound := boundedEdgeLabellings_sound K
    (centralLowerFaceIds half) state hstate
  funext id
  by_cases hphysical : id ∈
      slabPhysicalFaceEdges (centralExtent half)
  · cases hside : plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id)
    · exact assembleReflectedSlabLabelling_lower hphysical hside
    · rw [assembleReflectedSlabLabelling_fixed hphysical hside]
      change 0 = state id
      exact (hsound.2 id (by
        intro hlower
        have hlowerSide := (mem_centralLowerFaceIds.mp hlower).2
        rw [hside] at hlowerSide
        contradiction)).symm
    · rw [assembleReflectedSlabLabelling_upper hphysical hside]
      change 0 = state id
      exact (hsound.2 id (by
        intro hlower
        have hlowerSide := (mem_centralLowerFaceIds.mp hlower).2
        rw [hside] at hlowerSide
        contradiction)).symm
  · rw [assembleReflectedSlabLabelling_zero_off_physical
      half state zeroEdgeLabelling zeroEdgeLabelling hphysical]
    exact (hsound.2 id (by
      intro hlower
      exact hphysical (mem_centralLowerFaceIds.mp hlower).1)).symm

/-- The zero-extended slab production term is exactly the common six-face
cube weight. -/
theorem lowSpinCentralSlabPhysicalTerm_eqv
    (w : Q') {volume : Nat} (index : LowSpinCentralIndex volume) :
    slabParametricKPhysicalTerm w 1
        (centralExtent (volume + 1))
        (lowSpinCentralSlabPhysical volume index) ≈
      (coeffW w 1) ^ 6 := by
  have hambient := slabParametricKPhysicalTerm_ambient w
    (lowSpinCentralSlabPhysical_mem index)
  rw [lowSpinCentralSlabPhysical_roundtrip index] at hambient
  have hside :
      centralExtent (volume + 1) + 1 = 4 + 2 * volume := by
    unfold centralExtent
    omega
  rw [hside] at hambient
  exact Q'.eqv_trans _ _ _ hambient
    (Q'.eqv_trans _ _ _
      (parametricKPhysicalTerm_one_eqv_localized
        w (4 + 2 * volume)
        (timeSlicePhysical (2 * volume)
          (lowSpinCentralTimeSliceIndex index)))
      (timeSliceProduction_eqv_spinOneCubeWeight
        w (lowSpinCentralTimeSliceIndex index)))

theorem lowSpinCentralAssembledTerm_eqv
    (w : Q') {volume : Nat} (index : LowSpinCentralIndex volume) :
    slabParametricKPhysicalTerm w 1
        (centralExtent (volume + 1))
        (assembleReflectedSlabLabelling (volume + 1)
          (lowSpinCentralLowerState volume index)
          zeroEdgeLabelling zeroEdgeLabelling) ≈
      (coeffW w 1) ^ 6 := by
  rw [assembleLowerOnly_eq (lowSpinCentralLowerState_mem index),
    lowSpinCentralLowerState_eq_slabPhysical index]
  exact lowSpinCentralSlabPhysicalTerm_eqv w index

theorem lowSpinCentralAssembledTerm_pos
    {w : Q'} (hw : (0 : Q') < w)
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    (0 : Q') < slabParametricKPhysicalTerm w 1
      (centralExtent (volume + 1))
      (assembleReflectedSlabLabelling (volume + 1)
        (lowSpinCentralLowerState volume index)
        zeroEdgeLabelling zeroEdgeLabelling) := by
  have hcoefficient : (0 : Q') < coeffW w 1 := coeffW_pos hw 1
  have hpower : (0 : Q') < (coeffW w 1) ^ 6 :=
    pow_pos hcoefficient 6
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv (lowSpinCentralAssembledTerm_eqv w index))

/-! ## 2. The vacuum entry and the complete positive row share one floor -/

private theorem listQSum_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_local value hvalue tail)
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

private theorem zero_mem_bounded_local (K : Nat) (ids : List Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  apply boundedEdgeLabellings_complete
  · intro _id _hid
    change 0 < K + 1
    omega
  · intro _id _hid
    rfl

/-- The exact common six-face activity lies below the complete raw kernel
entry from every replica to the vacuum target. -/
theorem lowSpinCentralCommonFloor_le_vacuumKernel
    {w : Q'} (hw : (0 : Q') ≤ w)
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    (coeffW w 1) ^ 6 ≤
      centralPhysicalReflectedKernel w 1 (volume + 1)
        (lowSpinCentralLowerState volume index)
        zeroEdgeLabelling := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm w 1
      (centralExtent (volume + 1))
      (assembleReflectedSlabLabelling (volume + 1)
        (lowSpinCentralLowerState volume index)
        boundary zeroEdgeLabelling)
  have hmember :
      value zeroEdgeLabelling ≤
        listQSum value (centralBoundaryChannels 1 (volume + 1)) :=
    listQSum_member_le_local value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative hw 1
          (centralExtent (volume + 1))
          (assembleReflectedSlabLabelling (volume + 1)
            (lowSpinCentralLowerState volume index)
            boundary zeroEdgeLabelling))
      (centralBoundaryChannels 1 (volume + 1))
      (zero_mem_bounded_local 1
        (centralFixedFaceIds (volume + 1)))
  unfold centralPhysicalReflectedKernel
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (lowSpinCentralAssembledTerm_eqv w index))
    hmember

theorem lowSpinCentralVacuumKernel_pos
    {w : Q'} (hw : (0 : Q') < w)
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    (0 : Q') <
      centralPhysicalReflectedKernel w 1 (volume + 1)
        (lowSpinCentralLowerState volume index)
        zeroEdgeLabelling := by
  have hpower : (0 : Q') < (coeffW w 1) ^ 6 :=
    pow_pos (coeffW_pos hw 1) 6
  exact Q'.pos_of_lt_of_le hpower
    (lowSpinCentralCommonFloor_le_vacuumKernel
      (Q'.le_of_lt hw) index)

theorem lowSpinCentralLowerState_mem_positive
    {w : Q'} (hw : (0 : Q') < w)
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    lowSpinCentralLowerState volume index ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) 1 (volume + 1) := by
  apply mem_centralPositiveHalfStates_iff.mpr
  refine ⟨lowSpinCentralLowerState_mem index, ?_⟩
  unfold centralPhysicalRowMarginal
  have hmember := listQSum_member_le_local
    (centralNormalizedPhysicalReflectedKernel
      w (Q'.le_of_lt hw) 1 (volume + 1)
      (lowSpinCentralLowerState volume index))
    (fun target =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralLowerState volume index) target)
    (centralHalfStates 1 (volume + 1))
    (zeroEdgeLabelling_mem_centralHalfStates 1 (volume + 1))
  have hjoint : (0 : Q') <
      centralNormalizedPhysicalReflectedKernel
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralLowerState volume index)
        zeroEdgeLabelling := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.mul_pos
      (lowSpinCentralVacuumKernel_pos hw index)
      (Q'.recipPos_pos _ _)
  exact Q'.pos_of_lt_of_le hjoint hmember

/-- The complete unnormalised positive-carrier row of every selected replica
has the same volume-independent floor. -/
theorem lowSpinCentralCommonFloor_le_positiveRawRow
    {w : Q'} (hw : (0 : Q') < w)
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    (coeffW w 1) ^ 6 ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralLowerState volume index) := by
  unfold centralPhysicalPositiveRawRowMass
  have hmember := listQSum_member_le_local
    (centralPhysicalReflectedKernel w 1 (volume + 1)
      (lowSpinCentralLowerState volume index))
    (fun target =>
      centralPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralLowerState volume index) target)
    (centralPositiveHalfStates
      w (Q'.le_of_lt hw) 1 (volume + 1))
    (zeroEdgeLabelling_mem_centralPositiveHalfStates
      (Q'.le_of_lt hw) 1 (volume + 1))
  exact Q'.le_trans' _ _ _
    (lowSpinCentralCommonFloor_le_vacuumKernel
      (Q'.le_of_lt hw) index)
    hmember

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor.lowSpinCentralSlabPhysicalTerm_eqv
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor.lowSpinCentralAssembledTerm_eqv
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor.lowSpinCentralCommonFloor_le_vacuumKernel
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor.lowSpinCentralLowerState_mem_positive
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor.lowSpinCentralCommonFloor_le_positiveRawRow
