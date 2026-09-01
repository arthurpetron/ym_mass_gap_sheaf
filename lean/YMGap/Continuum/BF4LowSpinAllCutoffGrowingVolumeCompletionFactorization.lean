/-
# All-cutoff low-spin growing-volume row equality

The cutoff-one completion factorization uses only a spin-one source cube and
geometric separation from the fixed/upper completion.  This module lifts that
argument to every representation cutoff `K >= 1`.  Arbitrary-cutoff time-shift
and nested-box invariance identify the source factors, while exact all-spin
component factorization leaves the unchanged completion factor common.

The result is uniform in the finite cutoff and in the positive coupling, but
it still grows the reflection half-volume.  It is not the fixed-half matched
cutoff ray, an all-vector spectral gap, a continuum limit, or the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization
import YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
import YMGap.Continuum.Z4TimeShiftedPhysicalWeights

namespace YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization

set_option maxRecDepth 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor
open YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4DyadicSlabCubeTranslatedProjectedComposition
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4UnitCubeAllVolumePhysicality

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Arbitrary-cutoff source invariance -/

private theorem boundedEdgeLabellings_mono_local
    {base later : Nat} (hcutoff : base ≤ later)
    {ids : List Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings base ids) :
    physical ∈ boundedEdgeLabellings later ids := by
  have hsound := boundedEdgeLabellings_sound base ids physical hphysical
  apply boundedEdgeLabellings_complete
  · intro id hid
    have hlt := hsound.1 id hid
    omega
  · intro id hid
    exact hsound.2 id hid

private theorem oddFineCubePhysical_mem_bounded_K
    {K : Nat} (hK : 1 ≤ K) :
    oddFineCubePhysical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount 4)) := by
  have hone : oddFineCubePhysical ∈ boundedEdgeLabellings 1
      (List.range (plaquetteEdgeCount 4)) := by
    simpa [explicitPhysicalLabellings, physicalFaceEdges] using
      oddFineCubePhysical_mem
  exact boundedEdgeLabellings_mono_local hK hone

private theorem timeSliceShiftedPhysical_mem_bounded_K
    {K horizon : Nat} (hK : 1 ≤ K)
    (index : TimeSliceIndex horizon) :
    timeShiftTransportPhysical index.val 4 oddFineCubePhysical ∈
      boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount (4 + index.val))) :=
  boundedEdgeLabellings_mono_local hK
    (timeSliceShiftedPhysical_mem_bounded index)

/-- At arbitrary cutoff, every selected time-slice source has the same exact
physical spin-foam weight as the base spin-one cube. -/
theorem timeSliceParametricKPhysicalTerm_eqv_base
    (w : Q') {K horizon : Nat} (hK : 1 ≤ K)
    (index : TimeSliceIndex horizon) :
    parametricKPhysicalTerm w K (4 + horizon)
        (timeSlicePhysical horizon index) ≈
      parametricKPhysicalTerm w K 4 oddFineCubePhysical := by
  have hshift := parametricKPhysicalTerm_timeShift w
    (K := K) (shift := index.val)
    (oddFineCubePhysical_mem_bounded_K hK)
  have hcross := parametricKPhysicalTerm_cross_volume w
    (K := K) (small := 4 + index.val) (large := 4 + horizon) (by
      have hle := timeSliceIndex_le index
      omega)
    (timeSliceShiftedPhysical_mem_bounded_K hK index)
  change parametricKPhysicalTerm w K (4 + index.val)
      (timeShiftTransportPhysical index.val 4 oddFineCubePhysical) ≈
    parametricKPhysicalTerm w K (4 + horizon)
      (timeSliceTransportedPhysical horizon index) at hcross
  rw [timeSliceTransportedPhysical_eq_componentLabel index] at hcross
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hshift hcross)

theorem timeSliceParametricKPhysicalTerm_eqv_between
    (w : Q') {K horizon : Nat} (hK : 1 ≤ K)
    (left right : TimeSliceIndex horizon) :
    parametricKPhysicalTerm w K (4 + horizon)
        (timeSlicePhysical horizon left) ≈
      parametricKPhysicalTerm w K (4 + horizon)
        (timeSlicePhysical horizon right) := by
  exact Q'.eqv_trans _ _ _
    (timeSliceParametricKPhysicalTerm_eqv_base w hK left)
    (Q'.eqv_symm
      (timeSliceParametricKPhysicalTerm_eqv_base w hK right))

private theorem lowSpinCentralLowerState_mem_K
    {K volume : Nat} (hK : 1 ≤ K)
    (index : LowSpinCentralIndex volume) :
    lowSpinCentralLowerState volume index ∈
      centralHalfStates K (volume + 1) :=
  boundedEdgeLabellings_mono_local hK
    (lowSpinCentralLowerState_mem index)

private theorem lowSpinCentralSourceAmbient_mem_bounded_K
    {K volume : Nat} (hK : 1 ≤ K)
    (index : LowSpinCentralIndex volume) :
    timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index) ∈
      boundedEdgeLabellings K
        (List.range
          (plaquetteEdgeCount (centralAmbient (volume + 1)))) := by
  have hone := timeSlicePhysical_mem
    (lowSpinCentralTimeSliceIndex index)
  have hone' : timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index) ∈
      boundedEdgeLabellings 1
        (List.range
          (plaquetteEdgeCount (centralAmbient (volume + 1)))) := by
    simpa [explicitPhysicalLabellings, physicalFaceEdges,
      lowSpinCentralAmbient_eq volume] using hone
  exact boundedEdgeLabellings_mono_local hK hone'

private theorem zeroEdgeLabelling_mem_bounded_local
    (cutoff : Nat) (ids : List Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings cutoff ids := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < cutoff + 1
    omega
  · intro _ _
    rfl

private theorem lowSpinCentralCompletionRemainderAmbient_mem_bounded_K
    {K volume : Nat} {boundary target : EdgeLabelling}
    (hboundary : boundary ∈
      centralBoundaryChannels K (volume + 1))
    (htarget : target ∈ centralHalfStates K (volume + 1)) :
    lowSpinCentralCompletionRemainderAmbient volume boundary target ∈
      boundedEdgeLabellings K
        (List.range
          (plaquetteEdgeCount (centralAmbient (volume + 1)))) := by
  have hslab := assembleReflectedSlabLabelling_mem_full
    (zeroEdgeLabelling_mem_bounded_local K
      (centralLowerFaceIds (volume + 1)))
    hboundary htarget
  unfold lowSpinCentralCompletionRemainderAmbient
  exact slabToAmbientPhysical_mem_bounded hslab

/-! ## 2. Arbitrary-cutoff complete-row equality -/

theorem lowSpinCentralKAssembledTerm_eqv_source_mul_remainder
    (w : Q') {K volume : Nat} (hK : 1 ≤ K)
    (index : LowSpinCentralIndex volume)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈
      centralBoundaryChannels K (volume + 1))
    (htarget : target ∈ centralHalfStates K (volume + 1)) :
    slabParametricKPhysicalTerm w K (centralExtent (volume + 1))
        (assembleReflectedSlabLabelling (volume + 1)
          (lowSpinCentralLowerState volume index) boundary target) ≈
      parametricKPhysicalTerm w K (centralAmbient (volume + 1))
          (timeSlicePhysical (2 * volume)
            (lowSpinCentralTimeSliceIndex index)) *
        parametricKPhysicalTerm w K (centralAmbient (volume + 1))
          (lowSpinCentralCompletionRemainderAmbient
            volume boundary target) := by
  have hfullBounded := assembleReflectedSlabLabelling_mem_full
    (lowSpinCentralLowerState_mem_K hK index) hboundary htarget
  have hambient := slabParametricKPhysicalTerm_ambient w hfullBounded
  rw [lowSpinCentralAssembledAmbient_eq_binaryUnion
    index boundary target] at hambient
  have hfactor := parametricKPhysicalTerm_union_factor (w := w)
    (lowSpinCentralSourceAmbient_mem_bounded_K hK index)
    (lowSpinCentralCompletionRemainderAmbient_mem_bounded_K
      hboundary htarget)
    (lowSpinCentralSource_completionRemainder_faceDisjoint
      index boundary target)
    (lowSpinCentralSource_completionRemainder_linkSeparated
      index boundary target)
  exact Q'.eqv_trans _ _ _ hambient hfactor

theorem lowSpinCentralKAssembledTerm_eqv_between
    (w : Q') {K volume : Nat} (hK : 1 ≤ K)
    (left right : LowSpinCentralIndex volume)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈
      centralBoundaryChannels K (volume + 1))
    (htarget : target ∈ centralHalfStates K (volume + 1)) :
    slabParametricKPhysicalTerm w K (centralExtent (volume + 1))
        (assembleReflectedSlabLabelling (volume + 1)
          (lowSpinCentralLowerState volume left) boundary target) ≈
      slabParametricKPhysicalTerm w K (centralExtent (volume + 1))
        (assembleReflectedSlabLabelling (volume + 1)
          (lowSpinCentralLowerState volume right) boundary target) := by
  have hleft := lowSpinCentralKAssembledTerm_eqv_source_mul_remainder
    w hK left boundary target hboundary htarget
  have hright := lowSpinCentralKAssembledTerm_eqv_source_mul_remainder
    w hK right boundary target hboundary htarget
  have hsource := timeSliceParametricKPhysicalTerm_eqv_between
    w hK (lowSpinCentralTimeSliceIndex left)
      (lowSpinCentralTimeSliceIndex right)
  rw [lowSpinCentralAmbient_eq volume] at hsource
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hsource)
      (Q'.eqv_symm hright))

theorem lowSpinCentralKReflectedKernel_eqv_between
    (w : Q') {K volume : Nat} (hK : 1 ≤ K)
    (left right : LowSpinCentralIndex volume)
    (target : EdgeLabelling)
    (htarget : target ∈ centralHalfStates K (volume + 1)) :
    centralPhysicalReflectedKernel w K (volume + 1)
        (lowSpinCentralLowerState volume left) target ≈
      centralPhysicalReflectedKernel w K (volume + 1)
        (lowSpinCentralLowerState volume right) target := by
  unfold centralPhysicalReflectedKernel
  apply listQSum_congr_on
  intro boundary hboundary
  exact lowSpinCentralKAssembledTerm_eqv_between
    w hK left right boundary target hboundary htarget

/-- At every finite representation cutoff at least one, all selected
low-spin growing-volume positive raw rows are exactly equal. -/
theorem lowSpinCentralKPositiveRawRows_eqv
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K volume : Nat} (hK : 1 ≤ K)
    (left right : LowSpinCentralIndex volume) :
    centralPhysicalPositiveRawRowMass w hw K (volume + 1)
        (lowSpinCentralLowerState volume left) ≈
      centralPhysicalPositiveRawRowMass w hw K (volume + 1)
        (lowSpinCentralLowerState volume right) := by
  unfold centralPhysicalPositiveRawRowMass
  apply listQSum_congr_on
  intro target htarget
  exact lowSpinCentralKReflectedKernel_eqv_between
    w hK left right target
      ((mem_centralPositiveHalfStates_iff.mp htarget).1)

/-! ## 3. All-cutoff replication and the fixed-source volume tail -/

/-- The same literal `volume + 1` low-spin sources form a positive-row
replication datum at every representation cutoff `K >= 1`. -/
def lowSpinCentralKPositiveRawReplication
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) :
    CentralPositiveRawReplicationListAt w hw K (volume + 1) where
  reference := lowSpinCentralReferenceState volume
  reference_mem := by
    unfold lowSpinCentralReferenceState
    exact mem_centralPositiveHalfStates_of_le
      (Q'.le_of_lt hw) hK
      (lowSpinCentralLowerState_mem_positive hw
        (lowSpinCentralReferenceIndex volume))
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
    exact mem_centralPositiveHalfStates_of_le
      (Q'.le_of_lt hw) hK
      (lowSpinCentralLowerState_mem_positive hw index)

theorem lowSpinCentralKPositiveRawReplication_count
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) :
    (lowSpinCentralKPositiveRawReplication
      w hw K hK volume).replicas.length = volume + 1 :=
  lowSpinCentralLowerStates_length volume

def lowSpinCentralKComputedRawRowRatioFloor
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) : Q' :=
  (lowSpinCentralKPositiveRawReplication
    w hw K hK volume).rawRowRatioFloor

/-- At every finite cutoff, each exact replica/reference row ratio clips to
one and the computed floor is exactly one. -/
theorem lowSpinCentralKComputedRawRowRatioFloor_eq_one
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) :
    lowSpinCentralKComputedRawRowRatioFloor
      w hw K hK volume = 1 := by
  unfold lowSpinCentralKComputedRawRowRatioFloor
  apply rawRowRatioFloor_eq_one_of_reference_le
    (lowSpinCentralKPositiveRawReplication w hw K hK volume)
  intro state hstate
  change state ∈ lowSpinCentralLowerStates volume at hstate
  obtain ⟨index, _hindex, rfl⟩ := List.mem_map.mp hstate
  exact Q'.le_of_eqv
    (lowSpinCentralKPositiveRawRows_eqv
      (Q'.le_of_lt hw) hK
      (lowSpinCentralReferenceIndex volume) index)

def lowSpinCentralKComputedEffectiveMultiplicity
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) : Q' :=
  (lowSpinCentralKPositiveRawReplication
    w hw K hK volume).effectiveMultiplicity

/-- The exact effective multiplicity is uniformly the literal spatial count,
independently of cutoff and coupling. -/
theorem lowSpinCentralKComputedEffectiveMultiplicity_eqv_count
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) :
    lowSpinCentralKComputedEffectiveMultiplicity
        w hw K hK volume ≈
      Q'.ofNat (volume + 1) := by
  unfold lowSpinCentralKComputedEffectiveMultiplicity effectiveMultiplicity
  rw [lowSpinCentralKPositiveRawReplication_count w hw K hK volume]
  have hfloor := lowSpinCentralKComputedRawRowRatioFloor_eq_one
    w hw K hK volume
  unfold lowSpinCentralKComputedRawRowRatioFloor at hfloor
  rw [hfloor]
  exact Q'.mul_one_eqv (Q'.ofNat (volume + 1))

theorem lowSpinCentralKComputedEffectiveMultiplicity_pos
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) :
    (0 : Q') < lowSpinCentralKComputedEffectiveMultiplicity
      w hw K hK volume :=
  (lowSpinCentralKPositiveRawReplication
    w hw K hK volume).effectiveMultiplicity_pos

theorem lowSpinCentralKReferenceMarginal_le_reciprocalEffective
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (volume : Nat) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K (volume + 1)
        (lowSpinCentralReferenceState volume) ≤
      Q'.divPos 1
        (lowSpinCentralKComputedEffectiveMultiplicity
          w hw K hK volume)
        (lowSpinCentralKComputedEffectiveMultiplicity_pos
          w hw K hK volume) := by
  exact referenceMarginal_le_reciprocalEffectiveMultiplicity
    (lowSpinCentralKPositiveRawReplication w hw K hK volume)

private theorem one_le_epsilon_mul_ofNat_succ_of_den_le
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {volume : Nat} (hvolume : epsilon.den ≤ volume) :
    (1 : Q') ≤ epsilon * Q'.ofNat (volume + 1) := by
  have hnum : (0 : Int) < epsilon.num := Q'.num_pos_of_pos hepsilon
  show (1 : Q').num *
        ((epsilon * Q'.ofNat (volume + 1)).den : Int) ≤
      (epsilon * Q'.ofNat (volume + 1)).num *
        ((1 : Q').den : Int)
  show (1 : Int) *
        ((epsilon * Q'.ofNat (volume + 1)).den : Int) ≤
      (epsilon.num * ((volume + 1 : Nat) : Int)) * (1 : Int)
  rw [Q'.mul_den_cast]
  change (1 : Int) * ((epsilon.den : Int) * 1) ≤
    (epsilon.num * ((volume + 1 : Nat) : Int)) * 1
  simp only [Int.one_mul, Int.mul_one]
  have hden : (epsilon.denPred + 1 : Int) ≤ (volume : Int) :=
    Int.ofNat_le.mpr hvolume
  have honeNum : (1 : Int) ≤ epsilon.num := by omega
  have hvolumeNonnegative : (0 : Int) ≤ (volume : Int) :=
    Int.natCast_nonneg volume
  have hscaled : (volume : Int) ≤ epsilon.num * (volume : Int) := by
    have := Int.mul_le_mul_of_nonneg_right honeNum hvolumeNonnegative
    simpa only [Int.one_mul] using this
  have hsucc : epsilon.num * (volume : Int) ≤
      epsilon.num * ((volume + 1 : Nat) : Int) := by
    apply Int.mul_le_mul_of_nonneg_left
    · exact Int.ofNat_le.mpr (Nat.le_succ volume)
    · omega
  exact Int.le_trans hden (Int.le_trans hscaled hsucc)

/-- Uniformly over every finite cutoff `K >= 1`, the fixed slice-zero
stationary marginal is at most `epsilon` once `volume >= epsilon.den`. -/
theorem lowSpinCentralKReferenceMarginal_le_epsilon
    (w : Q') (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (volume : Nat) (hvolume : epsilon.den ≤ volume) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K (volume + 1)
        (lowSpinCentralReferenceState volume) ≤
      epsilon := by
  let effective :=
    lowSpinCentralKComputedEffectiveMultiplicity w hw K hK volume
  have heffectivePos : (0 : Q') < effective :=
    lowSpinCentralKComputedEffectiveMultiplicity_pos
      w hw K hK volume
  have heffective : effective ≈ Q'.ofNat (volume + 1) :=
    lowSpinCentralKComputedEffectiveMultiplicity_eqv_count
      w hw K hK volume
  have honeCount :
      (1 : Q') ≤ epsilon * Q'.ofNat (volume + 1) :=
    one_le_epsilon_mul_ofNat_succ_of_den_le hepsilon hvolume
  have hepsilonEffective :
      epsilon * effective ≈ epsilon * Q'.ofNat (volume + 1) :=
    Q'.mul_eqv_congr_left epsilon effective
      (Q'.ofNat (volume + 1)) heffective
  have honeEffective : (1 : Q') ≤ epsilon * effective :=
    Q'.le_trans' _ _ _ honeCount
      (Q'.le_of_eqv (Q'.eqv_symm hepsilonEffective))
  have hreciprocal : Q'.divPos 1 effective heffectivePos ≤ epsilon :=
    Q'.divPos_le_of_le_mul 1 effective heffectivePos honeEffective
  exact Q'.le_trans' _ _ _
    (lowSpinCentralKReferenceMarginal_le_reciprocalEffective
      w hw K hK volume)
    hreciprocal

end YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization

#print axioms
  YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization.timeSliceParametricKPhysicalTerm_eqv_between
#print axioms
  YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization.lowSpinCentralKAssembledTerm_eqv_between
#print axioms
  YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization.lowSpinCentralKPositiveRawRows_eqv
#print axioms
  YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization.lowSpinCentralKPositiveRawReplication
#print axioms
  YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization.lowSpinCentralKComputedRawRowRatioFloor_eq_one
#print axioms
  YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization.lowSpinCentralKComputedEffectiveMultiplicity_eqv_count
#print axioms
  YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization.lowSpinCentralKReferenceMarginal_le_epsilon
