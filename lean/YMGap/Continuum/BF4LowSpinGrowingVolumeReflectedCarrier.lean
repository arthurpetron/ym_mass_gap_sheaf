/-
# Low-spin growing-volume reflected carrier

The common-box time-slice replicas are already literal cutoff-one physical
labellings.  This file proves that they lie in the corrected reflection slab,
uses the existing ambient-to-slab restriction to reindex them, and then
selects a linearly growing family supported entirely in the central lower
half.  The resulting `volume + 1` states are literal, duplicate-free members
of `centralHalfStates 1 (volume + 1)`.

This closes the geometric carrier adapter needed by the volume-parametric
positive-row route.  It does not yet prove a reflected kernel floor, a raw-row
sum floor, a cutoff-uniform gap, a continuum limit, or the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option autoImplicit false

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Every common-box time slice is a corrected-slab state -/

/-- A common box of side `4 + horizon` is the ambient corner box of the
corrected slab of extent `3 + horizon`. -/
theorem timeSliceAmbient_eq_slabAmbient (horizon : Nat) :
    (3 + horizon) + 1 = 4 + horizon := by
  omega

/-- Every time-slice replica excites only spatial plaquettes at its own time,
so it misses all top temporal faces omitted from the corrected slab. -/
theorem timeSlicePhysical_ambientSlabSupported
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    ambientSlabSupportedB (3 + horizon)
      (timeSlicePhysical horizon index) = true := by
  apply (ambientSlabSupportedB_true_iff_excited_support
    (3 + horizon) (timeSlicePhysical horizon index)).2
  intro id hid
  have hambient : (3 + horizon) + 1 = 4 + horizon :=
    timeSliceAmbient_eq_slabAmbient horizon
  have hidSupport : id ∈ timeSliceSupportIds horizon index := by
    rw [hambient] at hid
    unfold timeSlicePhysical at hid
    rw [excitedPlaquetteIds_componentLabel_eq_support
      (timeSliceSupportIds_mem index)] at hid
    exact hid
  have hidPhysical : id ∈ physicalFaceEdges (4 + horizon) :=
    mem_of_mem_sublists
      (physicalFaceEdges (4 + horizon))
      (timeSliceSupportIds horizon index)
      (timeSliceSupportIds_mem index) id hidSupport
  have hgeometric : boxPlaquetteAt (4 + horizon) id ∈
      geometricPolymer (4 + horizon)
        (timeSliceSupportIds horizon index) :=
    List.mem_map.mpr ⟨id, hidSupport, rfl⟩
  have hshifted : boxPlaquetteAt (4 + horizon) id ∈
      shiftedOddFineCubeSurface index.val :=
    (timeSliceSupportIds_sameSupport index).1 _ hgeometric
  rw [hambient]
  apply (mem_boundaryCompleteSlabPlaquettes
    (3 + horizon) (boxPlaquetteAt (4 + horizon) id)).mpr
  refine ⟨?_, ?_⟩
  · rw [hambient]
    exact boxPlaquetteAt_mem_boxPlaquettes_of_physical hidPhysical
  · have htime := shiftedOddFineCubeSurface_time hshifted
    have hplane := shiftedOddFineCubeSurface_spatialPlane hshifted
    rcases hplane with hplane | hplane | hplane
    all_goals unfold plaquetteTimeAdmissible
    all_goals rw [hplane, htime]
    all_goals have hindex := timeSliceIndex_le index
    all_goals omega

/-- Restrict a common-box time-slice labelling to corrected-slab numerical
face coordinates. -/
def timeSliceSlabPhysical
    (horizon : Nat) (index : TimeSliceIndex horizon) : EdgeLabelling :=
  ambientToSlabPhysical (3 + horizon)
    (timeSlicePhysical horizon index)

theorem timeSliceSlabPhysical_mem
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    timeSliceSlabPhysical horizon index ∈
      boundedEdgeLabellings 1 (slabPhysicalFaceEdges (3 + horizon)) := by
  unfold timeSliceSlabPhysical
  apply ambientToSlabPhysical_mem_bounded
  have hphysical := timeSlicePhysical_mem index
  simpa [explicitPhysicalLabellings, physicalFaceEdges,
    timeSliceAmbient_eq_slabAmbient horizon] using hphysical

/-- Zero-extending the slab reindex recovers the original literal common-box
labelling. -/
theorem timeSliceSlabPhysical_roundtrip
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    slabToAmbientPhysical (3 + horizon)
        (timeSliceSlabPhysical horizon index) =
      timeSlicePhysical horizon index := by
  unfold timeSliceSlabPhysical
  apply slabToAmbientPhysical_ambientToSlab
  · have hphysical := timeSlicePhysical_mem index
    simpa [explicitPhysicalLabellings, physicalFaceEdges,
      timeSliceAmbient_eq_slabAmbient horizon] using hphysical
  · exact timeSlicePhysical_ambientSlabSupported index

theorem timeSliceSlabPhysical_injective (horizon : Nat) :
    Function.Injective (timeSliceSlabPhysical horizon) := by
  intro left right heq
  have hextended := congrArg (slabToAmbientPhysical (3 + horizon)) heq
  rw [timeSliceSlabPhysical_roundtrip left,
    timeSliceSlabPhysical_roundtrip right] at hextended
  exact timeSlicePhysical_injective horizon hextended

/-! ## 2. A linearly growing central lower-half family -/

/-- We use a common-box horizon `2 * volume` and the central reflection half
`volume + 1`.  Their ambient side lengths agree exactly. -/
theorem lowSpinCentralAmbient_eq (volume : Nat) :
    4 + 2 * volume = centralAmbient (volume + 1) := by
  unfold centralAmbient centralExtent
  omega

theorem lowSpinCentralExtent_eq (volume : Nat) :
    3 + 2 * volume = centralExtent (volume + 1) := by
  unfold centralExtent
  omega

abbrev LowSpinCentralIndex (volume : Nat) :=
  {k : Nat // k ∈ List.range (volume + 1)}

/-- Embed the selected lower indices `0, ..., volume` into the full common
horizon `0, ..., 2 * volume`. -/
def lowSpinCentralTimeSliceIndex
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    TimeSliceIndex (2 * volume) :=
  ⟨index.val, List.mem_range.mpr (by
    have hlt := List.mem_range.mp index.property
    omega)⟩

def lowSpinCentralIndices (volume : Nat) :
    List (LowSpinCentralIndex volume) :=
  (List.range (volume + 1)).attach

theorem lowSpinCentralIndices_length (volume : Nat) :
    (lowSpinCentralIndices volume).length = volume + 1 := by
  unfold lowSpinCentralIndices
  simp only [List.length_attach, List.length_range]

theorem lowSpinCentralIndices_nodup (volume : Nat) :
    (lowSpinCentralIndices volume).Nodup := by
  simpa [lowSpinCentralIndices, timeSliceIndices] using
    (timeSliceIndices_nodup volume)

def lowSpinCentralSlabPhysical
    (volume : Nat) (index : LowSpinCentralIndex volume) : EdgeLabelling :=
  ambientToSlabPhysical (centralExtent (volume + 1))
    (timeSlicePhysical (2 * volume)
      (lowSpinCentralTimeSliceIndex index))

theorem lowSpinCentralSlabPhysical_mem
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    lowSpinCentralSlabPhysical volume index ∈
      boundedEdgeLabellings 1
        (slabPhysicalFaceEdges (centralExtent (volume + 1))) := by
  unfold lowSpinCentralSlabPhysical
  apply ambientToSlabPhysical_mem_bounded
  have hphysical := timeSlicePhysical_mem
    (lowSpinCentralTimeSliceIndex index)
  simpa [explicitPhysicalLabellings, physicalFaceEdges,
    lowSpinCentralAmbient_eq volume] using hphysical

theorem lowSpinCentralSlabPhysical_roundtrip
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    slabToAmbientPhysical (centralExtent (volume + 1))
        (lowSpinCentralSlabPhysical volume index) =
      timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index) := by
  unfold lowSpinCentralSlabPhysical
  apply slabToAmbientPhysical_ambientToSlab
  · have hphysical := timeSlicePhysical_mem
      (lowSpinCentralTimeSliceIndex index)
    simpa [explicitPhysicalLabellings, physicalFaceEdges,
      lowSpinCentralAmbient_eq volume] using hphysical
  · simpa [lowSpinCentralExtent_eq volume] using
      (timeSlicePhysical_ambientSlabSupported
        (lowSpinCentralTimeSliceIndex index))

theorem lowSpinCentralSlabPhysical_injective (volume : Nat) :
    Function.Injective (lowSpinCentralSlabPhysical volume) := by
  intro left right heq
  have hextended := congrArg
    (slabToAmbientPhysical (centralExtent (volume + 1))) heq
  rw [lowSpinCentralSlabPhysical_roundtrip left,
    lowSpinCentralSlabPhysical_roundtrip right] at hextended
  have hindex := timeSlicePhysical_injective (2 * volume) hextended
  have hval : left.val = right.val :=
    congrArg
      (fun embedded : TimeSliceIndex (2 * volume) => embedded.val)
      hindex
  apply Subtype.ext
  exact hval

/-! ## 3. The selected slab states live entirely in the lower half -/

private theorem lowSpinCentralShiftedSurface_lower
    {volume : Nat} (index : LowSpinCentralIndex volume)
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ shiftedOddFineCubeSurface index.val) :
    plaquetteHalfSide (volume + 1) plaquette = .lower := by
  have htime := shiftedOddFineCubeSurface_time hplaquette
  have hplane := shiftedOddFineCubeSurface_spatialPlane hplaquette
  have hindex := List.mem_range.mp index.property
  rcases hplane with hplane | hplane | hplane
  all_goals obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  all_goals simp only at htime hplane
  all_goals subst plane
  all_goals simp only [plaquetteHalfSide, spatialHalfSide]
  all_goals rw [if_pos (by omega)]

/-- Because every excited face is on a selected lower spatial slice,
restricting the reindexed slab state to `centralLowerFaceIds` changes no
coordinate. -/
theorem lowSpinCentralLowerRestriction_eq
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    centralLowerRestriction (volume + 1)
        (lowSpinCentralSlabPhysical volume index) =
      lowSpinCentralSlabPhysical volume index := by
  have hbounded := lowSpinCentralSlabPhysical_mem index
  have hsound := boundedEdgeLabellings_sound 1
    (slabPhysicalFaceEdges (centralExtent (volume + 1)))
    (lowSpinCentralSlabPhysical volume index) hbounded
  funext sourceId
  by_cases hlower : sourceId ∈ centralLowerFaceIds (volume + 1)
  · simp only [centralLowerRestriction, if_pos hlower]
  · simp only [centralLowerRestriction, if_neg hlower]
    by_cases hphysical : sourceId ∈
        slabPhysicalFaceEdges (centralExtent (volume + 1))
    · unfold lowSpinCentralSlabPhysical
      rw [ambientToSlabPhysical_eq_on_physical hphysical]
      have hslab := slabPlaquetteAt_mem hphysical
      have hbox :=
        (mem_boundaryCompleteSlabPlaquettes
          (centralExtent (volume + 1)) _).mp hslab |>.1
      obtain ⟨targetId, hindexed⟩ := exists_mem_enumerate hbox
      rw [geometricSpinOfPhysical_eq_of_enumerate hindexed]
      apply Eq.symm
      apply componentLabel_eq_zero_of_not_mem
      intro htarget
      have htargetEq :
          boxPlaquetteAt (centralAmbient (volume + 1)) targetId =
            slabPlaquetteAt (centralExtent (volume + 1)) sourceId :=
        boxPlaquetteAt_eq_of_enumerate hindexed
      have hgeometric :
          slabPlaquetteAt (centralExtent (volume + 1)) sourceId ∈
            geometricPolymer (4 + 2 * volume)
              (timeSliceSupportIds (2 * volume)
                (lowSpinCentralTimeSliceIndex index)) := by
        rw [← lowSpinCentralAmbient_eq volume] at htargetEq
        exact List.mem_map.mpr ⟨targetId, htarget, htargetEq⟩
      have hshifted :
          slabPlaquetteAt (centralExtent (volume + 1)) sourceId ∈
            shiftedOddFineCubeSurface index.val := by
        exact (timeSliceSupportIds_sameSupport
          (lowSpinCentralTimeSliceIndex index)).1 _ hgeometric
      apply hlower
      apply mem_centralLowerFaceIds.mpr
      exact ⟨hphysical,
        lowSpinCentralShiftedSurface_lower index hshifted⟩
    · exact (hsound.2 sourceId hphysical).symm

/-- The literal lower-half state consumed by the reflected Gram/kernel. -/
def lowSpinCentralLowerState
    (volume : Nat) (index : LowSpinCentralIndex volume) : EdgeLabelling :=
  centralLowerRestriction (volume + 1)
    (lowSpinCentralSlabPhysical volume index)

theorem lowSpinCentralLowerState_eq_slabPhysical
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    lowSpinCentralLowerState volume index =
      lowSpinCentralSlabPhysical volume index := by
  exact lowSpinCentralLowerRestriction_eq index

theorem lowSpinCentralLowerState_mem
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    lowSpinCentralLowerState volume index ∈
      centralHalfStates 1 (volume + 1) := by
  unfold lowSpinCentralLowerState centralHalfStates
  exact centralLowerRestriction_mem
    (lowSpinCentralSlabPhysical_mem index)

theorem lowSpinCentralLowerState_injective (volume : Nat) :
    Function.Injective (lowSpinCentralLowerState volume) := by
  intro left right heq
  rw [lowSpinCentralLowerState_eq_slabPhysical left,
    lowSpinCentralLowerState_eq_slabPhysical right] at heq
  exact lowSpinCentralSlabPhysical_injective volume heq

def lowSpinCentralLowerStates (volume : Nat) : List EdgeLabelling :=
  (lowSpinCentralIndices volume).map
    (lowSpinCentralLowerState volume)

theorem lowSpinCentralLowerStates_length (volume : Nat) :
    (lowSpinCentralLowerStates volume).length = volume + 1 := by
  unfold lowSpinCentralLowerStates
  rw [List.length_map, lowSpinCentralIndices_length]

theorem lowSpinCentralLowerStates_nodup (volume : Nat) :
    (lowSpinCentralLowerStates volume).Nodup := by
  unfold lowSpinCentralLowerStates
  apply nodup_map_of_injOn
  · exact lowSpinCentralIndices_nodup volume
  · intro left _hleft right _hright heq
    exact lowSpinCentralLowerState_injective volume heq

theorem lowSpinCentralLowerStates_mem
    {volume : Nat} {state : EdgeLabelling}
    (hstate : state ∈ lowSpinCentralLowerStates volume) :
    state ∈ centralHalfStates 1 (volume + 1) := by
  obtain ⟨index, _hindex, rfl⟩ := List.mem_map.mp hstate
  exact lowSpinCentralLowerState_mem index

end YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier.timeSlicePhysical_ambientSlabSupported
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier.timeSliceSlabPhysical_roundtrip
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier.lowSpinCentralLowerRestriction_eq
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier.lowSpinCentralLowerState_injective
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier.lowSpinCentralLowerStates_nodup
