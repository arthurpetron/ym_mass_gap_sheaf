/-
# Low-spin growing-volume replica geometry

The existing common-horizon time-slice construction already supplies the
geometric core needed by the alternate replica route.  In a box of size
`4 + horizon`, it places `horizon + 1` pairwise link-separated unit-cube
surfaces, each carrying only twice-spin zero or one.  This module records the
missing row-family facts explicitly: every transported support is inhabited,
the physical time-slice encoding is injective, the resulting list is
duplicate free with exact growing length, and every individual production summand has
the same positive weight `(coeffW w 1)^6`.

This is the concrete low-spin volume geometry, not yet the adapter into the
central reflected positive-row replication gate.  No common reflected raw-row
floor, cofinal all-vector gap, continuum measure, or Clay theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.Z4DyadicSlabCubeManyTimeSlicePositiveWeight

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry

set_option maxRecDepth 200000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
open YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.HKPos

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fixed local complexity and injective volume placements -/

private def lowSpinTimeShiftRoot_nonempty
    (shift : Nat) :
    Σ' face : Nat,
      face ∈ timeShiftCanonicalRoot shift 4
        oddFineUnitCubeSupportIds := by
  have hsame :
      sameSupport
        (geometricPolymer (4 + shift)
          (timeShiftCanonicalRoot shift 4 oddFineUnitCubeSupportIds))
        ((geometricPolymer 4 oddFineUnitCubeSupportIds).map
          (timeShiftPlaquette shift)) := by
    unfold timeShiftCanonicalRoot
    apply geometricSupportIds_sameSupport
    intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact timeShiftPlaquette_mem_box_add
      (geometricPolymer_subset_box
        oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports source hsource)
  have hsource : boxPlaquetteAt 4 504 ∈
      geometricPolymer 4 oddFineUnitCubeSupportIds :=
    List.mem_map.mpr ⟨504, by decide, rfl⟩
  have hshifted : timeShiftPlaquette shift (boxPlaquetteAt 4 504) ∈
      (geometricPolymer 4 oddFineUnitCubeSupportIds).map
        (timeShiftPlaquette shift) :=
    List.mem_map.mpr ⟨boxPlaquetteAt 4 504, hsource, rfl⟩
  have hencoded := hsame.2 _ hshifted
  obtain ⟨face, hface, _⟩ :=
    decodeMapMember (boxPlaquetteAt (4 + shift))
      (timeShiftCanonicalRoot shift 4 oddFineUnitCubeSupportIds)
      (timeShiftPlaquette shift (boxPlaquetteAt 4 504)) hencoded
  exact ⟨face, hface⟩

def lowSpinTimeSliceSupport_nonempty
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    Σ' face : Nat, face ∈ timeSliceSupportIds horizon index := by
  have hshiftMem :
      timeShiftCanonicalRoot index.val 4 oddFineUnitCubeSupportIds ∈
        cutoffOneFaceSupports (4 + index.val) := by
    unfold timeShiftCanonicalRoot
    exact geometricSupportIds_mem_cutoffOneFaceSupports _ _
  obtain ⟨sourceFace, hsourceFace⟩ :=
    lowSpinTimeShiftRoot_nonempty index.val
  obtain ⟨targetFace, htargetFace, _⟩ :=
    transportPolymerMemberTarget
      (n := 4 + index.val) (m := 4 + horizon)
      (support := timeShiftCanonicalRoot index.val 4
        oddFineUnitCubeSupportIds) (by
      have hle := timeSliceIndex_le index
      omega) hshiftMem hsourceFace
  unfold timeSliceSupportIds
  exact ⟨targetFace, htargetFace⟩

/-- Distinct time indices produce distinct literal cutoff-one physical
labellings in the same common box. -/
theorem timeSlicePhysical_injective (horizon : Nat) :
    Function.Injective (timeSlicePhysical horizon) := by
  intro left right heq
  by_cases hval : left.val = right.val
  · exact Subtype.ext hval
  · have hdisjoint := timeSliceSupportIds_disjoint
      (horizon := horizon) (left := left) (right := right) hval
    have hsupports : timeSliceSupportIds horizon left =
        timeSliceSupportIds horizon right := by
      have hexcited := congrArg (excitedPlaquetteIds (4 + horizon)) heq
      unfold timeSlicePhysical at hexcited
      rw [excitedPlaquetteIds_componentLabel_eq_support
          (timeSliceSupportIds_mem left),
        excitedPlaquetteIds_componentLabel_eq_support
          (timeSliceSupportIds_mem right)] at hexcited
      exact hexcited
    obtain ⟨face, hface⟩ := lowSpinTimeSliceSupport_nonempty left
    exact False.elim
      (hdisjoint face hface (by rw [← hsupports]; exact hface))

/-- The complete list of low-spin time-slice replicas in the common horizon
box. -/
def lowSpinTimeSlicePhysicals (horizon : Nat) : List EdgeLabelling :=
  (timeSliceIndices horizon).map (timeSlicePhysical horizon)

theorem lowSpinTimeSlicePhysicals_length (horizon : Nat) :
    (lowSpinTimeSlicePhysicals horizon).length = horizon + 1 := by
  unfold lowSpinTimeSlicePhysicals timeSliceIndices
  simp only [List.length_map, List.length_attach, List.length_range]

theorem lowSpinTimeSlicePhysicals_nodup (horizon : Nat) :
    (lowSpinTimeSlicePhysicals horizon).Nodup := by
  unfold lowSpinTimeSlicePhysicals
  apply nodup_map_of_injOn
  · exact timeSliceIndices_nodup horizon
  · intro left _hleft right _hright heq
    exact timeSlicePhysical_injective horizon heq

/-- Each replica remains in the literal cutoff-one physical carrier of the
common growing box. -/
theorem lowSpinTimeSlicePhysical_mem
    {horizon : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ lowSpinTimeSlicePhysicals horizon) :
    physical ∈ explicitPhysicalLabellings 1 (4 + horizon) := by
  obtain ⟨index, _hindex, rfl⟩ := List.mem_map.mp hphysical
  exact timeSlicePhysical_mem index

/-! ## 2. Uniform individual low-spin production weight -/

theorem timeSliceProduction_eqv_spinOneCubeWeight
    (w : Q') {horizon : Nat} (index : TimeSliceIndex horizon) :
    parametricLocalizedSpinFoamWeight w (4 + horizon)
        (timeSlicePhysical horizon index) ≈
      (coeffW w 1) ^ 6 := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (timeSliceRawWeight_eqv_production w index))
    (closedCubeFineSlotRawWeight_eqv_pow_six w
      (alternatingCubeFineSlotAssignment index.val))

theorem timeSliceProduction_pos
    {w : Q'} (hw : (0 : Q') < w)
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    (0 : Q') < parametricLocalizedSpinFoamWeight w (4 + horizon)
      (timeSlicePhysical horizon index) := by
  have hcoefficient : (0 : Q') < coeffW w 1 := coeffW_pos hw 1
  have hpower : (0 : Q') < (coeffW w 1) ^ 6 := by
    exact pow_pos hcoefficient 6
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv (timeSliceProduction_eqv_spinOneCubeWeight w index))

end YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry.lowSpinTimeSliceSupport_nonempty
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry.timeSlicePhysical_injective
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry.lowSpinTimeSlicePhysicals_nodup
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry.timeSliceProduction_eqv_spinOneCubeWeight
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry.timeSliceProduction_pos
