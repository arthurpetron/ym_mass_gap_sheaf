/-
# Exact activity matching for the central/small-lift signed path

The central unit cube moves from coarse cell `111` to fine cell `000`, while
the outward x small-lift cube moves from coarse cell `000` to fine cell `100`.
Both are literal six-face boundaries.  This module first proves equality of
their complete cutoff-one spin-summed activities and only then records the
signed cancellation at the intermediate cell.
-/

import YMGap.Continuum.Z4AxisCubeSixFaceActivity
import YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
import YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.Z4OutwardCentralSmallLiftActivityPair

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. At cutoff one, a fixed support fibre is a singleton -/

theorem physicalLabellingsWithSupport_one_perm_componentLabel
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (physicalLabellingsWithSupport 1 n support).Perm
      [componentLabel support] := by
  apply perm_of_nodup_mem_iff_constructive
    (physicalLabellingsWithSupport 1 n support)
    [componentLabel support]
    (physicalLabellingsWithSupport_nodup 1 n support)
    (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
  intro physical
  constructor
  · intro hphysical
    have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
    have hleft : physical ∈ explicitPhysicalLabellings 1 n := by
      simpa [explicitPhysicalLabellings, physicalFaceEdges] using hparts.1
    have hright : componentLabel support ∈
        explicitPhysicalLabellings 1 n :=
      componentLabel_mem_explicitPhysicalLabellings_one hsupport
    have hids : excitedPlaquetteIds n physical =
        excitedPlaquetteIds n (componentLabel support) :=
      hparts.2.trans
        (excitedPlaquetteIds_componentLabel_eq_support hsupport).symm
    have heq := cutoffOne_supportIds_injective hleft hright hids
    exact List.mem_singleton.mpr heq
  · intro hphysical
    have heq := List.mem_singleton.mp hphysical
    subst physical
    apply mem_physicalLabellingsWithSupport_iff.mpr
    exact ⟨by
      simpa [explicitPhysicalLabellings, physicalFaceEdges] using
        (componentLabel_mem_explicitPhysicalLabellings_one hsupport),
      excitedPlaquetteIds_componentLabel_eq_support hsupport⟩

/-- The complete fixed-support spin sum at cutoff one is exactly its literal
fundamental-spin canonical activity; no omitted higher-spin term exists. -/
theorem couplingParametricKSupportActivity_one_eqv_canonical
    (coupling : Q') {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    couplingParametricKSupportActivity coupling 1 n support ≈
      canonicalSurfaceActivity coupling n support := by
  unfold couplingParametricKSupportActivity
  refine Q'.eqv_trans _
    (listQSum (parametricKPhysicalTerm coupling 1 n)
      [componentLabel support]) _ ?_ ?_
  · exact listQSum_perm _
      (physicalLabellingsWithSupport_one_perm_componentLabel hsupport)
  · change parametricKPhysicalTerm coupling 1 n
        (componentLabel support) + 0 ≈
      canonicalSurfaceActivity coupling n support
    refine Q'.eqv_trans _
      (parametricKPhysicalTerm coupling 1 n (componentLabel support)) _
      (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
    unfold canonicalSurfaceActivity
    exact parametricKPhysicalTerm_one_eqv_localized coupling n
      (componentLabel support)

/-- A singleton family carried by a closed cutoff-one surface has the exact
face-count activity, with the full fixed-support spin sum already included. -/
theorem couplingParametricKSingletonSupportFamilyActivity_one_eqv_pow_length
    (coupling : Q') {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hincidence : ∀ {link : Z4Link},
      link ∈ touchedPhysicalLinks n (componentLabel support) →
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length = 2) :
    couplingParametricKSupportFamilyActivity coupling 1 n [support] ≈
      (coeffW coupling 1) ^ support.length := by
  refine Q'.eqv_trans _
    (couplingParametricKSupportActivity coupling 1 n support) _
    (Q'.mul_one_eqv _) ?_
  refine Q'.eqv_trans _
    (canonicalSurfaceActivity coupling n support) _
    (couplingParametricKSupportActivity_one_eqv_canonical
      coupling hsupport) ?_
  exact canonicalSurfaceActivity_eqv_pow_length_of_incidence_two
    coupling hsupport hincidence

/-! ## 2. Exact equality of the two complete six-face activities -/

theorem outwardCentralCubeRoot_activity_eqv_pow_six
    (coupling : Q') :
    canonicalSurfaceActivity coupling 6
        (axisCoarseRoot zeroAxisOffset) ≈
      (coeffW coupling 1) ^ 6 :=
  axisCoarseRoot_canonicalSurfaceActivity_eqv_pow_six coupling
    zeroAxisOffset (Or.inl rfl)

theorem outwardCentral_smallLift_supportActivities_eqv
    (coupling : Q') :
    couplingParametricKSupportActivity coupling 1 6
        (axisCoarseRoot zeroAxisOffset) ≈
      couplingParametricKSupportActivity coupling 1 6
        outwardXFineSmallLiftRoot := by
  have hcentralSupport := canonicalSurfacePolymer_mem_faceSupports
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
  have hsmallSupport := canonicalSurfacePolymer_mem_faceSupports
    outwardXFineSmallLiftRoot_mem_canonical
  refine Q'.eqv_trans _
    (canonicalSurfaceActivity coupling 6
      (axisCoarseRoot zeroAxisOffset)) _
    (couplingParametricKSupportActivity_one_eqv_canonical
      coupling hcentralSupport) ?_
  refine Q'.eqv_trans _ ((coeffW coupling 1) ^ 6) _
    (outwardCentralCubeRoot_activity_eqv_pow_six coupling) ?_
  refine Q'.eqv_trans _
    (canonicalSurfaceActivity coupling 6 outwardXFineSmallLiftRoot) _
    (Q'.eqv_symm
      (outwardXFineSmallLiftRoot_activity_eqv_pow_six coupling)) ?_
  exact Q'.eqv_symm
    (couplingParametricKSupportActivity_one_eqv_canonical
      coupling hsmallSupport)

theorem outwardCentral_smallLift_singletonFamilyActivities_eqv
    (coupling : Q') :
    couplingParametricKSupportFamilyActivity coupling 1 6
        [axisCoarseRoot zeroAxisOffset] ≈
      couplingParametricKSupportFamilyActivity coupling 1 6
        [outwardXFineSmallLiftRoot] := by
  refine Q'.eqv_trans _
    (couplingParametricKSupportActivity coupling 1 6
      (axisCoarseRoot zeroAxisOffset)) _ ?_ ?_
  · exact Q'.mul_one_eqv _
  · refine Q'.eqv_trans _
      (couplingParametricKSupportActivity coupling 1 6
        outwardXFineSmallLiftRoot) _
      (outwardCentral_smallLift_supportActivities_eqv coupling) ?_
    exact Q'.eqv_symm (Q'.mul_one_eqv _)

/-! ## 3. The central cube moves from `111` to `000` -/

theorem outwardCentralCoarseQueryFaces_mem_surface :
    outwardXQueryFace ∈ axisCubeSurface zeroAxisOffset ∧
    outwardYQueryFace ∈ axisCubeSurface zeroAxisOffset ∧
    outwardZQueryFace ∈ axisCubeSurface zeroAxisOffset := by
  rw [axisCubeSurface_zero_eq]
  exact ⟨by
      simpa [outwardXQueryFace] using
        (cubeFace_mem_unitCubeSurface .rightYZ),
    by
      simpa [outwardYQueryFace] using
        (cubeFace_mem_unitCubeSurface .backXZ),
    by
      simpa [outwardZQueryFace] using
        (cubeFace_mem_unitCubeSurface .topXY)⟩

theorem outwardCentralCubeRoot_coarsePattern_111 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel (axisCoarseRoot zeroAxisOffset)) =
      (true, true, true) := by
  have hx : ∀ id, id ∈ outwardXQuery →
      id ∈ axisCoarseRoot zeroAxisOffset := by
    unfold outwardXQuery axisCoarseRoot
    exact coarseFaceQuerySupport_subset_geometricRoot zeroAxisOffset
      .rightYZ (axisCubeSurface zeroAxisOffset)
      outwardCentralCoarseQueryFaces_mem_surface.1
  have hy : ∀ id, id ∈ outwardYQuery →
      id ∈ axisCoarseRoot zeroAxisOffset := by
    unfold outwardYQuery axisCoarseRoot
    exact coarseFaceQuerySupport_subset_geometricRoot zeroAxisOffset
      .backXZ (axisCubeSurface zeroAxisOffset)
      outwardCentralCoarseQueryFaces_mem_surface.2.1
  have hz : ∀ id, id ∈ outwardZQuery →
      id ∈ axisCoarseRoot zeroAxisOffset := by
    unfold outwardZQuery axisCoarseRoot
    exact coarseFaceQuerySupport_subset_geometricRoot zeroAxisOffset
      .topXY (axisCubeSurface zeroAxisOffset)
      outwardCentralCoarseQueryFaces_mem_surface.2.2
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl)) hx,
    componentLabel_subsupportEvent_true
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl)) hy,
    componentLabel_subsupportEvent_true
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl)) hz]

theorem outwardCentralFineQueryFaces_not_mem_surface :
    outwardXFineQueryFace ∉ axisCubeSurface zeroAxisOffset ∧
    outwardYFineQueryFace ∉ axisCubeSurface zeroAxisOffset ∧
    outwardZFineQueryFace ∉ axisCubeSurface zeroAxisOffset := by
  rw [axisCubeSurface_zero_eq]
  simp [outwardXFineQueryFace, outwardYFineQueryFace,
    outwardZFineQueryFace, unitCubeSurface, dyadicCell, dyadicVertex,
    axisShiftPlaquette, axisShiftVertex, zeroAxisOffset, cubeFace]

theorem outwardCentralCubeRoot_finePattern_000 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel (axisCoarseRoot zeroAxisOffset)) =
      (false, false, false) := by
  have hx : ¬ (∀ id, id ∈ outwardXFineQuery →
      id ∈ axisCoarseRoot zeroAxisOffset) := by
    unfold axisCoarseRoot
    rw [outwardXFineQuery_eq_geometric]
    exact fineFaceQuerySupport_not_subset_geometricRoot zeroAxisOffset
      (Or.inl rfl) .rightYZ .origin (axisCubeSurface zeroAxisOffset)
      (axisCubeSurface_subset_box_six zeroAxisOffset (Or.inl rfl))
      outwardCentralFineQueryFaces_not_mem_surface.1
  have hy : ¬ (∀ id, id ∈ outwardYFineQuery →
      id ∈ axisCoarseRoot zeroAxisOffset) := by
    unfold axisCoarseRoot
    rw [outwardYFineQuery_eq_geometric]
    exact fineFaceQuerySupport_not_subset_geometricRoot zeroAxisOffset
      (Or.inl rfl) .backXZ .origin (axisCubeSurface zeroAxisOffset)
      (axisCubeSurface_subset_box_six zeroAxisOffset (Or.inl rfl))
      outwardCentralFineQueryFaces_not_mem_surface.2.1
  have hz : ¬ (∀ id, id ∈ outwardZFineQuery →
      id ∈ axisCoarseRoot zeroAxisOffset) := by
    unfold axisCoarseRoot
    rw [outwardZFineQuery_eq_geometric]
    exact fineFaceQuerySupport_not_subset_geometricRoot zeroAxisOffset
      (Or.inl rfl) .topXY .origin (axisCubeSurface zeroAxisOffset)
      (axisCubeSurface_subset_box_six zeroAxisOffset (Or.inl rfl))
      outwardCentralFineQueryFaces_not_mem_surface.2.2
  apply outwardFinePattern_eq_of_events
  · exact componentLabel_subsupportEvent_false
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl)) hx
  · exact componentLabel_subsupportEvent_false
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl)) hy
  · exact componentLabel_subsupportEvent_false
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl)) hz

theorem outwardCentralCubeRoot_coarseFamilyPattern_111 :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [axisCoarseRoot zeroAxisOffset] = (true, true, true) := by
  have hpattern := outwardCentralCubeRoot_coarsePattern_111
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent at hpattern
  rw [componentLabelAmbientFamily_eq_singleton
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))] at hpattern
  simpa only [outwardComponentSubsupportFamilyPattern] using hpattern

theorem outwardCentralCubeRoot_fineFamilyPattern_000 :
    outwardComponentSubsupportFamilyPattern outwardFineQueries
        [axisCoarseRoot zeroAxisOffset] = (false, false, false) := by
  have hpattern := outwardCentralCubeRoot_finePattern_000
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent at hpattern
  rw [componentLabelAmbientFamily_eq_singleton
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))] at hpattern
  simpa only [outwardComponentSubsupportFamilyPattern] using hpattern

/-! ## 4. The small lift moves from `000` to `100` -/

theorem outwardCoarseQueryFaces_not_mem_smallLift :
    outwardXQueryFace ∉ outwardXFineSmallLiftSurface ∧
    outwardYQueryFace ∉ outwardXFineSmallLiftSurface ∧
    outwardZQueryFace ∉ outwardXFineSmallLiftSurface := by
  simp [outwardXQueryFace, outwardYQueryFace, outwardZQueryFace,
    outwardXFineSmallLiftSurface, outwardXFineSmallLiftOffset,
    axisCubeSurface, unitCubeSurface, axisShiftPlaquette, axisShiftVertex,
    doubleAxisOffset, xAxisOffset, zeroAxisOffset, cubeFace]

theorem outwardXFineSmallLiftRoot_coarsePattern_000 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXFineSmallLiftRoot) =
      (false, false, false) := by
  have hx : ¬ (∀ id, id ∈ outwardXQuery →
      id ∈ outwardXFineSmallLiftRoot) := by
    unfold outwardXFineSmallLiftRoot outwardXQuery
    exact coarseFaceQuerySupport_not_subset_geometricRoot zeroAxisOffset
      (Or.inl rfl) .rightYZ outwardXFineSmallLiftSurface
      outwardXFineSmallLiftSurface_subset_box_six
      outwardCoarseQueryFaces_not_mem_smallLift.1
  have hy : ¬ (∀ id, id ∈ outwardYQuery →
      id ∈ outwardXFineSmallLiftRoot) := by
    unfold outwardXFineSmallLiftRoot outwardYQuery
    exact coarseFaceQuerySupport_not_subset_geometricRoot zeroAxisOffset
      (Or.inl rfl) .backXZ outwardXFineSmallLiftSurface
      outwardXFineSmallLiftSurface_subset_box_six
      outwardCoarseQueryFaces_not_mem_smallLift.2.1
  have hz : ¬ (∀ id, id ∈ outwardZQuery →
      id ∈ outwardXFineSmallLiftRoot) := by
    unfold outwardXFineSmallLiftRoot outwardZQuery
    exact coarseFaceQuerySupport_not_subset_geometricRoot zeroAxisOffset
      (Or.inl rfl) .topXY outwardXFineSmallLiftSurface
      outwardXFineSmallLiftSurface_subset_box_six
      outwardCoarseQueryFaces_not_mem_smallLift.2.2
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_false
      outwardXFineSmallLiftRoot_mem_canonical hx,
    componentLabel_subsupportEvent_false
      outwardXFineSmallLiftRoot_mem_canonical hy,
    componentLabel_subsupportEvent_false
      outwardXFineSmallLiftRoot_mem_canonical hz]

theorem outwardXFineSmallLiftRoot_coarseFamilyPattern_000 :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [outwardXFineSmallLiftRoot] = (false, false, false) := by
  have hpattern := outwardXFineSmallLiftRoot_coarsePattern_000
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent at hpattern
  rw [componentLabelAmbientFamily_eq_singleton
    outwardXFineSmallLiftRoot_mem_canonical] at hpattern
  simpa only [outwardComponentSubsupportFamilyPattern] using hpattern

theorem outwardCentral_smallLift_exact_twoStepPath :
    (outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [axisCoarseRoot zeroAxisOffset] = (true, true, true) ∧
      outwardComponentSubsupportFamilyPattern outwardFineQueries
        [axisCoarseRoot zeroAxisOffset] = (false, false, false)) ∧
    (outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [outwardXFineSmallLiftRoot] = (false, false, false) ∧
      outwardComponentSubsupportFamilyPattern outwardFineQueries
        [outwardXFineSmallLiftRoot] = (true, false, false)) :=
  ⟨⟨outwardCentralCubeRoot_coarseFamilyPattern_111,
      outwardCentralCubeRoot_fineFamilyPattern_000⟩,
    ⟨outwardXFineSmallLiftRoot_coarseFamilyPattern_000,
      outwardXFineSmallLift_familyPattern_100⟩⟩

#print axioms physicalLabellingsWithSupport_one_perm_componentLabel
#print axioms couplingParametricKSupportActivity_one_eqv_canonical
#print axioms couplingParametricKSingletonSupportFamilyActivity_one_eqv_pow_length
#print axioms outwardCentralCubeRoot_activity_eqv_pow_six
#print axioms outwardCentral_smallLift_supportActivities_eqv
#print axioms outwardCentral_smallLift_singletonFamilyActivities_eqv
#print axioms outwardCentralCubeRoot_coarsePattern_111
#print axioms outwardCentralCubeRoot_finePattern_000
#print axioms outwardXFineSmallLiftRoot_coarsePattern_000
#print axioms outwardCentral_smallLift_exact_twoStepPath

end YMGap.Continuum.Z4OutwardCentralSmallLiftActivityPair
