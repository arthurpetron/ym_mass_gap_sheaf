/-
# A many-time-slice family of projected fine cubes

For a horizon `h`, place one odd fine unit cube on each Euclidean-time slice
`0, ..., h` and encode all copies in the common size-`4+h` box.  A copy is
first translated by its slice index and then zero-extended to the common box.
Its numerical support is the corresponding exact canonical re-encoding.

Distinct slices share neither a face nor an actual lattice link because all
six faces are spatial and every boundary link retains the face's time
coordinate.  This pairwise fact is lifted constructively to the recursive
`LinkSeparatedFamily` predicate for the duplicate-free attached range.

Successive slices alternate the two assignments retained by the global slot
projector.  Exact time-translation and cross-volume covariance identify every
projected raw mass with its actual physical production summand.  Consequently
the full finite product is exactly the production weight of the physical
union in the common horizon box.
-/

import YMGap.Continuum.Z4DyadicSlabCubeTranslatedProjectedComposition

namespace YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
open YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition
open YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge
open YMGap.Continuum.Z4DyadicSlabCubeTranslatedProjectedComposition
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights

local infix:50 " ≈ " => Q'.eqv

private theorem sameSupport_map_local
    {X Y : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (h : sameSupport (L := z4Chain.toLattice) X Y) :
    sameSupport (L := z4Chain.toLattice)
      (X.map mapP) (Y.map mapP) := by
  constructor
  · intro target htarget
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
    exact List.mem_map.mpr ⟨source, h.1 source hsource, rfl⟩
  · intro target htarget
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
    exact List.mem_map.mpr ⟨source, h.2 source hsource, rfl⟩

private theorem range_nodup_local : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      exact ⟨range_nodup_local n,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun x hx y hy hxy => by
          have hyN : y = n := List.mem_singleton.mp hy
          rw [hxy, hyN] at hx
          exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl n)⟩

/-! ## 1. Alternating corrected-slab assignments -/

def alternatingCubeFineSlotAssignment : Nat → CubeFineSlotAssignment
  | 0 => oddFineCubeSlotAssignment
  | k + 1 =>
      reflectCubeFineSlotAssignmentTime
        (alternatingCubeFineSlotAssignment k)

theorem alternatingCubeFineSlotAssignment_zero :
    alternatingCubeFineSlotAssignment 0 =
      oddFineCubeSlotAssignment := rfl

theorem alternatingCubeFineSlotAssignment_one :
    alternatingCubeFineSlotAssignment 1 =
      reflectedOddFineCubeSlotAssignment := rfl

theorem alternatingCubeFineSlotAssignment_succ (k : Nat) :
    alternatingCubeFineSlotAssignment (k + 1) =
      reflectCubeFineSlotAssignmentTime
        (alternatingCubeFineSlotAssignment k) := rfl

theorem alternatingCubeFineSlotAssignment_mem_closed :
    ∀ k : Nat, alternatingCubeFineSlotAssignment k ∈
      closedCubeFineSlotStateSpace
  | 0 => oddFineCubeSlotAssignment_mem_closed
  | k + 1 =>
      reflectCubeFineSlotAssignmentTime_mem_closed
        (alternatingCubeFineSlotAssignment_mem_closed k)

/-! ## 2. Common-horizon time-slice embeddings -/

abbrev TimeSliceIndex (horizon : Nat) :=
  {k : Nat // k ∈ List.range (horizon + 1)}

def timeSliceIndices (horizon : Nat) : List (TimeSliceIndex horizon) :=
  (List.range (horizon + 1)).attach

theorem timeSliceIndices_nodup (horizon : Nat) :
    (timeSliceIndices horizon).Nodup :=
  attach_nodup_of_nodup _ (range_nodup_local (horizon + 1))

theorem timeSliceIndex_le
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    index.val ≤ horizon := by
  have hlt := List.mem_range.mp index.property
  omega

def shiftedOddFineCubeSurface (shift : Nat) : List Z4Plaq :=
  oddFineUnitCubeSurface.map (timeShiftPlaquette shift)

def timeSliceTransportedPhysical
    (horizon : Nat) (index : TimeSliceIndex horizon) : EdgeLabelling :=
  transportPhysical (4 + index.val) (4 + horizon)
    (timeShiftTransportPhysical index.val 4 oddFineCubePhysical)

def timeSliceSupportIds
    (horizon : Nat) (index : TimeSliceIndex horizon) : List Nat :=
  transportPolymer (4 + index.val) (4 + horizon)
    (timeShiftCanonicalRoot index.val 4 oddFineUnitCubeSupportIds)

def timeSlicePhysical
    (horizon : Nat) (index : TimeSliceIndex horizon) : EdgeLabelling :=
  componentLabel (timeSliceSupportIds horizon index)

private theorem oddFineCubePhysical_mem_bounded :
    oddFineCubePhysical ∈ boundedEdgeLabellings 1
      (List.range (plaquetteEdgeCount 4)) := by
  simpa [explicitPhysicalLabellings, physicalFaceEdges] using
    oddFineCubePhysical_mem

theorem timeSliceShiftedPhysical_mem_bounded
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    timeShiftTransportPhysical index.val 4 oddFineCubePhysical ∈
      boundedEdgeLabellings 1
        (List.range (plaquetteEdgeCount (4 + index.val))) :=
  timeShiftTransportPhysical_mem_bounded
    (shift := index.val) oddFineCubePhysical_mem_bounded

theorem timeSliceTransportedPhysical_mem
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    timeSliceTransportedPhysical horizon index ∈
      explicitPhysicalLabellings 1 (4 + horizon) := by
  unfold timeSliceTransportedPhysical explicitPhysicalLabellings
    physicalFaceEdges
  exact transportPhysical_mem_bounded
    (timeSliceShiftedPhysical_mem_bounded index)

theorem timeSliceSupportIds_mem
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    timeSliceSupportIds horizon index ∈
      cutoffOneFaceSupports (4 + horizon) := by
  unfold timeSliceSupportIds
  exact transportPolymer_mem_cutoffOneFaceSupports _ _ _

theorem timeSlicePhysical_mem
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    timeSlicePhysical horizon index ∈
      explicitPhysicalLabellings 1 (4 + horizon) := by
  unfold timeSlicePhysical
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  exact List.mem_map.mpr
    ⟨timeSliceSupportIds horizon index,
      timeSliceSupportIds_mem index, rfl⟩

theorem timeSliceTransportedPhysical_excitedSupport
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    excitedPlaquetteIds (4 + horizon)
        (timeSliceTransportedPhysical horizon index) =
      timeSliceSupportIds horizon index := by
  unfold timeSliceTransportedPhysical timeSliceSupportIds
  rw [excitedPlaquetteIds_transportPhysical,
    excitedPlaquetteIds_timeShiftTransportPhysical,
    excitedPlaquetteIds_componentLabel_eq_support
      oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports]

theorem timeSliceTransportedPhysical_eq_componentLabel
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    timeSliceTransportedPhysical horizon index =
      timeSlicePhysical horizon index := by
  apply cutoffOne_supportIds_injective
    (timeSliceTransportedPhysical_mem index)
    (timeSlicePhysical_mem index)
  unfold timeSlicePhysical
  rw [timeSliceTransportedPhysical_excitedSupport,
    excitedPlaquetteIds_componentLabel_eq_support
      (timeSliceSupportIds_mem index)]

/-! ## 3. Pairwise separation of distinct slices -/

theorem shiftedOddFineCubeSurface_time
    {shift : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ shiftedOddFineCubeSurface shift) :
    plaquette.1.2.2.2 = shift := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  have htime := oddFineUnitCubeSurface_time_zero hsource
  simp only [timeShiftPlaquette, timeShiftVertex] at htime ⊢
  omega

theorem shiftedOddFineCubeSurface_spatialPlane
    {shift : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ shiftedOddFineCubeSurface shift) :
    plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12 := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq]
  simpa only [timeShiftPlaquette] using
    oddFineUnitCubeSurface_spatialPlane hsource

private theorem spatialPlaquette_edge_timeCoordinate
    {plaquette : Z4Plaq} {link : Z4Link}
    (hplane : plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12)
    (hlink : link ∈ edgesOf plaquette) :
    link.1.2.2.2 = plaquette.1.2.2.2 := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rcases hplane with rfl | rfl | rfl <;>
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink <;>
    rcases hlink with rfl | rfl | rfl | rfl <;> rfl

theorem distinctShiftedOddFineCubeSurfaces_disjoint
    {leftShift rightShift : Nat} (hne : leftShift ≠ rightShift) :
    SupportsDisjoint (shiftedOddFineCubeSurface leftShift)
      (shiftedOddFineCubeSurface rightShift) := by
  intro plaquette hleft hright
  apply hne
  exact (shiftedOddFineCubeSurface_time hleft).symm.trans
    (shiftedOddFineCubeSurface_time hright)

theorem distinctShiftedOddFineCubeSurfaces_linkDisjoint
    {leftShift rightShift : Nat} (hne : leftShift ≠ rightShift)
    {left right : Z4Plaq} {link : Z4Link}
    (hleft : left ∈ shiftedOddFineCubeSurface leftShift)
    (hright : right ∈ shiftedOddFineCubeSurface rightShift)
    (hlinkLeft : link ∈ edgesOf left)
    (hlinkRight : link ∈ edgesOf right) : False := by
  have hleftTime := spatialPlaquette_edge_timeCoordinate
    (shiftedOddFineCubeSurface_spatialPlane hleft) hlinkLeft
  have hrightTime := spatialPlaquette_edge_timeCoordinate
    (shiftedOddFineCubeSurface_spatialPlane hright) hlinkRight
  apply hne
  exact (shiftedOddFineCubeSurface_time hleft).symm.trans
    (hleftTime.symm.trans
      (hrightTime.trans (shiftedOddFineCubeSurface_time hright)))

private theorem timeShiftRoot_same_shiftedSurface
    (shift : Nat) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (4 + shift)
        (timeShiftCanonicalRoot shift 4 oddFineUnitCubeSupportIds))
      (shiftedOddFineCubeSurface shift) := by
  unfold timeShiftCanonicalRoot shiftedOddFineCubeSurface
  exact sameSupport_trans
    (geometricSupportIds_sameSupport (by
      intro plaquette hplaquette
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
      exact timeShiftPlaquette_mem_box_add
        (geometricPolymer_subset_box
          oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports
          source hsource)))
    (sameSupport_map_local (timeShiftPlaquette shift)
      oddFineUnitCubeSupportIds_sameSupport)

theorem timeSliceSupportIds_sameSupport
    {horizon : Nat} (index : TimeSliceIndex horizon) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (4 + horizon)
        (timeSliceSupportIds horizon index))
      (shiftedOddFineCubeSurface index.val) := by
  have hshiftMem :
      timeShiftCanonicalRoot index.val 4 oddFineUnitCubeSupportIds ∈
        cutoffOneFaceSupports (4 + index.val) := by
    unfold timeShiftCanonicalRoot
    exact geometricSupportIds_mem_cutoffOneFaceSupports _ _
  exact sameSupport_trans
    (sameSupport_symm
      (transportPolymer_sameSupport (by
        have hle := timeSliceIndex_le index
        omega)
        hshiftMem))
    (timeShiftRoot_same_shiftedSurface index.val)

theorem timeSliceSupportIds_disjoint
    {horizon : Nat} {left right : TimeSliceIndex horizon}
    (hne : left.val ≠ right.val) :
    SupportsDisjoint (timeSliceSupportIds horizon left)
      (timeSliceSupportIds horizon right) := by
  intro face hleft hright
  have hleftGeom : boxPlaquetteAt (4 + horizon) face ∈
      geometricPolymer (4 + horizon)
        (timeSliceSupportIds horizon left) :=
    List.mem_map.mpr ⟨face, hleft, rfl⟩
  have hrightGeom : boxPlaquetteAt (4 + horizon) face ∈
      geometricPolymer (4 + horizon)
        (timeSliceSupportIds horizon right) :=
    List.mem_map.mpr ⟨face, hright, rfl⟩
  exact distinctShiftedOddFineCubeSurfaces_disjoint hne
    (boxPlaquetteAt (4 + horizon) face)
    (timeSliceSupportIds_sameSupport left |>.1 _ hleftGeom)
    (timeSliceSupportIds_sameSupport right |>.1 _ hrightGeom)

theorem timeSliceSupportIds_separated
    {horizon : Nat} {left right : TimeSliceIndex horizon}
    (hne : left.val ≠ right.val) :
    SupportsSeparated (faceLinkAdjacentB (4 + horizon))
      (timeSliceSupportIds horizon left)
      (timeSliceSupportIds horizon right) := by
  intro leftFace hleft rightFace hright
  cases hadj : faceLinkAdjacentB (4 + horizon) leftFace rightFace with
  | false => rfl
  | true =>
      have hactual := actualAdjacentOfFaceLinkAdjacent hadj
      have hleftGeom : boxPlaquetteAt (4 + horizon) leftFace ∈
          geometricPolymer (4 + horizon)
            (timeSliceSupportIds horizon left) :=
        List.mem_map.mpr ⟨leftFace, hleft, rfl⟩
      have hrightGeom : boxPlaquetteAt (4 + horizon) rightFace ∈
          geometricPolymer (4 + horizon)
            (timeSliceSupportIds horizon right) :=
        List.mem_map.mpr ⟨rightFace, hright, rfl⟩
      have hleftBoundary := hactual.on_p
      have hrightBoundary := hactual.on_q
      change z4Boundary
          (boxPlaquetteAt (4 + horizon) leftFace) hactual.link = true
        at hleftBoundary
      change z4Boundary
          (boxPlaquetteAt (4 + horizon) rightFace) hactual.link = true
        at hrightBoundary
      exact False.elim
        (distinctShiftedOddFineCubeSurfaces_linkDisjoint hne
          (timeSliceSupportIds_sameSupport left |>.1 _ hleftGeom)
          (timeSliceSupportIds_sameSupport right |>.1 _ hrightGeom)
          (of_decide_eq_true hleftBoundary)
          (of_decide_eq_true hrightBoundary))

/-! ## 4. Recursive separation of the entire attached range -/

private theorem timeSliceIndex_val_ne_of_ne
    {horizon : Nat} {left right : TimeSliceIndex horizon}
    (hne : left ≠ right) : left.val ≠ right.val := by
  intro hval
  apply hne
  exact Subtype.ext hval

theorem timeSlicePhysicalList_linkSeparated
    (horizon : Nat) :
    ∀ (indices : List (TimeSliceIndex horizon)), indices.Nodup →
      LinkSeparatedFamily (4 + horizon)
        (indices.map (timeSlicePhysical horizon))
  | [], _ => trivial
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      have hheadDisjoint : ∀ support,
          support ∈ tail.map (timeSliceSupportIds horizon) →
          SupportsDisjoint (timeSliceSupportIds horizon head) support := by
        intro support hsupport
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hsupport
        apply timeSliceSupportIds_disjoint
        apply timeSliceIndex_val_ne_of_ne
        intro heq
        subst index
        exact hparts.1 hindex
      have hheadSeparated : ∀ support,
          support ∈ tail.map (timeSliceSupportIds horizon) →
          SupportsSeparated (faceLinkAdjacentB (4 + horizon))
            (timeSliceSupportIds horizon head) support := by
        intro support hsupport
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hsupport
        apply timeSliceSupportIds_separated
        apply timeSliceIndex_val_ne_of_ne
        intro heq
        subst index
        exact hparts.1 hindex
      have hface := componentLabel_faceDisjoint_union
        (4 + horizon) (timeSliceSupportIds horizon head)
        (tail.map (timeSliceSupportIds horizon)) hheadDisjoint
      have hlink := componentLabel_linkSeparated_union
        (4 + horizon) (timeSliceSupportIds horizon head)
        (tail.map (timeSliceSupportIds horizon)) hheadSeparated
      have htail := timeSlicePhysicalList_linkSeparated horizon tail hparts.2
      change
        FaceDisjoint (4 + horizon) (timeSlicePhysical horizon head)
            (binaryUnionLabels (tail.map (timeSlicePhysical horizon))) ∧
          LinkSeparated (4 + horizon) (timeSlicePhysical horizon head)
              (binaryUnionLabels (tail.map (timeSlicePhysical horizon))) ∧
            LinkSeparatedFamily (4 + horizon)
              (tail.map (timeSlicePhysical horizon))
      unfold timeSlicePhysical
      simp only [List.map_map] at hface hlink
      exact ⟨hface, hlink, htail⟩

theorem allTimeSlicePhysicals_linkSeparated (horizon : Nat) :
    LinkSeparatedFamily (4 + horizon)
      ((timeSliceIndices horizon).map (timeSlicePhysical horizon)) :=
  timeSlicePhysicalList_linkSeparated horizon
    (timeSliceIndices horizon) (timeSliceIndices_nodup horizon)

/-! ## 5. Exact bridge and finite-product identity -/

theorem timeSliceRawWeight_eqv_production
    (w : Q') {horizon : Nat} (index : TimeSliceIndex horizon) :
    closedCubeFineSlotRawWeight w
        (alternatingCubeFineSlotAssignment index.val) ≈
      parametricLocalizedSpinFoamWeight w (4 + horizon)
        (timeSlicePhysical horizon index) := by
  exact Q'.eqv_trans _
    (closedCubeFineSlotRawWeight w oddFineCubeSlotAssignment) _
    (Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
      (closedCubeFineSlotRawWeight_eqv_pow_six w _)
      (Q'.eqv_symm
        (closedCubeFineSlotRawWeight_eqv_pow_six w
          oddFineCubeSlotAssignment)))
    (Q'.eqv_trans _
      (parametricLocalizedSpinFoamWeight w 4 oddFineCubePhysical) _
      (oddFineCubeProjectedSummandBridge w).raw_eqv
      (Q'.eqv_trans _
        (parametricKPhysicalTerm w 1 4 oddFineCubePhysical) _
        (Q'.eqv_symm
          (parametricKPhysicalTerm_one_eqv_localized
            w 4 oddFineCubePhysical))
        (Q'.eqv_trans _
          (parametricKPhysicalTerm w 1 (4 + index.val)
            (timeShiftTransportPhysical index.val 4
              oddFineCubePhysical)) _
          (parametricKPhysicalTerm_timeShift w
            (shift := index.val) oddFineCubePhysical_mem_bounded)
          (Q'.eqv_trans _
            (parametricKPhysicalTerm w 1 (4 + horizon)
              (timeSliceTransportedPhysical horizon index)) _
            (parametricKPhysicalTerm_cross_volume w (by
              have hle := timeSliceIndex_le index
              omega) (timeSliceShiftedPhysical_mem_bounded index))
            (by
              rw [timeSliceTransportedPhysical_eq_componentLabel index]
              exact parametricKPhysicalTerm_one_eqv_localized
                w (4 + horizon) (timeSlicePhysical horizon index))))))

def timeSliceProjectedBridge
    (w : Q') (horizon : Nat) (index : TimeSliceIndex horizon) :
    ProjectedFineCubeSummandBridge w (4 + horizon) where
  assignment := alternatingCubeFineSlotAssignment index.val
  assignment_mem := alternatingCubeFineSlotAssignment_mem_closed index.val
  physical := timeSlicePhysical horizon index
  physical_mem := timeSlicePhysical_mem index
  raw_eqv := timeSliceRawWeight_eqv_production w index

def manyTimeSliceProjectedBridges
    (w : Q') (horizon : Nat) :
    List (ProjectedFineCubeSummandBridge w (4 + horizon)) :=
  (timeSliceIndices horizon).map (timeSliceProjectedBridge w horizon)

theorem manyTimeSliceProjectedBridges_length
    (w : Q') (horizon : Nat) :
    (manyTimeSliceProjectedBridges w horizon).length = horizon + 1 := by
  unfold manyTimeSliceProjectedBridges timeSliceIndices
  simp only [List.length_map, List.length_attach, List.length_range]

def manyTimeSliceProjectedFamily
    (w : Q') (horizon : Nat) :
    LinkSeparatedProjectedFineCubeFamily w (4 + horizon) where
  bridges := manyTimeSliceProjectedBridges w horizon
  separated := by
    unfold manyTimeSliceProjectedBridges
    simpa [timeSliceProjectedBridge] using
      allTimeSlicePhysicals_linkSeparated horizon

theorem manyTimeSliceProjectedFamily_unionProduction
    (w : Q') (horizon : Nat) :
    projectedFineCubeRawProduct w
        (manyTimeSliceProjectedBridges w horizon) ≈
      parametricLocalizedSpinFoamWeight w (4 + horizon)
        (binaryUnionLabels
          ((manyTimeSliceProjectedBridges w horizon).map
            fun bridge => bridge.physical)) :=
  linkSeparatedProjectedFineCubeFamily_unionProduction
    (manyTimeSliceProjectedFamily w horizon)

/-! ## Dependency gates -/

#print axioms alternatingCubeFineSlotAssignment_mem_closed
#print axioms timeSliceIndices_nodup
#print axioms timeSliceTransportedPhysical_mem
#print axioms timeSliceTransportedPhysical_eq_componentLabel
#print axioms distinctShiftedOddFineCubeSurfaces_linkDisjoint
#print axioms timeSliceSupportIds_sameSupport
#print axioms timeSliceSupportIds_disjoint
#print axioms timeSliceSupportIds_separated
#print axioms timeSlicePhysicalList_linkSeparated
#print axioms allTimeSlicePhysicals_linkSeparated
#print axioms timeSliceRawWeight_eqv_production
#print axioms manyTimeSliceProjectedBridges_length
#print axioms manyTimeSliceProjectedFamily
#print axioms manyTimeSliceProjectedFamily_unionProduction
#print axioms oddFineCube_self_not_faceDisjoint

end YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
