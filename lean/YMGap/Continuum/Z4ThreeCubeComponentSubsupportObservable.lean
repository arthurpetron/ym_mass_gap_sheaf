/-
# Component sub-support observables for the three-cube block

Exact canonical-component occurrence cannot represent overlapping local
coordinates: link-overlapping canonical roots are mutually exclusive.  The
replacement observable asks whether a prescribed finite face sub-support is
contained in one decoded connected component.  Several overlapping queries
may therefore be true on the same component.

This module first supplies the exact Boolean decoder and then instantiates it
on three nonempty face queries inside the unshifted coarse and refined cube
components.  Their component labels give literal `111` witnesses with
derived positive character/fusion weights.
-/

import YMGap.Continuum.Z4OverlappingCanonicalRootOccurrenceFence
import YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder

namespace YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4OverlappingCanonicalRootOccurrenceFence
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4RetunedParityPhysicalMixtureKernel
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPhysicalCubeLeakage
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeBareCouplingShift
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact component sub-support decoder -/

def componentContainsSubsupportB
    (query component : List Nat) : Bool :=
  query.all (fun face => decide (face ∈ component))

def familyContainsComponentSubsupportB
    (query : List Nat) (family : List (List Nat)) : Bool :=
  family.any (componentContainsSubsupportB query)

theorem componentContainsSubsupportB_true_iff
    (query component : List Nat) :
    componentContainsSubsupportB query component = true ↔
      ∀ face, face ∈ query → face ∈ component := by
  unfold componentContainsSubsupportB
  constructor
  · intro hquery face hface
    have h := List.all_eq_true.mp hquery face hface
    exact of_decide_eq_true h
  · intro hquery
    apply List.all_eq_true.mpr
    intro face hface
    exact decide_eq_true (hquery face hface)

theorem familyContainsComponentSubsupportB_true_iff
    (query : List Nat) (family : List (List Nat)) :
    familyContainsComponentSubsupportB query family = true ↔
      ∃ component, component ∈ family ∧
        ∀ face, face ∈ query → face ∈ component := by
  unfold familyContainsComponentSubsupportB
  constructor
  · intro hfamily
    obtain ⟨component, hcomponent, hquery⟩ :=
      List.any_eq_true.mp hfamily
    exact ⟨component, hcomponent,
      (componentContainsSubsupportB_true_iff query component).1 hquery⟩
  · rintro ⟨component, hcomponent, hquery⟩
    exact List.any_eq_true.mpr
      ⟨component, hcomponent,
        (componentContainsSubsupportB_true_iff query component).2 hquery⟩

theorem familyContainsComponentSubsupportB_singleton
    (face : Nat) (family : List (List Nat)) :
    familyContainsComponentSubsupportB [face] family =
      familyContainsFaceB face family := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hquery
    obtain ⟨component, hcomponent, hface⟩ :=
      (familyContainsComponentSubsupportB_true_iff [face] family).1 hquery
    exact (familyContainsFaceB_true_iff face family).2
      ⟨component, hcomponent, hface face List.mem_cons_self⟩
  · intro hface
    obtain ⟨component, hcomponent, hfaceComponent⟩ :=
      (familyContainsFaceB_true_iff face family).1 hface
    apply (familyContainsComponentSubsupportB_true_iff [face] family).2
    refine ⟨component, hcomponent, ?_⟩
    intro target htarget
    have heq : target = face := by simpa using htarget
    rw [heq]
    exact hfaceComponent

def physicalComponentSubsupportEvent
    (volume : Nat) (query : List Nat) (physical : EdgeLabelling) : Bool :=
  familyContainsComponentSubsupportB query
    (physicalCanonicalAmbientFamily volume physical)

theorem physicalComponentSubsupportEvent_true_iff
    (volume : Nat) (query : List Nat) (physical : EdgeLabelling) :
    physicalComponentSubsupportEvent volume query physical = true ↔
      ∃ component,
        component ∈ physicalCanonicalAmbientFamily volume physical ∧
        ∀ face, face ∈ query → face ∈ component := by
  exact familyContainsComponentSubsupportB_true_iff query
    (physicalCanonicalAmbientFamily volume physical)

theorem physicalComponentSingletonEvent_true_iff_excited
    (volume face : Nat) (physical : EdgeLabelling) :
    physicalComponentSubsupportEvent volume [face] physical = true ↔
      face ∈ excitedPlaquetteIds volume physical := by
  unfold physicalComponentSubsupportEvent
  rw [familyContainsComponentSubsupportB_singleton]
  constructor
  · intro hface
    obtain ⟨component, hcomponent, hfaceComponent⟩ :=
      (familyContainsFaceB_true_iff face
        (physicalCanonicalAmbientFamily volume physical)).1 hface
    exact (mem_physicalCanonicalAmbientFamily_flatten_iff
      volume physical face).1
      (List.mem_flatten.mpr
        ⟨component, hcomponent, hfaceComponent⟩)
  · intro hexcited
    have hflatten :=
      (mem_physicalCanonicalAmbientFamily_flatten_iff
        volume physical face).2 hexcited
    obtain ⟨component, hcomponent, hfaceComponent⟩ :=
      List.mem_flatten.mp hflatten
    exact (familyContainsFaceB_true_iff face
      (physicalCanonicalAmbientFamily volume physical)).2
      ⟨component, hcomponent, hfaceComponent⟩

/-! ## 2. Nonempty geometric face queries at both block scales -/

def axisCoarseFaceQuerySupport
    (offset : AxisOffset) (face : CubeFaceIndex) : List Nat :=
  geometricSupportIds 6
    [axisShiftPlaquette offset (cubeFace face)]

def axisFineFaceQuerySupport
    (offset : AxisOffset) (face : CubeFaceIndex)
    (index : DyadicCellIndex) : List Nat :=
  geometricSupportIds 6
    [dyadicCell (axisShiftPlaquette offset (cubeFace face)) index]

theorem axisCoarseFaceQuerySupport_subset_root
    (offset : AxisOffset) (face : CubeFaceIndex) :
    ∀ id, id ∈ axisCoarseFaceQuerySupport offset face →
      id ∈ axisCoarseRoot offset := by
  intro id hid
  have hparts := (mem_geometricSupportIds_iff 6
    [axisShiftPlaquette offset (cubeFace face)] id).1 hid
  apply (mem_geometricSupportIds_iff 6 (axisCubeSurface offset) id).2
  refine ⟨hparts.1, ?_⟩
  have heq : boxPlaquetteAt 6 id =
      axisShiftPlaquette offset (cubeFace face) := by
    simpa only [List.mem_singleton] using hparts.2
  rw [heq]
  exact List.mem_map.mpr
    ⟨cubeFace face, cubeFace_mem_unitCubeSurface face, rfl⟩

theorem axisFineFaceQuerySupport_subset_root
    (offset : AxisOffset) (face : CubeFaceIndex)
    (index : DyadicCellIndex) :
    ∀ id, id ∈ axisFineFaceQuerySupport offset face index →
      id ∈ axisFineRoot offset := by
  intro id hid
  have hparts := (mem_geometricSupportIds_iff 6
    [dyadicCell (axisShiftPlaquette offset (cubeFace face)) index] id).1 hid
  apply (mem_geometricSupportIds_iff 6
    (axisFineCubeSurface offset) id).2
  refine ⟨hparts.1, ?_⟩
  have heq : boxPlaquetteAt 6 id =
      dyadicCell (axisShiftPlaquette offset (cubeFace face)) index := by
    simpa only [List.mem_singleton] using hparts.2
  rw [heq]
  unfold axisFineCubeSurface
  apply (mem_dyadicSupportCells_iff _ _).2
  exact ⟨axisShiftPlaquette offset (cubeFace face),
    List.mem_map.mpr
      ⟨cubeFace face, cubeFace_mem_unitCubeSurface face, rfl⟩,
    dyadicCell_mem_cells _ _⟩

theorem axisCoarseFaceQuerySupport_nonempty
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset)
    (face : CubeFaceIndex) :
    ∃ id : Nat, id ∈ axisCoarseFaceQuerySupport offset face := by
  have hgeometric := axisCoarseFace_mem_geometricRoot
    offset hoffset face
  obtain ⟨id, hidRoot, hidEq⟩ := List.mem_map.mp hgeometric
  have hidPhysical : id ∈ physicalFaceEdges 6 :=
    mem_of_mem_sublists (physicalFaceEdges 6)
      (axisCoarseRoot offset)
      (canonicalSurfacePolymer_mem_faceSupports
        (axisCoarseRoot_mem_canonical offset hoffset)) id hidRoot
  refine ⟨id, (mem_geometricSupportIds_iff 6
    [axisShiftPlaquette offset (cubeFace face)] id).2
      ⟨hidPhysical, ?_⟩⟩
  simpa only [List.mem_singleton] using hidEq

theorem axisFineFaceQuerySupport_nonempty
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset)
    (face : CubeFaceIndex) (index : DyadicCellIndex) :
    ∃ id : Nat, id ∈ axisFineFaceQuerySupport offset face index := by
  have hgeometric := axisFineCell_mem_geometricRoot
    offset hoffset face index
  obtain ⟨id, hidRoot, hidEq⟩ := List.mem_map.mp hgeometric
  have hidPhysical : id ∈ physicalFaceEdges 6 :=
    mem_of_mem_sublists (physicalFaceEdges 6)
      (axisFineRoot offset)
      (canonicalSurfacePolymer_mem_faceSupports
        (axisFineRoot_mem_canonical offset hoffset)) id hidRoot
  refine ⟨id, (mem_geometricSupportIds_iff 6
    [dyadicCell (axisShiftPlaquette offset (cubeFace face)) index] id).2
      ⟨hidPhysical, ?_⟩⟩
  simpa only [List.mem_singleton] using hidEq

theorem coarseXAxisLeftFace_eq_zeroRightFace :
    axisShiftPlaquette xAxisOffset (cubeFace .leftYZ) =
      axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ) := by
  simp [axisShiftPlaquette, axisShiftVertex, xAxisOffset,
    zeroAxisOffset, cubeFace]

theorem coarseYAxisFrontFace_eq_zeroBackFace :
    axisShiftPlaquette yAxisOffset (cubeFace .frontXZ) =
      axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ) := by
  simp [axisShiftPlaquette, axisShiftVertex, yAxisOffset,
    zeroAxisOffset, cubeFace]

theorem coarseXAxisLeftQuery_eq_zeroRightQuery :
    axisCoarseFaceQuerySupport xAxisOffset .leftYZ =
      axisCoarseFaceQuerySupport zeroAxisOffset .rightYZ := by
  exact congrArg (fun plaquette : Z4Plaq =>
    geometricSupportIds 6 [plaquette])
    coarseXAxisLeftFace_eq_zeroRightFace

theorem coarseYAxisFrontQuery_eq_zeroBackQuery :
    axisCoarseFaceQuerySupport yAxisOffset .frontXZ =
      axisCoarseFaceQuerySupport zeroAxisOffset .backXZ := by
  exact congrArg (fun plaquette : Z4Plaq =>
    geometricSupportIds 6 [plaquette])
    coarseYAxisFrontFace_eq_zeroBackFace

theorem fineXAxisLeftQuery_eq_zeroRightQuery :
    axisFineFaceQuerySupport xAxisOffset .leftYZ .origin =
      axisFineFaceQuerySupport zeroAxisOffset .rightYZ .origin := by
  exact congrArg (fun plaquette : Z4Plaq =>
    geometricSupportIds 6 [dyadicCell plaquette .origin])
    coarseXAxisLeftFace_eq_zeroRightFace

theorem fineYAxisFrontQuery_eq_zeroBackQuery :
    axisFineFaceQuerySupport yAxisOffset .frontXZ .origin =
      axisFineFaceQuerySupport zeroAxisOffset .backXZ .origin := by
  exact congrArg (fun plaquette : Z4Plaq =>
    geometricSupportIds 6 [dyadicCell plaquette .origin])
    coarseYAxisFrontFace_eq_zeroBackFace

abbrev ComponentSubsupportQueryTriple :=
  List Nat × List Nat × List Nat

def componentSubsupportQueryLeft
    (queries : ComponentSubsupportQueryTriple) : List Nat := queries.1

def componentSubsupportQueryShared
    (queries : ComponentSubsupportQueryTriple) : List Nat := queries.2.1

def componentSubsupportQueryRight
    (queries : ComponentSubsupportQueryTriple) : List Nat := queries.2.2

private theorem ne_nil_of_exists_mem {A : Type} {xs : List A}
    (h : ∃ x, x ∈ xs) : xs ≠ [] := by
  rintro rfl
  obtain ⟨x, hx⟩ := h
  exact List.not_mem_nil hx

/-- An opaque package prevents the elaborator from normalizing the large
finite-box identifier list every time a concrete refined query is projected.
The geometric identity remains available as a checked field. -/
structure CertifiedComponentSubsupport
    (root geometricSupport : List Nat) where
  support : List Nat
  support_eq_geometric : support = geometricSupport
  subset_root : ∀ face, face ∈ support → face ∈ root
  nonempty : support ≠ []

opaque threeAxisCoarseLeftQuery :
    CertifiedComponentSubsupport (axisCoarseRoot zeroAxisOffset)
      (axisCoarseFaceQuerySupport zeroAxisOffset .rightYZ) := {
  support := axisCoarseFaceQuerySupport zeroAxisOffset .rightYZ
  support_eq_geometric := rfl
  subset_root := axisCoarseFaceQuerySupport_subset_root
    zeroAxisOffset .rightYZ
  nonempty := ne_nil_of_exists_mem
    (axisCoarseFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .rightYZ)
}

opaque threeAxisCoarseSharedQuery :
    CertifiedComponentSubsupport (axisCoarseRoot zeroAxisOffset)
      (axisCoarseFaceQuerySupport zeroAxisOffset .backXZ) := {
  support := axisCoarseFaceQuerySupport zeroAxisOffset .backXZ
  support_eq_geometric := rfl
  subset_root := axisCoarseFaceQuerySupport_subset_root
    zeroAxisOffset .backXZ
  nonempty := ne_nil_of_exists_mem
    (axisCoarseFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .backXZ)
}

opaque threeAxisCoarseRightQuery :
    CertifiedComponentSubsupport (axisCoarseRoot zeroAxisOffset)
      (axisCoarseFaceQuerySupport zeroAxisOffset .bottomXY) := {
  support := axisCoarseFaceQuerySupport zeroAxisOffset .bottomXY
  support_eq_geometric := rfl
  subset_root := axisCoarseFaceQuerySupport_subset_root
    zeroAxisOffset .bottomXY
  nonempty := ne_nil_of_exists_mem
    (axisCoarseFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .bottomXY)
}

opaque threeAxisFineLeftQuery :
    CertifiedComponentSubsupport (axisFineRoot zeroAxisOffset)
      (axisFineFaceQuerySupport zeroAxisOffset .rightYZ .origin) := {
  support := axisFineFaceQuerySupport zeroAxisOffset .rightYZ .origin
  support_eq_geometric := rfl
  subset_root := axisFineFaceQuerySupport_subset_root
    zeroAxisOffset .rightYZ .origin
  nonempty := ne_nil_of_exists_mem
    (axisFineFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .rightYZ .origin)
}

opaque threeAxisFineSharedQuery :
    CertifiedComponentSubsupport (axisFineRoot zeroAxisOffset)
      (axisFineFaceQuerySupport zeroAxisOffset .backXZ .origin) := {
  support := axisFineFaceQuerySupport zeroAxisOffset .backXZ .origin
  support_eq_geometric := rfl
  subset_root := axisFineFaceQuerySupport_subset_root
    zeroAxisOffset .backXZ .origin
  nonempty := ne_nil_of_exists_mem
    (axisFineFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .backXZ .origin)
}

opaque threeAxisFineRightQuery :
    CertifiedComponentSubsupport (axisFineRoot zeroAxisOffset)
      (axisFineFaceQuerySupport zeroAxisOffset .bottomXY .origin) := {
  support := axisFineFaceQuerySupport zeroAxisOffset .bottomXY .origin
  support_eq_geometric := rfl
  subset_root := axisFineFaceQuerySupport_subset_root
    zeroAxisOffset .bottomXY .origin
  nonempty := ne_nil_of_exists_mem
    (axisFineFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .bottomXY .origin)
}

theorem threeAxisCoarseLeftQuery_is_xInterface :
    threeAxisCoarseLeftQuery.support =
      axisCoarseFaceQuerySupport xAxisOffset .leftYZ := by
  exact Eq.trans threeAxisCoarseLeftQuery.support_eq_geometric
    coarseXAxisLeftQuery_eq_zeroRightQuery.symm

theorem threeAxisCoarseSharedQuery_is_yInterface :
    threeAxisCoarseSharedQuery.support =
      axisCoarseFaceQuerySupport yAxisOffset .frontXZ := by
  exact Eq.trans threeAxisCoarseSharedQuery.support_eq_geometric
    coarseYAxisFrontQuery_eq_zeroBackQuery.symm

theorem threeAxisFineLeftQuery_is_xInterface :
    threeAxisFineLeftQuery.support =
      axisFineFaceQuerySupport xAxisOffset .leftYZ .origin := by
  exact Eq.trans threeAxisFineLeftQuery.support_eq_geometric
    fineXAxisLeftQuery_eq_zeroRightQuery.symm

theorem threeAxisFineSharedQuery_is_yInterface :
    threeAxisFineSharedQuery.support =
      axisFineFaceQuerySupport yAxisOffset .frontXZ .origin := by
  exact Eq.trans threeAxisFineSharedQuery.support_eq_geometric
    fineYAxisFrontQuery_eq_zeroBackQuery.symm

def threeAxisCoarseComponentQueries : ComponentSubsupportQueryTriple :=
  (threeAxisCoarseLeftQuery.support,
    threeAxisCoarseSharedQuery.support,
    threeAxisCoarseRightQuery.support)

def threeAxisFineComponentQueries : ComponentSubsupportQueryTriple :=
  (threeAxisFineLeftQuery.support,
    threeAxisFineSharedQuery.support,
    threeAxisFineRightQuery.support)

theorem threeAxisCoarseComponentQueries_subset_zeroRoot :
    (∀ id, id ∈ componentSubsupportQueryLeft
        threeAxisCoarseComponentQueries →
      id ∈ axisCoarseRoot zeroAxisOffset) ∧
    (∀ id, id ∈ componentSubsupportQueryShared
        threeAxisCoarseComponentQueries →
      id ∈ axisCoarseRoot zeroAxisOffset) ∧
    (∀ id, id ∈ componentSubsupportQueryRight
        threeAxisCoarseComponentQueries →
      id ∈ axisCoarseRoot zeroAxisOffset) := by
  exact ⟨threeAxisCoarseLeftQuery.subset_root,
    threeAxisCoarseSharedQuery.subset_root,
    threeAxisCoarseRightQuery.subset_root⟩

theorem threeAxisFineComponentQueries_subset_zeroRoot :
    (∀ id, id ∈ componentSubsupportQueryLeft
        threeAxisFineComponentQueries →
      id ∈ axisFineRoot zeroAxisOffset) ∧
    (∀ id, id ∈ componentSubsupportQueryShared
        threeAxisFineComponentQueries →
      id ∈ axisFineRoot zeroAxisOffset) ∧
    (∀ id, id ∈ componentSubsupportQueryRight
        threeAxisFineComponentQueries →
      id ∈ axisFineRoot zeroAxisOffset) := by
  exact ⟨threeAxisFineLeftQuery.subset_root,
    threeAxisFineSharedQuery.subset_root,
    threeAxisFineRightQuery.subset_root⟩

theorem threeAxisCoarseComponentQueries_nonempty :
    componentSubsupportQueryLeft threeAxisCoarseComponentQueries ≠ [] ∧
      componentSubsupportQueryShared threeAxisCoarseComponentQueries ≠ [] ∧
      componentSubsupportQueryRight threeAxisCoarseComponentQueries ≠ [] :=
  ⟨threeAxisCoarseLeftQuery.nonempty,
    threeAxisCoarseSharedQuery.nonempty,
    threeAxisCoarseRightQuery.nonempty⟩

theorem threeAxisFineComponentQueries_nonempty :
    componentSubsupportQueryLeft threeAxisFineComponentQueries ≠ [] ∧
      componentSubsupportQueryShared threeAxisFineComponentQueries ≠ [] ∧
      componentSubsupportQueryRight threeAxisFineComponentQueries ≠ [] :=
  ⟨threeAxisFineLeftQuery.nonempty,
    threeAxisFineSharedQuery.nonempty,
    threeAxisFineRightQuery.nonempty⟩

/-! ## 3. Literal jointly-true component witnesses -/

def physicalComponentSubsupportPattern
    (volume : Nat) (queries : ComponentSubsupportQueryTriple)
    (physical : EdgeLabelling) : ThreeBlockPattern :=
  (physicalComponentSubsupportEvent volume
      (componentSubsupportQueryLeft queries) physical,
    physicalComponentSubsupportEvent volume
      (componentSubsupportQueryShared queries) physical,
    physicalComponentSubsupportEvent volume
      (componentSubsupportQueryRight queries) physical)

def physicalComponentSubsupportLeftEvent
    (volume : Nat) (queries : ComponentSubsupportQueryTriple) :
    EdgeLabelling → Bool :=
  physicalComponentSubsupportEvent volume
    (componentSubsupportQueryLeft queries)

def physicalComponentSubsupportSharedEvent
    (volume : Nat) (queries : ComponentSubsupportQueryTriple) :
    EdgeLabelling → Bool :=
  physicalComponentSubsupportEvent volume
    (componentSubsupportQueryShared queries)

def physicalComponentSubsupportRightEvent
    (volume : Nat) (queries : ComponentSubsupportQueryTriple) :
    EdgeLabelling → Bool :=
  physicalComponentSubsupportEvent volume
    (componentSubsupportQueryRight queries)

/-- The actual normalized physical law equipped with three same-component
sub-support coordinates. -/
def normalizedPhysicalThreeSubsupportLaw
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling where
  mass := normalizedPhysicalMass coupling hcoupling cutoff volume
  states := activityMatchedConfigurationStateSpace cutoff volume
  leftParameter := finiteEventMass
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (physicalComponentSubsupportLeftEvent volume queries)
  sharedParameter := finiteEventMass
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (physicalComponentSubsupportSharedEvent volume queries)
  rightParameter := finiteEventMass
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (physicalComponentSubsupportRightEvent volume queries)
  leftEvent := physicalComponentSubsupportLeftEvent volume queries
  sharedEvent := physicalComponentSubsupportSharedEvent volume queries
  rightEvent := physicalComponentSubsupportRightEvent volume queries
  mass_nonnegative :=
    normalizedPhysicalMass_nonnegative coupling hcoupling cutoff volume
  left_nonnegative := finiteEventMass_nonnegative _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
  left_le_one := finiteEventMass_le_one _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
    (normalizedPhysicalMass_total coupling hcoupling cutoff volume)
  shared_nonnegative := finiteEventMass_nonnegative _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
  shared_le_one := finiteEventMass_le_one _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
    (normalizedPhysicalMass_total coupling hcoupling cutoff volume)
  right_nonnegative := finiteEventMass_nonnegative _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
  right_le_one := finiteEventMass_le_one _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
    (normalizedPhysicalMass_total coupling hcoupling cutoff volume)
  left_mass := Q'.eqv_refl _
  shared_mass := Q'.eqv_refl _
  right_mass := Q'.eqv_refl _
  normalized := normalizedPhysicalMass_total
    coupling hcoupling cutoff volume

def activityMatchedFineThreeSubsupportLaw
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  normalizedPhysicalThreeSubsupportLaw
    fineCoupling hfine cutoff volume queries

def activityMatchedCoarseThreeSubsupportLaw
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  normalizedPhysicalThreeSubsupportLaw
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine)
    cutoff volume queries

theorem normalizedPhysicalThreeSubsupportPattern_eq
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple)
    (physical : EdgeLabelling) :
    threeBlockPattern
        (normalizedPhysicalThreeSubsupportLaw coupling hcoupling
          cutoff volume queries) physical =
      physicalComponentSubsupportPattern volume queries physical := by
  rfl

theorem normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling cutoff volume queries) pattern ≈
      Q'.divPos
        (parametricKEventNumerator coupling cutoff volume
          (threeBlockPatternEvent
            (normalizedPhysicalThreeSubsupportLaw
              coupling hcoupling cutoff volume queries) pattern))
        (parametricKPhysicalPartition coupling cutoff volume)
        (couplingKPhysicalPartition_pos
          hcoupling cutoff volume) := by
  refine Q'.eqv_trans _
    (finiteEventMass
      (normalizedPhysicalMass coupling hcoupling cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (threeBlockPatternEvent
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling cutoff volume queries) pattern)) _ ?_ ?_
  · exact Q'.eqv_symm
      (finiteEventMass_threeBlockPatternEvent
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling cutoff volume queries) pattern)
  · unfold activityMatchedConfigurationStateSpace
    exact normalizedPhysicalEventMass_eqv_probability
      coupling hcoupling cutoff volume _

theorem componentLabel_subsupportEvent_true
    {volume : Nat} {root query : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers volume)
    (hquery : ∀ face, face ∈ query → face ∈ root) :
    physicalComponentSubsupportEvent volume query
      (componentLabel root) = true := by
  unfold physicalComponentSubsupportEvent
  rw [componentLabelAmbientFamily_eq_singleton hroot]
  apply (familyContainsComponentSubsupportB_true_iff query [root]).2
  exact ⟨root, List.mem_cons_self, hquery⟩

theorem componentLabel_subsupportPattern_111
    {volume : Nat} {root : List Nat}
    (queries : ComponentSubsupportQueryTriple)
    (hroot : root ∈ canonicalSurfacePolymers volume)
    (hleft : ∀ face,
      face ∈ componentSubsupportQueryLeft queries → face ∈ root)
    (hshared : ∀ face,
      face ∈ componentSubsupportQueryShared queries → face ∈ root)
    (hright : ∀ face,
      face ∈ componentSubsupportQueryRight queries → face ∈ root) :
    physicalComponentSubsupportPattern volume queries
        (componentLabel root) =
      (true, true, true) := by
  unfold physicalComponentSubsupportPattern
  rw [componentLabel_subsupportEvent_true hroot hleft,
    componentLabel_subsupportEvent_true hroot hshared,
    componentLabel_subsupportEvent_true hroot hright]

private theorem listQSum_member_le_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_nonnegative
          value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

theorem componentSubsupport111EventNumerator_pos_of_componentLabel
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (hcutoff : 1 ≤ cutoff)
    (queries : ComponentSubsupportQueryTriple) (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers volume)
    (hleft : ∀ face,
      face ∈ componentSubsupportQueryLeft queries → face ∈ root)
    (hshared : ∀ face,
      face ∈ componentSubsupportQueryShared queries → face ∈ root)
    (hright : ∀ face,
      face ∈ componentSubsupportQueryRight queries → face ∈ root)
    (hactivity : (0 : Q') < canonicalSurfaceActivity
      coupling volume root) :
    (0 : Q') < parametricKEventNumerator coupling cutoff volume
      (threeBlockPatternEvent
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling cutoff volume queries)
        (true, true, true)) := by
  let law := normalizedPhysicalThreeSubsupportLaw
    coupling hcoupling cutoff volume queries
  let event := threeBlockPatternEvent law (true, true, true)
  have hpattern : threeBlockPattern law (componentLabel root) =
      (true, true, true) := by
    unfold law
    rw [normalizedPhysicalThreeSubsupportPattern_eq]
    exact componentLabel_subsupportPattern_111
      queries hroot hleft hshared hright
  have hevent : event (componentLabel root) = true := by
    unfold event threeBlockPatternEvent
    exact decide_eq_true hpattern
  have hterm : parametricKEventTerm coupling cutoff volume event
      (componentLabel root) =
        parametricKPhysicalTerm coupling cutoff volume
          (componentLabel root) := by
    unfold parametricKEventTerm
    rw [if_pos hevent]
  have hphysical : componentLabel root ∈
      boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount volume)) :=
    componentLabel_mem_bounded_of_one_le hcutoff
      (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hle : parametricKEventTerm coupling cutoff volume event
        (componentLabel root) ≤
      parametricKEventNumerator coupling cutoff volume event := by
    unfold parametricKEventNumerator
    exact listQSum_member_le_nonnegative
      (parametricKEventTerm coupling cutoff volume event)
      (parametricKEventTerm_nonnegative
        hcoupling cutoff volume event)
      _ hphysical
  rw [hterm] at hle
  exact Q'.pos_of_lt_of_le
    (canonicalRootComponentPhysicalTerm_pos
      hcutoff hroot hactivity) hle

theorem normalizedPhysicalThreeSubsupport_111_mass_pos_of_componentLabel
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (hcutoff : 1 ≤ cutoff)
    (queries : ComponentSubsupportQueryTriple) (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers volume)
    (hleft : ∀ face,
      face ∈ componentSubsupportQueryLeft queries → face ∈ root)
    (hshared : ∀ face,
      face ∈ componentSubsupportQueryShared queries → face ∈ root)
    (hright : ∀ face,
      face ∈ componentSubsupportQueryRight queries → face ∈ root)
    (hactivity : (0 : Q') < canonicalSurfaceActivity
      coupling volume root) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw
        coupling hcoupling cutoff volume queries)
      (true, true, true) := by
  have hnumerator :=
    componentSubsupport111EventNumerator_pos_of_componentLabel
      coupling hcoupling cutoff volume hcutoff queries root hroot
      hleft hshared hright hactivity
  have hratio :=
    normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
      coupling hcoupling cutoff volume queries (true, true, true)
  have hratioPos := Q'.divPos_pos _ _
    (couplingKPhysicalPartition_pos hcoupling cutoff volume)
    hnumerator
  exact Q'.pos_of_lt_of_le hratioPos (Q'.ge_of_eqv hratio)

theorem threeAxisCoarseComponentPattern_111 :
    physicalComponentSubsupportPattern 6
        threeAxisCoarseComponentQueries
        (componentLabel (axisCoarseRoot zeroAxisOffset)) =
      (true, true, true) := by
  apply componentLabel_subsupportPattern_111
    threeAxisCoarseComponentQueries
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
  · exact threeAxisCoarseComponentQueries_subset_zeroRoot.1
  · exact threeAxisCoarseComponentQueries_subset_zeroRoot.2.1
  · exact threeAxisCoarseComponentQueries_subset_zeroRoot.2.2

theorem threeAxisFineComponentPattern_111 :
    physicalComponentSubsupportPattern 6
        threeAxisFineComponentQueries
        (componentLabel (axisFineRoot zeroAxisOffset)) =
      (true, true, true) := by
  apply componentLabel_subsupportPattern_111
    threeAxisFineComponentQueries
    (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
  · exact threeAxisFineComponentQueries_subset_zeroRoot.1
  · exact threeAxisFineComponentQueries_subset_zeroRoot.2.1
  · exact threeAxisFineComponentQueries_subset_zeroRoot.2.2

/-- The replacement coordinates genuinely recover the forbidden exact-root
cell: both the actual fine law and its activity-matched coarse law assign
strictly positive normalized mass to `111`. -/
theorem threeAxisFineCoarseComponentSubsupportPatternMass_111_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    (0 : Q') < threeBlockPatternMass
        (activityMatchedFineThreeSubsupportLaw fineCoupling
          (Q'.le_of_lt hfine) 1 6 threeAxisFineComponentQueries)
        (true, true, true) ∧
      (0 : Q') < threeBlockPatternMass
        (activityMatchedCoarseThreeSubsupportLaw fineCoupling
          (Q'.le_of_lt hfine) 1 6 threeAxisCoarseComponentQueries)
        (true, true, true) := by
  constructor
  · change (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw fineCoupling
        (Q'.le_of_lt hfine) 1 6 threeAxisFineComponentQueries)
      (true, true, true)
    exact normalizedPhysicalThreeSubsupport_111_mass_pos_of_componentLabel
      fineCoupling (Q'.le_of_lt hfine) 1 6 (by omega)
      threeAxisFineComponentQueries (axisFineRoot zeroAxisOffset)
      (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
      threeAxisFineComponentQueries_subset_zeroRoot.1
      threeAxisFineComponentQueries_subset_zeroRoot.2.1
      threeAxisFineComponentQueries_subset_zeroRoot.2.2
      (zeroAxisFineRoot_activity_pos hfine)
  · change (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw
        (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
        1 6 threeAxisCoarseComponentQueries)
      (true, true, true)
    exact normalizedPhysicalThreeSubsupport_111_mass_pos_of_componentLabel
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
      1 6 (by omega)
      threeAxisCoarseComponentQueries (axisCoarseRoot zeroAxisOffset)
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
      threeAxisCoarseComponentQueries_subset_zeroRoot.1
      threeAxisCoarseComponentQueries_subset_zeroRoot.2.1
      threeAxisCoarseComponentQueries_subset_zeroRoot.2.2
      (zeroAxisCoarseRoot_activity_pos
        (unitCubeBlockCoupling_pos hfine))

#print axioms componentContainsSubsupportB_true_iff
#print axioms familyContainsComponentSubsupportB_true_iff
#print axioms familyContainsComponentSubsupportB_singleton
#print axioms physicalComponentSubsupportEvent_true_iff
#print axioms physicalComponentSingletonEvent_true_iff_excited
#print axioms axisCoarseFaceQuerySupport_subset_root
#print axioms axisFineFaceQuerySupport_subset_root
#print axioms axisCoarseFaceQuerySupport_nonempty
#print axioms axisFineFaceQuerySupport_nonempty
#print axioms coarseXAxisLeftFace_eq_zeroRightFace
#print axioms coarseYAxisFrontFace_eq_zeroBackFace
#print axioms coarseXAxisLeftQuery_eq_zeroRightQuery
#print axioms coarseYAxisFrontQuery_eq_zeroBackQuery
#print axioms fineXAxisLeftQuery_eq_zeroRightQuery
#print axioms fineYAxisFrontQuery_eq_zeroBackQuery
#print axioms threeAxisCoarseLeftQuery
#print axioms threeAxisCoarseSharedQuery
#print axioms threeAxisCoarseRightQuery
#print axioms threeAxisFineLeftQuery
#print axioms threeAxisFineSharedQuery
#print axioms threeAxisFineRightQuery
#print axioms threeAxisCoarseLeftQuery_is_xInterface
#print axioms threeAxisCoarseSharedQuery_is_yInterface
#print axioms threeAxisFineLeftQuery_is_xInterface
#print axioms threeAxisFineSharedQuery_is_yInterface
#print axioms threeAxisCoarseComponentQueries_subset_zeroRoot
#print axioms threeAxisFineComponentQueries_subset_zeroRoot
#print axioms threeAxisCoarseComponentQueries_nonempty
#print axioms threeAxisFineComponentQueries_nonempty
#print axioms normalizedPhysicalThreeSubsupportLaw
#print axioms activityMatchedFineThreeSubsupportLaw
#print axioms activityMatchedCoarseThreeSubsupportLaw
#print axioms normalizedPhysicalThreeSubsupportPattern_eq
#print axioms normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
#print axioms componentLabel_subsupportEvent_true
#print axioms componentLabel_subsupportPattern_111
#print axioms componentSubsupport111EventNumerator_pos_of_componentLabel
#print axioms normalizedPhysicalThreeSubsupport_111_mass_pos_of_componentLabel
#print axioms threeAxisCoarseComponentPattern_111
#print axioms threeAxisFineComponentPattern_111
#print axioms threeAxisFineCoarseComponentSubsupportPatternMass_111_pos

end YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
