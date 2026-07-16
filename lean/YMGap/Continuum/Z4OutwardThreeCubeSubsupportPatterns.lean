/-
# Exact coarse truth table for the outward three-cube carriers

The face-disjoint outward carriers retain three independent central interface
faces: the zero-cube right, back, and top faces.  The +x, +y, and +z cube
boundaries contain exactly those respective faces.  This module turns the
geometric membership matrix into seven literal nonzero Boolean patterns on
canonical component labels.
-/

import YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier

namespace YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel

/-! ## 1. The three independent interface queries -/

def outwardXQuery : List Nat :=
  axisCoarseFaceQuerySupport zeroAxisOffset .rightYZ

def outwardYQuery : List Nat :=
  axisCoarseFaceQuerySupport zeroAxisOffset .backXZ

def outwardZQuery : List Nat :=
  axisCoarseFaceQuerySupport zeroAxisOffset .topXY

def outwardCoarseQueries : ComponentSubsupportQueryTriple :=
  (outwardXQuery, outwardYQuery, outwardZQuery)

def outwardXQueryFace : Z4Plaq :=
  axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ)

def outwardYQueryFace : Z4Plaq :=
  axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ)

def outwardZQueryFace : Z4Plaq :=
  axisShiftPlaquette zeroAxisOffset (cubeFace .topXY)

theorem coarseZAxisBottomFace_eq_zeroTopFace :
    axisShiftPlaquette zAxisOffset (cubeFace .bottomXY) =
      axisShiftPlaquette zeroAxisOffset (cubeFace .topXY) := by
  simp [axisShiftPlaquette, axisShiftVertex, zAxisOffset,
    zeroAxisOffset, cubeFace]

/-! ## 2. Query inclusion and exclusion through geometric encoding -/

theorem coarseFaceQuerySupport_subset_geometricRoot
    (offset : AxisOffset) (face : CubeFaceIndex)
    (support : List Z4Plaq)
    (hface : axisShiftPlaquette offset (cubeFace face) ∈ support) :
    ∀ id, id ∈ axisCoarseFaceQuerySupport offset face →
      id ∈ geometricSupportIds 6 support := by
  intro id hid
  have hparts := (mem_geometricSupportIds_iff 6
    [axisShiftPlaquette offset (cubeFace face)] id).1 hid
  apply (mem_geometricSupportIds_iff 6 support id).2
  refine ⟨hparts.1, ?_⟩
  have heq : boxPlaquetteAt 6 id =
      axisShiftPlaquette offset (cubeFace face) := by
    simpa only [List.mem_singleton] using hparts.2
  simpa only [heq] using hface

theorem coarseFaceQuerySupport_not_subset_geometricRoot
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset)
    (face : CubeFaceIndex) (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : axisShiftPlaquette offset (cubeFace face) ∉ support) :
    ¬ (∀ id, id ∈ axisCoarseFaceQuerySupport offset face →
      id ∈ geometricSupportIds 6 support) := by
  intro hsubset
  obtain ⟨id, hid⟩ :=
    axisCoarseFaceQuerySupport_nonempty offset hoffset face
  have hparts := (mem_geometricSupportIds_iff 6
    [axisShiftPlaquette offset (cubeFace face)] id).1 hid
  have hidRoot := hsubset id hid
  have hdecoded : boxPlaquetteAt 6 id ∈
      geometricPolymer 6 (geometricSupportIds 6 support) :=
    List.mem_map.mpr ⟨id, hidRoot, rfl⟩
  have hmem := (geometricSupportIds_sameSupport hbox).1 _ hdecoded
  have heq : boxPlaquetteAt 6 id =
      axisShiftPlaquette offset (cubeFace face) := by
    simpa only [List.mem_singleton] using hparts.2
  exact hface (heq ▸ hmem)

/-! The literal matrix is deliberately checked on the six/12/18-face lists,
not inferred from a diagram. -/

theorem outwardQueryFace_membership_matrix :
    outwardXQueryFace ∈ outwardXSurface ∧
    outwardXQueryFace ∉ outwardYSurface ∧
    outwardXQueryFace ∉ outwardZSurface ∧
    outwardYQueryFace ∉ outwardXSurface ∧
    outwardYQueryFace ∈ outwardYSurface ∧
    outwardYQueryFace ∉ outwardZSurface ∧
    outwardZQueryFace ∉ outwardXSurface ∧
    outwardZQueryFace ∉ outwardYSurface ∧
    outwardZQueryFace ∈ outwardZSurface := by
  simp [outwardXQueryFace, outwardYQueryFace, outwardZQueryFace,
    outwardXSurface, outwardYSurface, outwardZSurface, axisCubeSurface,
    unitCubeSurface, axisShiftPlaquette, axisShiftVertex, zeroAxisOffset,
    xAxisOffset, yAxisOffset, zAxisOffset, cubeFace]

theorem outwardXQueryFace_mem_X :
    outwardXQueryFace ∈ outwardXSurface :=
  outwardQueryFace_membership_matrix.1

theorem outwardXQueryFace_not_mem_Y :
    outwardXQueryFace ∉ outwardYSurface :=
  outwardQueryFace_membership_matrix.2.1

theorem outwardXQueryFace_not_mem_Z :
    outwardXQueryFace ∉ outwardZSurface :=
  outwardQueryFace_membership_matrix.2.2.1

theorem outwardYQueryFace_not_mem_X :
    outwardYQueryFace ∉ outwardXSurface :=
  outwardQueryFace_membership_matrix.2.2.2.1

theorem outwardYQueryFace_mem_Y :
    outwardYQueryFace ∈ outwardYSurface :=
  outwardQueryFace_membership_matrix.2.2.2.2.1

theorem outwardYQueryFace_not_mem_Z :
    outwardYQueryFace ∉ outwardZSurface :=
  outwardQueryFace_membership_matrix.2.2.2.2.2.1

theorem outwardZQueryFace_not_mem_X :
    outwardZQueryFace ∉ outwardXSurface :=
  outwardQueryFace_membership_matrix.2.2.2.2.2.2.1

theorem outwardZQueryFace_not_mem_Y :
    outwardZQueryFace ∉ outwardYSurface :=
  outwardQueryFace_membership_matrix.2.2.2.2.2.2.2.1

theorem outwardZQueryFace_mem_Z :
    outwardZQueryFace ∈ outwardZSurface :=
  outwardQueryFace_membership_matrix.2.2.2.2.2.2.2.2

/-! ## 3. Canonical singleton-family decoder, including false coordinates -/

theorem componentLabel_subsupportEvent_eq_componentContains
    {volume : Nat} {root query : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers volume) :
    physicalComponentSubsupportEvent volume query (componentLabel root) =
      componentContainsSubsupportB query root := by
  unfold physicalComponentSubsupportEvent
    familyContainsComponentSubsupportB
  rw [componentLabelAmbientFamily_eq_singleton hroot]
  simp

theorem componentLabel_subsupportEvent_false
    {volume : Nat} {root query : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers volume)
    (hnot : ¬ (∀ face, face ∈ query → face ∈ root)) :
    physicalComponentSubsupportEvent volume query
        (componentLabel root) = false := by
  rw [componentLabel_subsupportEvent_eq_componentContains hroot]
  cases hevent : componentContainsSubsupportB query root with
  | false => rfl
  | true =>
      exact absurd
        ((componentContainsSubsupportB_true_iff query root).1 hevent)
        hnot

/-! ## 4. Seven exact nonzero patterns -/

private theorem xQuery_subset
    (support : List Z4Plaq) (hface : outwardXQueryFace ∈ support) :
    ∀ id, id ∈ outwardXQuery → id ∈ geometricSupportIds 6 support := by
  exact coarseFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .rightYZ support hface

private theorem yQuery_subset
    (support : List Z4Plaq) (hface : outwardYQueryFace ∈ support) :
    ∀ id, id ∈ outwardYQuery → id ∈ geometricSupportIds 6 support := by
  exact coarseFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .backXZ support hface

private theorem zQuery_subset
    (support : List Z4Plaq) (hface : outwardZQueryFace ∈ support) :
    ∀ id, id ∈ outwardZQuery → id ∈ geometricSupportIds 6 support := by
  exact coarseFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .topXY support hface

private theorem xQuery_not_subset
    (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardXQueryFace ∉ support) :
    ¬ (∀ id, id ∈ outwardXQuery →
      id ∈ geometricSupportIds 6 support) := by
  exact coarseFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .rightYZ support hbox hface

private theorem yQuery_not_subset
    (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardYQueryFace ∉ support) :
    ¬ (∀ id, id ∈ outwardYQuery →
      id ∈ geometricSupportIds 6 support) := by
  exact coarseFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .backXZ support hbox hface

private theorem zQuery_not_subset
    (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardZQueryFace ∉ support) :
    ¬ (∀ id, id ∈ outwardZQuery →
      id ∈ geometricSupportIds 6 support) := by
  exact coarseFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .topXY support hbox hface

theorem outwardXRoot_pattern_100 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXRoot) = (true, false, false) := by
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true outwardXRoot_mem_canonical
      (xQuery_subset outwardXSurface
        outwardXQueryFace_mem_X),
    componentLabel_subsupportEvent_false outwardXRoot_mem_canonical
      (yQuery_not_subset outwardXSurface outwardXSurface_subset_box_six
        outwardYQueryFace_not_mem_X),
    componentLabel_subsupportEvent_false outwardXRoot_mem_canonical
      (zQuery_not_subset outwardXSurface outwardXSurface_subset_box_six
        outwardZQueryFace_not_mem_X)]

theorem outwardYRoot_pattern_010 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardYRoot) = (false, true, false) := by
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_false outwardYRoot_mem_canonical
      (xQuery_not_subset outwardYSurface outwardYSurface_subset_box_six
        outwardXQueryFace_not_mem_Y),
    componentLabel_subsupportEvent_true outwardYRoot_mem_canonical
      (yQuery_subset outwardYSurface
        outwardYQueryFace_mem_Y),
    componentLabel_subsupportEvent_false outwardYRoot_mem_canonical
      (zQuery_not_subset outwardYSurface outwardYSurface_subset_box_six
        outwardZQueryFace_not_mem_Y)]

theorem outwardZRoot_pattern_001 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardZRoot) = (false, false, true) := by
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_false outwardZRoot_mem_canonical
      (xQuery_not_subset outwardZSurface outwardZSurface_subset_box_six
        outwardXQueryFace_not_mem_Z),
    componentLabel_subsupportEvent_false outwardZRoot_mem_canonical
      (yQuery_not_subset outwardZSurface outwardZSurface_subset_box_six
        outwardYQueryFace_not_mem_Z),
    componentLabel_subsupportEvent_true outwardZRoot_mem_canonical
      (zQuery_subset outwardZSurface
        outwardZQueryFace_mem_Z)]

theorem outwardXQueryFace_mem_XY :
    outwardXQueryFace ∈ outwardXYSurface := by
  exact List.mem_append.mpr (Or.inl outwardXQueryFace_mem_X)

theorem outwardYQueryFace_mem_XY :
    outwardYQueryFace ∈ outwardXYSurface := by
  exact List.mem_append.mpr (Or.inr outwardYQueryFace_mem_Y)

theorem outwardZQueryFace_not_mem_XY :
    outwardZQueryFace ∉ outwardXYSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hx | hy
  · exact outwardZQueryFace_not_mem_X hx
  · exact outwardZQueryFace_not_mem_Y hy

theorem outwardXQueryFace_mem_XZ :
    outwardXQueryFace ∈ outwardXZSurface := by
  exact List.mem_append.mpr (Or.inl outwardXQueryFace_mem_X)

theorem outwardYQueryFace_not_mem_XZ :
    outwardYQueryFace ∉ outwardXZSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hx | hz
  · exact outwardYQueryFace_not_mem_X hx
  · exact outwardYQueryFace_not_mem_Z hz

theorem outwardZQueryFace_mem_XZ :
    outwardZQueryFace ∈ outwardXZSurface := by
  exact List.mem_append.mpr (Or.inr outwardZQueryFace_mem_Z)

theorem outwardXQueryFace_not_mem_YZ :
    outwardXQueryFace ∉ outwardYZSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hy | hz
  · exact outwardXQueryFace_not_mem_Y hy
  · exact outwardXQueryFace_not_mem_Z hz

theorem outwardYQueryFace_mem_YZ :
    outwardYQueryFace ∈ outwardYZSurface := by
  exact List.mem_append.mpr (Or.inl outwardYQueryFace_mem_Y)

theorem outwardZQueryFace_mem_YZ :
    outwardZQueryFace ∈ outwardYZSurface := by
  exact List.mem_append.mpr (Or.inr outwardZQueryFace_mem_Z)

theorem outwardXQueryFace_mem_XYZ :
    outwardXQueryFace ∈ outwardXYZSurface := by
  exact List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inl outwardXQueryFace_mem_X)))

theorem outwardYQueryFace_mem_XYZ :
    outwardYQueryFace ∈ outwardXYZSurface := by
  exact List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inr outwardYQueryFace_mem_Y)))

theorem outwardZQueryFace_mem_XYZ :
    outwardZQueryFace ∈ outwardXYZSurface := by
  exact List.mem_append.mpr (Or.inr outwardZQueryFace_mem_Z)

theorem outwardXYRoot_pattern_110 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXYRoot) = (true, true, false) := by
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true outwardXYRoot_mem_canonical
      (xQuery_subset outwardXYSurface outwardXQueryFace_mem_XY),
    componentLabel_subsupportEvent_true outwardXYRoot_mem_canonical
      (yQuery_subset outwardXYSurface outwardYQueryFace_mem_XY),
    componentLabel_subsupportEvent_false outwardXYRoot_mem_canonical
      (zQuery_not_subset outwardXYSurface outwardXYSurface_subset_box_six
        outwardZQueryFace_not_mem_XY)]

theorem outwardXZRoot_pattern_101 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXZRoot) = (true, false, true) := by
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true outwardXZRoot_mem_canonical
      (xQuery_subset outwardXZSurface outwardXQueryFace_mem_XZ),
    componentLabel_subsupportEvent_false outwardXZRoot_mem_canonical
      (yQuery_not_subset outwardXZSurface outwardXZSurface_subset_box_six
        outwardYQueryFace_not_mem_XZ),
    componentLabel_subsupportEvent_true outwardXZRoot_mem_canonical
      (zQuery_subset outwardXZSurface outwardZQueryFace_mem_XZ)]

theorem outwardYZRoot_pattern_011 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardYZRoot) = (false, true, true) := by
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_false outwardYZRoot_mem_canonical
      (xQuery_not_subset outwardYZSurface outwardYZSurface_subset_box_six
        outwardXQueryFace_not_mem_YZ),
    componentLabel_subsupportEvent_true outwardYZRoot_mem_canonical
      (yQuery_subset outwardYZSurface outwardYQueryFace_mem_YZ),
    componentLabel_subsupportEvent_true outwardYZRoot_mem_canonical
      (zQuery_subset outwardYZSurface outwardZQueryFace_mem_YZ)]

theorem outwardXYZRoot_pattern_111 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXYZRoot) = (true, true, true) := by
  unfold physicalComponentSubsupportPattern outwardCoarseQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true outwardXYZRoot_mem_canonical
      (xQuery_subset outwardXYZSurface outwardXQueryFace_mem_XYZ),
    componentLabel_subsupportEvent_true outwardXYZRoot_mem_canonical
      (yQuery_subset outwardXYZSurface outwardYQueryFace_mem_XYZ),
    componentLabel_subsupportEvent_true outwardXYZRoot_mem_canonical
      (zQuery_subset outwardXYZSurface outwardZQueryFace_mem_XYZ)]

/-- Every nonzero Boolean cell has a concrete canonical component-label
witness. -/
theorem outwardNonzeroPattern_witnesses :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXRoot) = (true, false, false) ∧
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardYRoot) = (false, true, false) ∧
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardZRoot) = (false, false, true) ∧
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXYRoot) = (true, true, false) ∧
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXZRoot) = (true, false, true) ∧
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardYZRoot) = (false, true, true) ∧
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel outwardXYZRoot) = (true, true, true) :=
  ⟨outwardXRoot_pattern_100, outwardYRoot_pattern_010,
    outwardZRoot_pattern_001, outwardXYRoot_pattern_110,
    outwardXZRoot_pattern_101, outwardYZRoot_pattern_011,
    outwardXYZRoot_pattern_111⟩

/-! ## 5. A pattern-generic positive-mass witness theorem -/

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

theorem componentSubsupportPatternEventNumerator_pos_of_physical
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount volume)))
    (hpattern : physicalComponentSubsupportPattern volume queries physical =
      pattern)
    (hterm : (0 : Q') <
      parametricKPhysicalTerm coupling cutoff volume physical) :
    (0 : Q') < parametricKEventNumerator coupling cutoff volume
      (threeBlockPatternEvent
        (normalizedPhysicalThreeSubsupportLaw
          coupling hcoupling cutoff volume queries) pattern) := by
  let law := normalizedPhysicalThreeSubsupportLaw
    coupling hcoupling cutoff volume queries
  let event := threeBlockPatternEvent law pattern
  have hlawPattern : threeBlockPattern law physical = pattern := by
    unfold law
    rw [normalizedPhysicalThreeSubsupportPattern_eq]
    exact hpattern
  have hevent : event physical = true := by
    unfold event threeBlockPatternEvent
    exact decide_eq_true hlawPattern
  have htermEq : parametricKEventTerm coupling cutoff volume event physical =
      parametricKPhysicalTerm coupling cutoff volume physical := by
    unfold parametricKEventTerm
    rw [if_pos hevent]
  have hle : parametricKEventTerm coupling cutoff volume event physical ≤
      parametricKEventNumerator coupling cutoff volume event := by
    unfold parametricKEventNumerator
    exact listQSum_member_le_nonnegative
      (parametricKEventTerm coupling cutoff volume event)
      (parametricKEventTerm_nonnegative
        hcoupling cutoff volume event)
      _ hphysical
  rw [htermEq] at hle
  exact Q'.pos_of_lt_of_le hterm hle

theorem normalizedPhysicalThreeSubsupport_patternMass_pos_of_physical
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount volume)))
    (hpattern : physicalComponentSubsupportPattern volume queries physical =
      pattern)
    (hterm : (0 : Q') <
      parametricKPhysicalTerm coupling cutoff volume physical) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw
        coupling hcoupling cutoff volume queries) pattern := by
  have hnumerator :=
    componentSubsupportPatternEventNumerator_pos_of_physical
      coupling hcoupling cutoff volume queries pattern physical
      hphysical hpattern hterm
  have hratio :=
    normalizedPhysicalThreeSubsupportPatternMass_eqv_character_ratio
      coupling hcoupling cutoff volume queries pattern
  have hratioPos := Q'.divPos_pos _ _
    (couplingKPhysicalPartition_pos hcoupling cutoff volume)
    hnumerator
  exact Q'.pos_of_lt_of_le hratioPos (Q'.ge_of_eqv hratio)

theorem normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (hcutoff : 1 ≤ cutoff)
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) (root : List Nat)
    (hroot : root ∈ canonicalSurfacePolymers volume)
    (hpattern : physicalComponentSubsupportPattern volume queries
      (componentLabel root) = pattern)
    (hactivity : (0 : Q') < canonicalSurfaceActivity
      coupling volume root) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw
        coupling hcoupling cutoff volume queries) pattern := by
  apply normalizedPhysicalThreeSubsupport_patternMass_pos_of_physical
    coupling hcoupling cutoff volume queries pattern (componentLabel root)
  · exact componentLabel_mem_bounded_of_one_le hcutoff
      (canonicalSurfacePolymer_mem_faceSupports hroot)
  · exact hpattern
  · exact canonicalRootComponentPhysicalTerm_pos
      hcutoff hroot hactivity

/-! ## 6. Positive normalized mass for the seven nonzero cells -/

theorem outwardNonzeroPatternMasses_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, false, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (false, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (false, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (false, true, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, true, true) := by
  exact ⟨
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardCoarseQueries (true, false, false) outwardXRoot
      outwardXRoot_mem_canonical outwardXRoot_pattern_100
      (outwardXRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardCoarseQueries (false, true, false) outwardYRoot
      outwardYRoot_mem_canonical outwardYRoot_pattern_010
      (outwardYRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardCoarseQueries (false, false, true) outwardZRoot
      outwardZRoot_mem_canonical outwardZRoot_pattern_001
      (outwardZRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardCoarseQueries (true, true, false) outwardXYRoot
      outwardXYRoot_mem_canonical outwardXYRoot_pattern_110
      (outwardXYRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardCoarseQueries (true, false, true) outwardXZRoot
      outwardXZRoot_mem_canonical outwardXZRoot_pattern_101
      (outwardXZRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardCoarseQueries (false, true, true) outwardYZRoot
      outwardYZRoot_mem_canonical outwardYZRoot_pattern_011
      (outwardYZRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardCoarseQueries (true, true, true) outwardXYZRoot
      outwardXYZRoot_mem_canonical outwardXYZRoot_pattern_111
      (outwardXYZRoot_activity_pos hcoupling)⟩

/-! ## 7. The vacuum cell and all-eight coarse positivity -/

private theorem excitedPlaquetteIds_zero_local (volume : Nat) :
    excitedPlaquetteIds volume zeroEdgeLabelling = [] := by
  unfold excitedPlaquetteIds physicalFaceEdges
  have general : ∀ edges : List Nat,
      edges.filter (fun edge => decide (1 ≤ zeroEdgeLabelling edge)) = [] := by
    intro edges
    induction edges with
    | nil => rfl
    | cons head tail ih =>
        rw [List.filter_cons]
        have hfalse : decide (1 ≤ zeroEdgeLabelling head) = false := by rfl
        rw [hfalse]
        exact ih
  exact general _

theorem physicalCanonicalAmbientFamily_zero_local (volume : Nat) :
    physicalCanonicalAmbientFamily volume zeroEdgeLabelling = [] := by
  unfold physicalCanonicalAmbientFamily canonicalSurfaceFamily
  rw [excitedPlaquetteIds_zero_local]
  have hlabel : componentLabel [] = zeroEdgeLabelling := by
    funext edge
    rfl
  rw [hlabel]
  unfold surfaceComponents
  rw [excitedPlaquetteIds_zero_local]
  change ambientOrderedFamily volume [] = []
  unfold ambientOrderedFamily
  generalize canonicalSurfacePolymers volume = polymers
  induction polymers with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filter_cons]
      have hfalse : decide (head ∈ ([] : List (List Nat))) = false := by rfl
      rw [hfalse]
      exact ih

theorem outwardVacuum_pattern_000 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        zeroEdgeLabelling = (false, false, false) := by
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent
    familyContainsComponentSubsupportB
  rw [physicalCanonicalAmbientFamily_zero_local]
  rfl

theorem outwardVacuumPatternMass_pos
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling hcoupling
        1 6 outwardCoarseQueries) (false, false, false) := by
  apply normalizedPhysicalThreeSubsupport_patternMass_pos_of_physical
    coupling hcoupling 1 6 outwardCoarseQueries
    (false, false, false) zeroEdgeLabelling
  · exact zeroEdgeLabelling_mem_bounded 1 6
  · exact outwardVacuum_pattern_000
  · have heq := parametricKPhysicalTerm_zero_eqv_one coupling 1 6
    exact Q'.pos_of_lt_of_le
      (show (0 : Q') < (1 : Q') by decide)
      (Q'.le_of_eqv (Q'.eqv_symm heq))

/-- At every strictly positive derived coupling, all eight Boolean cells of
the outward component-sub-support law have strictly positive normalized
mass.  Each nonzero cell is supplied by an exact closed surface, while `000`
is supplied by the exact vacuum term. -/
theorem outwardAllEightPatternMasses_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (false, false, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, false, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (false, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (false, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (false, true, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries)
      (true, true, true) := by
  exact ⟨outwardVacuumPatternMass_pos coupling (Q'.le_of_lt hcoupling),
    outwardNonzeroPatternMasses_pos coupling hcoupling⟩

#print axioms coarseZAxisBottomFace_eq_zeroTopFace
#print axioms coarseFaceQuerySupport_subset_geometricRoot
#print axioms coarseFaceQuerySupport_not_subset_geometricRoot
#print axioms outwardQueryFace_membership_matrix
#print axioms componentLabel_subsupportEvent_eq_componentContains
#print axioms componentLabel_subsupportEvent_false
#print axioms outwardXRoot_pattern_100
#print axioms outwardYRoot_pattern_010
#print axioms outwardZRoot_pattern_001
#print axioms outwardXYRoot_pattern_110
#print axioms outwardXZRoot_pattern_101
#print axioms outwardYZRoot_pattern_011
#print axioms outwardXYZRoot_pattern_111
#print axioms outwardNonzeroPattern_witnesses
#print axioms componentSubsupportPatternEventNumerator_pos_of_physical
#print axioms normalizedPhysicalThreeSubsupport_patternMass_pos_of_physical
#print axioms normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
#print axioms outwardNonzeroPatternMasses_pos
#print axioms physicalCanonicalAmbientFamily_zero_local
#print axioms outwardVacuum_pattern_000
#print axioms outwardVacuumPatternMass_pos
#print axioms outwardAllEightPatternMasses_pos

end YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
