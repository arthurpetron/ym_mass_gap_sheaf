/-
# Exact fine truth table for the outward three-cube carriers

The three exterior coarse queries each have a distinguished dyadic child.
This module checks their complete membership matrix on the seven refined
outward carriers and derives positive normalized mass for all eight fine
Boolean patterns from exact canonical activities.
-/

import YMGap.Continuum.Z4OutwardThreeCubeFineCarrier
import YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns

namespace YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardThreeCubeFineCarrier
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

/-! ## 1. Three distinguished dyadic exterior queries -/

/- The literal geometric lists are large enough that repeatedly projecting a
transparent triple makes the elaborator normalize the whole finite box.  The
opaque certificates expose the exact geometric identities once while keeping
subsequent triple projections constant-size. -/
structure FineFaceQueryCertificate (geometric : List Nat) where
  support : List Nat
  support_eq_geometric : support = geometric

opaque outwardXFineQueryCertificate : FineFaceQueryCertificate
    (axisFineFaceQuerySupport zeroAxisOffset .rightYZ .origin) := {
  support := axisFineFaceQuerySupport zeroAxisOffset .rightYZ .origin
  support_eq_geometric := rfl
}

opaque outwardYFineQueryCertificate : FineFaceQueryCertificate
    (axisFineFaceQuerySupport zeroAxisOffset .backXZ .origin) := {
  support := axisFineFaceQuerySupport zeroAxisOffset .backXZ .origin
  support_eq_geometric := rfl
}

opaque outwardZFineQueryCertificate : FineFaceQueryCertificate
    (axisFineFaceQuerySupport zeroAxisOffset .topXY .origin) := {
  support := axisFineFaceQuerySupport zeroAxisOffset .topXY .origin
  support_eq_geometric := rfl
}

def outwardXFineQuery : List Nat := outwardXFineQueryCertificate.support

def outwardYFineQuery : List Nat := outwardYFineQueryCertificate.support

def outwardZFineQuery : List Nat := outwardZFineQueryCertificate.support

theorem outwardXFineQuery_eq_geometric : outwardXFineQuery =
    axisFineFaceQuerySupport zeroAxisOffset .rightYZ .origin :=
  outwardXFineQueryCertificate.support_eq_geometric

theorem outwardYFineQuery_eq_geometric : outwardYFineQuery =
    axisFineFaceQuerySupport zeroAxisOffset .backXZ .origin :=
  outwardYFineQueryCertificate.support_eq_geometric

theorem outwardZFineQuery_eq_geometric : outwardZFineQuery =
    axisFineFaceQuerySupport zeroAxisOffset .topXY .origin :=
  outwardZFineQueryCertificate.support_eq_geometric

def outwardFineQueries : ComponentSubsupportQueryTriple :=
  (outwardXFineQuery, outwardYFineQuery, outwardZFineQuery)

theorem outwardFineQueries_left :
    componentSubsupportQueryLeft outwardFineQueries = outwardXFineQuery := rfl

theorem outwardFineQueries_shared :
    componentSubsupportQueryShared outwardFineQueries = outwardYFineQuery := rfl

theorem outwardFineQueries_right :
    componentSubsupportQueryRight outwardFineQueries = outwardZFineQuery := rfl

def outwardXFineQueryFace : Z4Plaq :=
  dyadicCell
    (axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ)) .origin

def outwardYFineQueryFace : Z4Plaq :=
  dyadicCell
    (axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ)) .origin

def outwardZFineQueryFace : Z4Plaq :=
  dyadicCell
    (axisShiftPlaquette zeroAxisOffset (cubeFace .topXY)) .origin

/-! ## 2. Query inclusion and exclusion through geometric encoding -/

theorem fineFaceQuerySupport_subset_geometricRoot
    (offset : AxisOffset) (face : CubeFaceIndex)
    (index : DyadicCellIndex) (support : List Z4Plaq)
    (hface : dyadicCell
      (axisShiftPlaquette offset (cubeFace face)) index ∈ support) :
    ∀ id, id ∈ axisFineFaceQuerySupport offset face index →
      id ∈ geometricSupportIds 6 support := by
  intro id hid
  have hparts := (mem_geometricSupportIds_iff 6
    [dyadicCell (axisShiftPlaquette offset (cubeFace face)) index] id).1 hid
  apply (mem_geometricSupportIds_iff 6 support id).2
  refine ⟨hparts.1, ?_⟩
  have heq : boxPlaquetteAt 6 id =
      dyadicCell (axisShiftPlaquette offset (cubeFace face)) index := by
    simpa only [List.mem_singleton] using hparts.2
  simpa only [heq] using hface

theorem fineFaceQuerySupport_not_subset_geometricRoot
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset)
    (face : CubeFaceIndex) (index : DyadicCellIndex)
    (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : dyadicCell
      (axisShiftPlaquette offset (cubeFace face)) index ∉ support) :
    ¬ (∀ id, id ∈ axisFineFaceQuerySupport offset face index →
      id ∈ geometricSupportIds 6 support) := by
  intro hsubset
  obtain ⟨id, hid⟩ :=
    axisFineFaceQuerySupport_nonempty offset hoffset face index
  have hparts := (mem_geometricSupportIds_iff 6
    [dyadicCell (axisShiftPlaquette offset (cubeFace face)) index] id).1 hid
  have hidRoot := hsubset id hid
  have hdecoded : boxPlaquetteAt 6 id ∈
      geometricPolymer 6 (geometricSupportIds 6 support) :=
    List.mem_map.mpr ⟨id, hidRoot, rfl⟩
  have hmem := (geometricSupportIds_sameSupport hbox).1 _ hdecoded
  have heq : boxPlaquetteAt 6 id =
      dyadicCell (axisShiftPlaquette offset (cubeFace face)) index := by
    simpa only [List.mem_singleton] using hparts.2
  exact hface (heq ▸ hmem)

/-! The full matrix is kernel-computed on the literal 24/48/72-face lists. -/

theorem outwardFineQueryFace_membership_matrix :
    outwardXFineQueryFace ∈ outwardXFineSurface ∧
    outwardXFineQueryFace ∉ outwardYFineSurface ∧
    outwardXFineQueryFace ∉ outwardZFineSurface ∧
    outwardYFineQueryFace ∉ outwardXFineSurface ∧
    outwardYFineQueryFace ∈ outwardYFineSurface ∧
    outwardYFineQueryFace ∉ outwardZFineSurface ∧
    outwardZFineQueryFace ∉ outwardXFineSurface ∧
    outwardZFineQueryFace ∉ outwardYFineSurface ∧
    outwardZFineQueryFace ∈ outwardZFineSurface := by
  simp [outwardXFineQueryFace, outwardYFineQueryFace,
    outwardZFineQueryFace, outwardXFineSurface, outwardYFineSurface,
    outwardZFineSurface, axisFineCubeSurface, axisCubeSurface,
    dyadicSupportCells, dyadicPlaquetteCells, dyadicCellIndices,
    unitCubeSurface, axisShiftPlaquette, axisShiftVertex, zeroAxisOffset,
    xAxisOffset, yAxisOffset, zAxisOffset, cubeFace, dyadicCell,
    dyadicVertex, dirsOf, addE]

theorem outwardXFineQueryFace_mem_X :
    outwardXFineQueryFace ∈ outwardXFineSurface :=
  outwardFineQueryFace_membership_matrix.1

theorem outwardXFineQueryFace_not_mem_Y :
    outwardXFineQueryFace ∉ outwardYFineSurface :=
  outwardFineQueryFace_membership_matrix.2.1

theorem outwardXFineQueryFace_not_mem_Z :
    outwardXFineQueryFace ∉ outwardZFineSurface :=
  outwardFineQueryFace_membership_matrix.2.2.1

theorem outwardYFineQueryFace_not_mem_X :
    outwardYFineQueryFace ∉ outwardXFineSurface :=
  outwardFineQueryFace_membership_matrix.2.2.2.1

theorem outwardYFineQueryFace_mem_Y :
    outwardYFineQueryFace ∈ outwardYFineSurface :=
  outwardFineQueryFace_membership_matrix.2.2.2.2.1

theorem outwardYFineQueryFace_not_mem_Z :
    outwardYFineQueryFace ∉ outwardZFineSurface :=
  outwardFineQueryFace_membership_matrix.2.2.2.2.2.1

theorem outwardZFineQueryFace_not_mem_X :
    outwardZFineQueryFace ∉ outwardXFineSurface :=
  outwardFineQueryFace_membership_matrix.2.2.2.2.2.2.1

theorem outwardZFineQueryFace_not_mem_Y :
    outwardZFineQueryFace ∉ outwardYFineSurface :=
  outwardFineQueryFace_membership_matrix.2.2.2.2.2.2.2.1

theorem outwardZFineQueryFace_mem_Z :
    outwardZFineQueryFace ∈ outwardZFineSurface :=
  outwardFineQueryFace_membership_matrix.2.2.2.2.2.2.2.2

/-! ## 3. Seven exact nonzero fine patterns -/

theorem physicalComponentSubsupportPattern_eq_of_events
    {volume : Nat} {queries : ComponentSubsupportQueryTriple}
    {physical : EdgeLabelling} {left shared right : Bool}
    (hleft : physicalComponentSubsupportEvent volume
      (componentSubsupportQueryLeft queries) physical = left)
    (hshared : physicalComponentSubsupportEvent volume
      (componentSubsupportQueryShared queries) physical = shared)
    (hright : physicalComponentSubsupportEvent volume
      (componentSubsupportQueryRight queries) physical = right) :
    physicalComponentSubsupportPattern volume queries physical =
      (left, shared, right) := by
  unfold physicalComponentSubsupportPattern
  rw [hleft, hshared, hright]

theorem outwardFinePattern_eq_of_events
    {physical : EdgeLabelling} {left shared right : Bool}
    (hleft : physicalComponentSubsupportEvent 6
      outwardXFineQuery physical = left)
    (hshared : physicalComponentSubsupportEvent 6
      outwardYFineQuery physical = shared)
    (hright : physicalComponentSubsupportEvent 6
      outwardZFineQuery physical = right) :
    physicalComponentSubsupportPattern 6 outwardFineQueries physical =
      (left, shared, right) := by
  unfold physicalComponentSubsupportPattern
  rw [outwardFineQueries_left, outwardFineQueries_shared,
    outwardFineQueries_right, hleft, hshared, hright]

private theorem xFineQuery_subset
    (support : List Z4Plaq)
    (hface : outwardXFineQueryFace ∈ support) :
    ∀ id, id ∈ outwardXFineQuery →
      id ∈ geometricSupportIds 6 support := by
  rw [outwardXFineQuery_eq_geometric]
  exact fineFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .rightYZ .origin support hface

private theorem yFineQuery_subset
    (support : List Z4Plaq)
    (hface : outwardYFineQueryFace ∈ support) :
    ∀ id, id ∈ outwardYFineQuery →
      id ∈ geometricSupportIds 6 support := by
  rw [outwardYFineQuery_eq_geometric]
  exact fineFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .backXZ .origin support hface

private theorem zFineQuery_subset
    (support : List Z4Plaq)
    (hface : outwardZFineQueryFace ∈ support) :
    ∀ id, id ∈ outwardZFineQuery →
      id ∈ geometricSupportIds 6 support := by
  rw [outwardZFineQuery_eq_geometric]
  exact fineFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .topXY .origin support hface

private theorem xFineQuery_not_subset
    (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardXFineQueryFace ∉ support) :
    ¬ (∀ id, id ∈ outwardXFineQuery →
      id ∈ geometricSupportIds 6 support) := by
  rw [outwardXFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .rightYZ .origin support hbox hface

private theorem yFineQuery_not_subset
    (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardYFineQueryFace ∉ support) :
    ¬ (∀ id, id ∈ outwardYFineQuery →
      id ∈ geometricSupportIds 6 support) := by
  rw [outwardYFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .backXZ .origin support hbox hface

private theorem zFineQuery_not_subset
    (support : List Z4Plaq)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardZFineQueryFace ∉ support) :
    ¬ (∀ id, id ∈ outwardZFineQuery →
      id ∈ geometricSupportIds 6 support) := by
  rw [outwardZFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .topXY .origin support hbox hface

theorem outwardXFineRoot_pattern_100 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXFineRoot) = (true, false, false) := by
  have hx : ∀ id, id ∈ outwardXFineQuery → id ∈ outwardXFineRoot := by
    simpa only [outwardXFineRoot] using
      xFineQuery_subset outwardXFineSurface outwardXFineQueryFace_mem_X
  have hy : ¬ (∀ id, id ∈ outwardYFineQuery → id ∈ outwardXFineRoot) := by
    simpa only [outwardXFineRoot] using
      yFineQuery_not_subset outwardXFineSurface
        outwardXFineSurface_subset_box_six
        outwardYFineQueryFace_not_mem_X
  have hz : ¬ (∀ id, id ∈ outwardZFineQuery → id ∈ outwardXFineRoot) := by
    simpa only [outwardXFineRoot] using
      zFineQuery_not_subset outwardXFineSurface
        outwardXFineSurface_subset_box_six
        outwardZFineQueryFace_not_mem_X
  apply outwardFinePattern_eq_of_events
  · exact componentLabel_subsupportEvent_true
      (volume := 6) (root := outwardXFineRoot) (query := outwardXFineQuery)
      outwardXFineRoot_mem_canonical hx
  · exact componentLabel_subsupportEvent_false
      (volume := 6) (root := outwardXFineRoot) (query := outwardYFineQuery)
      outwardXFineRoot_mem_canonical hy
  · exact componentLabel_subsupportEvent_false
      (volume := 6) (root := outwardXFineRoot) (query := outwardZFineQuery)
      outwardXFineRoot_mem_canonical hz

theorem outwardYFineRoot_pattern_010 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardYFineRoot) = (false, true, false) := by
  unfold physicalComponentSubsupportPattern outwardFineQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_false outwardYFineRoot_mem_canonical
      (xFineQuery_not_subset outwardYFineSurface
        outwardYFineSurface_subset_box_six
        outwardXFineQueryFace_not_mem_Y),
    componentLabel_subsupportEvent_true outwardYFineRoot_mem_canonical
      (yFineQuery_subset outwardYFineSurface
        outwardYFineQueryFace_mem_Y),
    componentLabel_subsupportEvent_false outwardYFineRoot_mem_canonical
      (zFineQuery_not_subset outwardYFineSurface
        outwardYFineSurface_subset_box_six
        outwardZFineQueryFace_not_mem_Y)]

theorem outwardZFineRoot_pattern_001 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardZFineRoot) = (false, false, true) := by
  unfold physicalComponentSubsupportPattern outwardFineQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_false outwardZFineRoot_mem_canonical
      (xFineQuery_not_subset outwardZFineSurface
        outwardZFineSurface_subset_box_six
        outwardXFineQueryFace_not_mem_Z),
    componentLabel_subsupportEvent_false outwardZFineRoot_mem_canonical
      (yFineQuery_not_subset outwardZFineSurface
        outwardZFineSurface_subset_box_six
        outwardYFineQueryFace_not_mem_Z),
    componentLabel_subsupportEvent_true outwardZFineRoot_mem_canonical
      (zFineQuery_subset outwardZFineSurface
        outwardZFineQueryFace_mem_Z)]

theorem outwardXFineQueryFace_mem_XY :
    outwardXFineQueryFace ∈ outwardXYFineSurface :=
  List.mem_append.mpr (Or.inl outwardXFineQueryFace_mem_X)

theorem outwardYFineQueryFace_mem_XY :
    outwardYFineQueryFace ∈ outwardXYFineSurface :=
  List.mem_append.mpr (Or.inr outwardYFineQueryFace_mem_Y)

theorem outwardZFineQueryFace_not_mem_XY :
    outwardZFineQueryFace ∉ outwardXYFineSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hx | hy
  · exact outwardZFineQueryFace_not_mem_X hx
  · exact outwardZFineQueryFace_not_mem_Y hy

theorem outwardXFineQueryFace_mem_XZ :
    outwardXFineQueryFace ∈ outwardXZFineSurface :=
  List.mem_append.mpr (Or.inl outwardXFineQueryFace_mem_X)

theorem outwardYFineQueryFace_not_mem_XZ :
    outwardYFineQueryFace ∉ outwardXZFineSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hx | hz
  · exact outwardYFineQueryFace_not_mem_X hx
  · exact outwardYFineQueryFace_not_mem_Z hz

theorem outwardZFineQueryFace_mem_XZ :
    outwardZFineQueryFace ∈ outwardXZFineSurface :=
  List.mem_append.mpr (Or.inr outwardZFineQueryFace_mem_Z)

theorem outwardXFineQueryFace_not_mem_YZ :
    outwardXFineQueryFace ∉ outwardYZFineSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hy | hz
  · exact outwardXFineQueryFace_not_mem_Y hy
  · exact outwardXFineQueryFace_not_mem_Z hz

theorem outwardYFineQueryFace_mem_YZ :
    outwardYFineQueryFace ∈ outwardYZFineSurface :=
  List.mem_append.mpr (Or.inl outwardYFineQueryFace_mem_Y)

theorem outwardZFineQueryFace_mem_YZ :
    outwardZFineQueryFace ∈ outwardYZFineSurface :=
  List.mem_append.mpr (Or.inr outwardZFineQueryFace_mem_Z)

theorem outwardXFineQueryFace_mem_XYZ :
    outwardXFineQueryFace ∈ outwardXYZFineSurface :=
  List.mem_append.mpr
    (Or.inl (List.mem_append.mpr
      (Or.inl outwardXFineQueryFace_mem_X)))

theorem outwardYFineQueryFace_mem_XYZ :
    outwardYFineQueryFace ∈ outwardXYZFineSurface :=
  List.mem_append.mpr
    (Or.inl (List.mem_append.mpr
      (Or.inr outwardYFineQueryFace_mem_Y)))

theorem outwardZFineQueryFace_mem_XYZ :
    outwardZFineQueryFace ∈ outwardXYZFineSurface :=
  List.mem_append.mpr (Or.inr outwardZFineQueryFace_mem_Z)

theorem outwardXYFineRoot_pattern_110 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXYFineRoot) = (true, true, false) := by
  unfold physicalComponentSubsupportPattern outwardFineQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true outwardXYFineRoot_mem_canonical
      (xFineQuery_subset outwardXYFineSurface
        outwardXFineQueryFace_mem_XY),
    componentLabel_subsupportEvent_true outwardXYFineRoot_mem_canonical
      (yFineQuery_subset outwardXYFineSurface
        outwardYFineQueryFace_mem_XY),
    componentLabel_subsupportEvent_false outwardXYFineRoot_mem_canonical
      (zFineQuery_not_subset outwardXYFineSurface
        outwardXYFineSurface_subset_box_six
        outwardZFineQueryFace_not_mem_XY)]

theorem outwardXZFineRoot_pattern_101 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXZFineRoot) = (true, false, true) := by
  unfold physicalComponentSubsupportPattern outwardFineQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true outwardXZFineRoot_mem_canonical
      (xFineQuery_subset outwardXZFineSurface
        outwardXFineQueryFace_mem_XZ),
    componentLabel_subsupportEvent_false outwardXZFineRoot_mem_canonical
      (yFineQuery_not_subset outwardXZFineSurface
        outwardXZFineSurface_subset_box_six
        outwardYFineQueryFace_not_mem_XZ),
    componentLabel_subsupportEvent_true outwardXZFineRoot_mem_canonical
      (zFineQuery_subset outwardXZFineSurface
        outwardZFineQueryFace_mem_XZ)]

theorem outwardYZFineRoot_pattern_011 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardYZFineRoot) = (false, true, true) := by
  unfold physicalComponentSubsupportPattern outwardFineQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_false outwardYZFineRoot_mem_canonical
      (xFineQuery_not_subset outwardYZFineSurface
        outwardYZFineSurface_subset_box_six
        outwardXFineQueryFace_not_mem_YZ),
    componentLabel_subsupportEvent_true outwardYZFineRoot_mem_canonical
      (yFineQuery_subset outwardYZFineSurface
        outwardYFineQueryFace_mem_YZ),
    componentLabel_subsupportEvent_true outwardYZFineRoot_mem_canonical
      (zFineQuery_subset outwardYZFineSurface
        outwardZFineQueryFace_mem_YZ)]

theorem outwardXYZFineRoot_pattern_111 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXYZFineRoot) = (true, true, true) := by
  unfold physicalComponentSubsupportPattern outwardFineQueries
    componentSubsupportQueryLeft componentSubsupportQueryShared
    componentSubsupportQueryRight
  rw [componentLabel_subsupportEvent_true outwardXYZFineRoot_mem_canonical
      (xFineQuery_subset outwardXYZFineSurface
        outwardXFineQueryFace_mem_XYZ),
    componentLabel_subsupportEvent_true outwardXYZFineRoot_mem_canonical
      (yFineQuery_subset outwardXYZFineSurface
        outwardYFineQueryFace_mem_XYZ),
    componentLabel_subsupportEvent_true outwardXYZFineRoot_mem_canonical
      (zFineQuery_subset outwardXYZFineSurface
        outwardZFineQueryFace_mem_XYZ)]

theorem outwardNonzeroFinePattern_witnesses :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXFineRoot) = (true, false, false) ∧
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardYFineRoot) = (false, true, false) ∧
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardZFineRoot) = (false, false, true) ∧
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXYFineRoot) = (true, true, false) ∧
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXZFineRoot) = (true, false, true) ∧
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardYZFineRoot) = (false, true, true) ∧
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXYZFineRoot) = (true, true, true) :=
  ⟨outwardXFineRoot_pattern_100, outwardYFineRoot_pattern_010,
    outwardZFineRoot_pattern_001, outwardXYFineRoot_pattern_110,
    outwardXZFineRoot_pattern_101, outwardYZFineRoot_pattern_011,
    outwardXYZFineRoot_pattern_111⟩

/-! ## 4. Positive normalized mass for all eight fine cells -/

theorem outwardNonzeroFinePatternMasses_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, false, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (false, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (false, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (false, true, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, true, true) := by
  exact ⟨
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardFineQueries (true, false, false) outwardXFineRoot
      outwardXFineRoot_mem_canonical outwardXFineRoot_pattern_100
      (outwardXFineRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardFineQueries (false, true, false) outwardYFineRoot
      outwardYFineRoot_mem_canonical outwardYFineRoot_pattern_010
      (outwardYFineRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardFineQueries (false, false, true) outwardZFineRoot
      outwardZFineRoot_mem_canonical outwardZFineRoot_pattern_001
      (outwardZFineRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardFineQueries (true, true, false) outwardXYFineRoot
      outwardXYFineRoot_mem_canonical outwardXYFineRoot_pattern_110
      (outwardXYFineRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardFineQueries (true, false, true) outwardXZFineRoot
      outwardXZFineRoot_mem_canonical outwardXZFineRoot_pattern_101
      (outwardXZFineRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardFineQueries (false, true, true) outwardYZFineRoot
      outwardYZFineRoot_mem_canonical outwardYZFineRoot_pattern_011
      (outwardYZFineRoot_activity_pos hcoupling),
    normalizedPhysicalThreeSubsupport_patternMass_pos_of_componentLabel
      coupling (Q'.le_of_lt hcoupling) 1 6 (by omega)
      outwardFineQueries (true, true, true) outwardXYZFineRoot
      outwardXYZFineRoot_mem_canonical outwardXYZFineRoot_pattern_111
      (outwardXYZFineRoot_activity_pos hcoupling)⟩

theorem outwardFineVacuum_pattern_000 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        zeroEdgeLabelling = (false, false, false) := by
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent
    familyContainsComponentSubsupportB
  rw [physicalCanonicalAmbientFamily_zero_local]
  rfl

theorem outwardFineVacuumPatternMass_pos
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling hcoupling
        1 6 outwardFineQueries) (false, false, false) := by
  apply normalizedPhysicalThreeSubsupport_patternMass_pos_of_physical
    coupling hcoupling 1 6 outwardFineQueries
    (false, false, false) zeroEdgeLabelling
  · exact zeroEdgeLabelling_mem_bounded 1 6
  · exact outwardFineVacuum_pattern_000
  · have heq := parametricKPhysicalTerm_zero_eqv_one coupling 1 6
    exact Q'.pos_of_lt_of_le
      (show (0 : Q') < (1 : Q') by decide)
      (Q'.le_of_eqv (Q'.eqv_symm heq))

/-- Every Boolean cell of the exact outward fine-query law has strictly
positive normalized mass at every strictly positive derived coupling. -/
theorem outwardAllEightFinePatternMasses_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (false, false, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, false, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (false, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (false, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, true, false) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, false, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (false, true, true) ∧
    (0 : Q') < threeBlockPatternMass
      (normalizedPhysicalThreeSubsupportLaw coupling
        (Q'.le_of_lt hcoupling) 1 6 outwardFineQueries)
      (true, true, true) := by
  exact ⟨outwardFineVacuumPatternMass_pos coupling
      (Q'.le_of_lt hcoupling),
    outwardNonzeroFinePatternMasses_pos coupling hcoupling⟩

#print axioms fineFaceQuerySupport_subset_geometricRoot
#print axioms fineFaceQuerySupport_not_subset_geometricRoot
#print axioms outwardFineQueryFace_membership_matrix
#print axioms outwardXFineRoot_pattern_100
#print axioms outwardYFineRoot_pattern_010
#print axioms outwardZFineRoot_pattern_001
#print axioms outwardXYFineRoot_pattern_110
#print axioms outwardXZFineRoot_pattern_101
#print axioms outwardYZFineRoot_pattern_011
#print axioms outwardXYZFineRoot_pattern_111
#print axioms outwardNonzeroFinePattern_witnesses
#print axioms outwardNonzeroFinePatternMasses_pos
#print axioms outwardFineVacuum_pattern_000
#print axioms outwardFineVacuumPatternMass_pos
#print axioms outwardAllEightFinePatternMasses_pos

end YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
