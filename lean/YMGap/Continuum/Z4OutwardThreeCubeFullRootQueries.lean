/-
# Full-root queries for the outward three-cube carriers

Distinguished child-face queries admit smaller closed lifts.  Complete-root
queries remove that ambiguity.  This file gives every entry of the coarse and
fine seven-row truth tables as an exact event theorem, together with a generic
event-to-pattern gate and an explicit six-face counterexample to the old query.
-/

import YMGap.Continuum.Z4OutwardThreeCubeFineCarrier
import YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns

namespace YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
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
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. Complete-root queries and reusable gates -/

def outwardCoarseFullRootQueries : ComponentSubsupportQueryTriple :=
  (outwardXRoot, outwardYRoot, outwardZRoot)

def outwardFineFullRootQueries : ComponentSubsupportQueryTriple :=
  (outwardXFineRoot, outwardYFineRoot, outwardZFineRoot)

theorem geometricSupportIds_mono
    {volume : Nat} {source target : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ source → plaquette ∈ target) :
    ∀ id, id ∈ geometricSupportIds volume source →
      id ∈ geometricSupportIds volume target := by
  intro id hid
  have hparts :=
    (mem_geometricSupportIds_iff volume source id).1 hid
  exact (mem_geometricSupportIds_iff volume target id).2
    ⟨hparts.1, hsubset _ hparts.2⟩

theorem geometricSupportIds_not_subset_of_witness
    {volume : Nat} {source target : List Z4Plaq}
    (hsourceBox : ∀ plaquette, plaquette ∈ source →
      plaquette ∈ boxPlaquettes volume)
    (witness : Z4Plaq) (hwitnessSource : witness ∈ source)
    (hwitnessTarget : witness ∉ target) :
    ¬ (∀ id, id ∈ geometricSupportIds volume source →
      id ∈ geometricSupportIds volume target) := by
  intro hsubset
  have hdecoded : witness ∈
      geometricPolymer volume (geometricSupportIds volume source) :=
    (geometricSupportIds_sameSupport hsourceBox).2 witness hwitnessSource
  obtain ⟨id, hidSource, hidEq⟩ := List.mem_map.mp hdecoded
  have hidTarget := hsubset id hidSource
  have htarget :=
    (mem_geometricSupportIds_iff volume target id).1 hidTarget
  exact hwitnessTarget (hidEq ▸ htarget.2)

theorem componentLabel_geometricFullRootEvent_true
    {query carrier : List Z4Plaq}
    (hcarrier : geometricSupportIds 6 carrier ∈
      canonicalSurfacePolymers 6)
    (hsubset : ∀ plaquette, plaquette ∈ query →
      plaquette ∈ carrier) :
    physicalComponentSubsupportEvent 6
        (geometricSupportIds 6 query)
        (componentLabel (geometricSupportIds 6 carrier)) = true := by
  exact componentLabel_subsupportEvent_true hcarrier
    (geometricSupportIds_mono hsubset)

theorem componentLabel_geometricFullRootEvent_false
    {query carrier : List Z4Plaq}
    (hcarrier : geometricSupportIds 6 carrier ∈
      canonicalSurfacePolymers 6)
    (hqueryBox : ∀ plaquette, plaquette ∈ query →
      plaquette ∈ boxPlaquettes 6)
    (witness : Z4Plaq) (hwitnessQuery : witness ∈ query)
    (hwitnessCarrier : witness ∉ carrier) :
    physicalComponentSubsupportEvent 6
        (geometricSupportIds 6 query)
        (componentLabel (geometricSupportIds 6 carrier)) = false := by
  exact componentLabel_subsupportEvent_false hcarrier
    (geometricSupportIds_not_subset_of_witness
      hqueryBox witness hwitnessQuery hwitnessCarrier)

/-- The small kernel-facing bridge from three event entries to the literal
Boolean truth-table row. -/
theorem physicalComponentSubsupportPattern_eq_of_event_entries
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

private theorem subset_refl_surface (surface : List Z4Plaq) :
    ∀ plaquette, plaquette ∈ surface → plaquette ∈ surface := by
  intro plaquette hplaquette
  exact hplaquette

private theorem subset_left_append
    (left right : List Z4Plaq) :
    ∀ plaquette, plaquette ∈ left → plaquette ∈ left ++ right := by
  intro plaquette hplaquette
  exact List.mem_append.mpr (Or.inl hplaquette)

private theorem subset_right_append
    (left right : List Z4Plaq) :
    ∀ plaquette, plaquette ∈ right → plaquette ∈ left ++ right := by
  intro plaquette hplaquette
  exact List.mem_append.mpr (Or.inr hplaquette)

private theorem subset_left_three
    (left middle right : List Z4Plaq) :
    ∀ plaquette, plaquette ∈ left →
      plaquette ∈ left ++ middle ++ right := by
  intro plaquette hplaquette
  exact List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inl hplaquette)))

private theorem subset_middle_three
    (left middle right : List Z4Plaq) :
    ∀ plaquette, plaquette ∈ middle →
      plaquette ∈ left ++ middle ++ right := by
  intro plaquette hplaquette
  exact List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inr hplaquette)))

private theorem subset_right_three
    (left middle right : List Z4Plaq) :
    ∀ plaquette, plaquette ∈ right →
      plaquette ∈ left ++ middle ++ right := by
  intro plaquette hplaquette
  exact List.mem_append.mpr (Or.inr hplaquette)

/-! ## 2. Coarse truth table: `100, 010, 001, 110, 101, 011, 111` -/

theorem outwardXRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXRoot
        (componentLabel outwardXRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXRoot_mem_canonical (subset_refl_surface outwardXSurface)

theorem outwardXRoot_fullY_false :
    physicalComponentSubsupportEvent 6 outwardYRoot
        (componentLabel outwardXRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXRoot_mem_canonical outwardYSurface_subset_box_six
    outwardYQueryFace outwardYQueryFace_mem_Y outwardYQueryFace_not_mem_X

theorem outwardXRoot_fullZ_false :
    physicalComponentSubsupportEvent 6 outwardZRoot
        (componentLabel outwardXRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXRoot_mem_canonical outwardZSurface_subset_box_six
    outwardZQueryFace outwardZQueryFace_mem_Z outwardZQueryFace_not_mem_X

theorem outwardYRoot_fullX_false :
    physicalComponentSubsupportEvent 6 outwardXRoot
        (componentLabel outwardYRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardYRoot_mem_canonical outwardXSurface_subset_box_six
    outwardXQueryFace outwardXQueryFace_mem_X outwardXQueryFace_not_mem_Y

theorem outwardYRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYRoot
        (componentLabel outwardYRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardYRoot_mem_canonical (subset_refl_surface outwardYSurface)

theorem outwardYRoot_fullZ_false :
    physicalComponentSubsupportEvent 6 outwardZRoot
        (componentLabel outwardYRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardYRoot_mem_canonical outwardZSurface_subset_box_six
    outwardZQueryFace outwardZQueryFace_mem_Z outwardZQueryFace_not_mem_Y

theorem outwardZRoot_fullX_false :
    physicalComponentSubsupportEvent 6 outwardXRoot
        (componentLabel outwardZRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardZRoot_mem_canonical outwardXSurface_subset_box_six
    outwardXQueryFace outwardXQueryFace_mem_X outwardXQueryFace_not_mem_Z

theorem outwardZRoot_fullY_false :
    physicalComponentSubsupportEvent 6 outwardYRoot
        (componentLabel outwardZRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardZRoot_mem_canonical outwardYSurface_subset_box_six
    outwardYQueryFace outwardYQueryFace_mem_Y outwardYQueryFace_not_mem_Z

theorem outwardZRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZRoot
        (componentLabel outwardZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardZRoot_mem_canonical (subset_refl_surface outwardZSurface)

theorem outwardXYRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXRoot
        (componentLabel outwardXYRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYRoot_mem_canonical
    (subset_left_append outwardXSurface outwardYSurface)

theorem outwardXYRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYRoot
        (componentLabel outwardXYRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYRoot_mem_canonical
    (subset_right_append outwardXSurface outwardYSurface)

theorem outwardXYRoot_fullZ_false :
    physicalComponentSubsupportEvent 6 outwardZRoot
        (componentLabel outwardXYRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXYRoot_mem_canonical outwardZSurface_subset_box_six
    outwardZQueryFace outwardZQueryFace_mem_Z outwardZQueryFace_not_mem_XY

theorem outwardXZRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXRoot
        (componentLabel outwardXZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXZRoot_mem_canonical
    (subset_left_append outwardXSurface outwardZSurface)

theorem outwardXZRoot_fullY_false :
    physicalComponentSubsupportEvent 6 outwardYRoot
        (componentLabel outwardXZRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXZRoot_mem_canonical outwardYSurface_subset_box_six
    outwardYQueryFace outwardYQueryFace_mem_Y outwardYQueryFace_not_mem_XZ

theorem outwardXZRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZRoot
        (componentLabel outwardXZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXZRoot_mem_canonical
    (subset_right_append outwardXSurface outwardZSurface)

theorem outwardYZRoot_fullX_false :
    physicalComponentSubsupportEvent 6 outwardXRoot
        (componentLabel outwardYZRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardYZRoot_mem_canonical outwardXSurface_subset_box_six
    outwardXQueryFace outwardXQueryFace_mem_X outwardXQueryFace_not_mem_YZ

theorem outwardYZRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYRoot
        (componentLabel outwardYZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardYZRoot_mem_canonical
    (subset_left_append outwardYSurface outwardZSurface)

theorem outwardYZRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZRoot
        (componentLabel outwardYZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardYZRoot_mem_canonical
    (subset_right_append outwardYSurface outwardZSurface)

theorem outwardXYZRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXRoot
        (componentLabel outwardXYZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYZRoot_mem_canonical
    (subset_left_three outwardXSurface outwardYSurface outwardZSurface)

theorem outwardXYZRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYRoot
        (componentLabel outwardXYZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYZRoot_mem_canonical
    (subset_middle_three outwardXSurface outwardYSurface outwardZSurface)

theorem outwardXYZRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZRoot
        (componentLabel outwardXYZRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYZRoot_mem_canonical
    (subset_right_three outwardXSurface outwardYSurface outwardZSurface)

/-! ## 3. Fine-scale probe matrix -/

def outwardXFineRootProbeFace : Z4Plaq :=
  dyadicCell
    (axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ)) .origin

def outwardYFineRootProbeFace : Z4Plaq :=
  dyadicCell
    (axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ)) .origin

def outwardZFineRootProbeFace : Z4Plaq :=
  dyadicCell
    (axisShiftPlaquette zeroAxisOffset (cubeFace .topXY)) .origin

theorem outwardFineRootProbeFace_membership_matrix :
    outwardXFineRootProbeFace ∈ outwardXFineSurface ∧
    outwardXFineRootProbeFace ∉ outwardYFineSurface ∧
    outwardXFineRootProbeFace ∉ outwardZFineSurface ∧
    outwardYFineRootProbeFace ∉ outwardXFineSurface ∧
    outwardYFineRootProbeFace ∈ outwardYFineSurface ∧
    outwardYFineRootProbeFace ∉ outwardZFineSurface ∧
    outwardZFineRootProbeFace ∉ outwardXFineSurface ∧
    outwardZFineRootProbeFace ∉ outwardYFineSurface ∧
    outwardZFineRootProbeFace ∈ outwardZFineSurface := by
  simp [outwardXFineRootProbeFace, outwardYFineRootProbeFace,
    outwardZFineRootProbeFace, outwardXFineSurface, outwardYFineSurface,
    outwardZFineSurface, axisFineCubeSurface, axisCubeSurface,
    dyadicSupportCells, dyadicPlaquetteCells, dyadicCellIndices,
    unitCubeSurface, axisShiftPlaquette, axisShiftVertex, zeroAxisOffset,
    xAxisOffset, yAxisOffset, zAxisOffset, cubeFace, dyadicCell,
    dyadicVertex, dirsOf, addE]

theorem outwardXFineRootProbeFace_mem_X :
    outwardXFineRootProbeFace ∈ outwardXFineSurface :=
  outwardFineRootProbeFace_membership_matrix.1

theorem outwardXFineRootProbeFace_not_mem_Y :
    outwardXFineRootProbeFace ∉ outwardYFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.1

theorem outwardXFineRootProbeFace_not_mem_Z :
    outwardXFineRootProbeFace ∉ outwardZFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.2.1

theorem outwardYFineRootProbeFace_not_mem_X :
    outwardYFineRootProbeFace ∉ outwardXFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.2.2.1

theorem outwardYFineRootProbeFace_mem_Y :
    outwardYFineRootProbeFace ∈ outwardYFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.2.2.2.1

theorem outwardYFineRootProbeFace_not_mem_Z :
    outwardYFineRootProbeFace ∉ outwardZFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.2.2.2.2.1

theorem outwardZFineRootProbeFace_not_mem_X :
    outwardZFineRootProbeFace ∉ outwardXFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.2.2.2.2.2.1

theorem outwardZFineRootProbeFace_not_mem_Y :
    outwardZFineRootProbeFace ∉ outwardYFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.2.2.2.2.2.2.1

theorem outwardZFineRootProbeFace_mem_Z :
    outwardZFineRootProbeFace ∈ outwardZFineSurface :=
  outwardFineRootProbeFace_membership_matrix.2.2.2.2.2.2.2.2

theorem outwardZFineRootProbeFace_not_mem_XY :
    outwardZFineRootProbeFace ∉ outwardXYFineSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hx | hy
  · exact outwardZFineRootProbeFace_not_mem_X hx
  · exact outwardZFineRootProbeFace_not_mem_Y hy

theorem outwardYFineRootProbeFace_not_mem_XZ :
    outwardYFineRootProbeFace ∉ outwardXZFineSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hx | hz
  · exact outwardYFineRootProbeFace_not_mem_X hx
  · exact outwardYFineRootProbeFace_not_mem_Z hz

theorem outwardXFineRootProbeFace_not_mem_YZ :
    outwardXFineRootProbeFace ∉ outwardYZFineSurface := by
  intro hmem
  rcases List.mem_append.mp hmem with hy | hz
  · exact outwardXFineRootProbeFace_not_mem_Y hy
  · exact outwardXFineRootProbeFace_not_mem_Z hz

/-! ## 4. Fine truth table: `100, 010, 001, 110, 101, 011, 111` -/

theorem outwardXFineRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardXFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXFineRoot_mem_canonical
    (subset_refl_surface outwardXFineSurface)

theorem outwardXFineRoot_fullY_false :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardXFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXFineRoot_mem_canonical outwardYFineSurface_subset_box_six
    outwardYFineRootProbeFace outwardYFineRootProbeFace_mem_Y
    outwardYFineRootProbeFace_not_mem_X

theorem outwardXFineRoot_fullZ_false :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardXFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXFineRoot_mem_canonical outwardZFineSurface_subset_box_six
    outwardZFineRootProbeFace outwardZFineRootProbeFace_mem_Z
    outwardZFineRootProbeFace_not_mem_X

theorem outwardYFineRoot_fullX_false :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardYFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardYFineRoot_mem_canonical outwardXFineSurface_subset_box_six
    outwardXFineRootProbeFace outwardXFineRootProbeFace_mem_X
    outwardXFineRootProbeFace_not_mem_Y

theorem outwardYFineRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardYFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardYFineRoot_mem_canonical
    (subset_refl_surface outwardYFineSurface)

theorem outwardYFineRoot_fullZ_false :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardYFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardYFineRoot_mem_canonical outwardZFineSurface_subset_box_six
    outwardZFineRootProbeFace outwardZFineRootProbeFace_mem_Z
    outwardZFineRootProbeFace_not_mem_Y

theorem outwardZFineRoot_fullX_false :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardZFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardZFineRoot_mem_canonical outwardXFineSurface_subset_box_six
    outwardXFineRootProbeFace outwardXFineRootProbeFace_mem_X
    outwardXFineRootProbeFace_not_mem_Z

theorem outwardZFineRoot_fullY_false :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardZFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardZFineRoot_mem_canonical outwardYFineSurface_subset_box_six
    outwardYFineRootProbeFace outwardYFineRootProbeFace_mem_Y
    outwardYFineRootProbeFace_not_mem_Z

theorem outwardZFineRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardZFineRoot_mem_canonical
    (subset_refl_surface outwardZFineSurface)

theorem outwardXYFineRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardXYFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYFineRoot_mem_canonical
    (subset_left_append outwardXFineSurface outwardYFineSurface)

theorem outwardXYFineRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardXYFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYFineRoot_mem_canonical
    (subset_right_append outwardXFineSurface outwardYFineSurface)

theorem outwardXYFineRoot_fullZ_false :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardXYFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXYFineRoot_mem_canonical outwardZFineSurface_subset_box_six
    outwardZFineRootProbeFace outwardZFineRootProbeFace_mem_Z
    outwardZFineRootProbeFace_not_mem_XY

theorem outwardXZFineRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardXZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXZFineRoot_mem_canonical
    (subset_left_append outwardXFineSurface outwardZFineSurface)

theorem outwardXZFineRoot_fullY_false :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardXZFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardXZFineRoot_mem_canonical outwardYFineSurface_subset_box_six
    outwardYFineRootProbeFace outwardYFineRootProbeFace_mem_Y
    outwardYFineRootProbeFace_not_mem_XZ

theorem outwardXZFineRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardXZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXZFineRoot_mem_canonical
    (subset_right_append outwardXFineSurface outwardZFineSurface)

theorem outwardYZFineRoot_fullX_false :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardYZFineRoot) = false := by
  exact componentLabel_geometricFullRootEvent_false
    outwardYZFineRoot_mem_canonical outwardXFineSurface_subset_box_six
    outwardXFineRootProbeFace outwardXFineRootProbeFace_mem_X
    outwardXFineRootProbeFace_not_mem_YZ

theorem outwardYZFineRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardYZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardYZFineRoot_mem_canonical
    (subset_left_append outwardYFineSurface outwardZFineSurface)

theorem outwardYZFineRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardYZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardYZFineRoot_mem_canonical
    (subset_right_append outwardYFineSurface outwardZFineSurface)

theorem outwardXYZFineRoot_fullX_true :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardXYZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYZFineRoot_mem_canonical
    (subset_left_three outwardXFineSurface outwardYFineSurface
      outwardZFineSurface)

theorem outwardXYZFineRoot_fullY_true :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardXYZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYZFineRoot_mem_canonical
    (subset_middle_three outwardXFineSurface outwardYFineSurface
      outwardZFineSurface)

theorem outwardXYZFineRoot_fullZ_true :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardXYZFineRoot) = true := by
  exact componentLabel_geometricFullRootEvent_true
    outwardXYZFineRoot_mem_canonical
    (subset_right_three outwardXFineSurface outwardYFineSurface
      outwardZFineSurface)

/-! ## 5. Six-face child-lift refutation fence -/

def outwardXFineSmallLiftOffset : AxisOffset :=
  doubleAxisOffset xAxisOffset

def outwardXFineSmallLiftSurface : List Z4Plaq :=
  axisCubeSurface outwardXFineSmallLiftOffset

def outwardXFineSmallLiftRoot : List Nat :=
  geometricSupportIds 6 outwardXFineSmallLiftSurface

theorem outwardXFineSmallLiftSurface_length :
    outwardXFineSmallLiftSurface.length = 6 := by
  simp [outwardXFineSmallLiftSurface, axisCubeSurface, unitCubeSurface]

theorem outwardFineSingleSurfaces_length :
    outwardXFineSurface.length = 24 ∧
    outwardYFineSurface.length = 24 ∧
    outwardZFineSurface.length = 24 := by
  simp [outwardXFineSurface, outwardYFineSurface, outwardZFineSurface,
    axisFineCubeSurface, axisCubeSurface, dyadicSupportCells_length,
    unitCubeSurface]

theorem outwardXFineSmallLiftSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXFineSmallLiftSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ :=
    decodeMapMember (axisShiftPlaquette outwardXFineSmallLiftOffset)
      unitCubeSurface plaquette hplaquette
  have hfour : axisShiftPlaquette outwardXFineSmallLiftOffset source ∈
      boxPlaquettes 4 := by
    simpa [outwardXFineSmallLiftOffset, doubleAxisOffset, xAxisOffset] using
      (axisShiftPlaquette_mem_extended_box outwardXFineSmallLiftOffset
        (unitCubeSurface_subset_box_two source hsource))
  exact boxPlaquettes_mono (by omega) hfour

theorem outwardXFineRootProbeFace_eq_smallLiftLeftFace :
    outwardXFineRootProbeFace =
      axisShiftPlaquette outwardXFineSmallLiftOffset
        (cubeFace .leftYZ) := by
  simp [outwardXFineRootProbeFace, outwardXFineSmallLiftOffset,
    doubleAxisOffset, xAxisOffset, zeroAxisOffset, cubeFace,
    axisShiftPlaquette, axisShiftVertex, dyadicCell, dyadicVertex]

theorem outwardXFineRootProbeFace_mem_smallLift :
    outwardXFineRootProbeFace ∈ outwardXFineSmallLiftSurface := by
  rw [outwardXFineRootProbeFace_eq_smallLiftLeftFace]
  unfold outwardXFineSmallLiftSurface axisCubeSurface
  exact List.mem_map.mpr
    ⟨cubeFace .leftYZ, cubeFace_mem_unitCubeSurface .leftYZ, rfl⟩

private theorem geometricRoot_mem_canonical_of_surface
    {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hnonempty : Σ' plaquette : Z4Plaq, plaquette ∈ support)
    (hconnected : PolymerModel.connectedIn
      (L := z4Chain.toLattice) support) :
    geometricSupportIds 6 support ∈ canonicalSurfacePolymers 6 := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · exact geometricSupportIds_mem_cutoffOneFaceSupports 6 support
  · obtain ⟨plaquette, hplaquette⟩ := hnonempty
    have hdecoded : plaquette ∈
        geometricPolymer 6 (geometricSupportIds 6 support) :=
      (geometricSupportIds_sameSupport hbox).2 plaquette hplaquette
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt 6)
        (geometricSupportIds 6 support) plaquette hdecoded
    exact ⟨identifier, hidentifier⟩
  · exact geometricSupportIds_connected hbox hconnected

theorem outwardXFineSmallLiftRoot_mem_canonical :
    outwardXFineSmallLiftRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical_of_surface
    outwardXFineSmallLiftSurface_subset_box_six
    ⟨outwardXFineRootProbeFace,
      outwardXFineRootProbeFace_mem_smallLift⟩
    (axisCubeSurface_connected outwardXFineSmallLiftOffset)

def outwardXDistinguishedFineChildQuery : List Nat :=
  geometricSupportIds 6 [outwardXFineRootProbeFace]

theorem outwardXFineSmallLift_childQuery_true :
    physicalComponentSubsupportEvent 6
        outwardXDistinguishedFineChildQuery
        (componentLabel outwardXFineSmallLiftRoot) = true := by
  apply componentLabel_subsupportEvent_true
    outwardXFineSmallLiftRoot_mem_canonical
  unfold outwardXDistinguishedFineChildQuery outwardXFineSmallLiftRoot
  apply geometricSupportIds_mono
  intro plaquette hplaquette
  have heq : plaquette = outwardXFineRootProbeFace := by
    simpa only [List.mem_singleton] using hplaquette
  rw [heq]
  exact outwardXFineRootProbeFace_mem_smallLift

def outwardXFineFarProbeFace : Z4Plaq :=
  dyadicCell
    (axisShiftPlaquette xAxisOffset (cubeFace .rightYZ)) .origin

theorem outwardXFineFarProbeFace_mem_X :
    outwardXFineFarProbeFace ∈ outwardXFineSurface := by
  unfold outwardXFineFarProbeFace outwardXFineSurface axisFineCubeSurface
  apply (mem_dyadicSupportCells_iff _ _).2
  exact ⟨axisShiftPlaquette xAxisOffset (cubeFace .rightYZ),
    List.mem_map.mpr
      ⟨cubeFace .rightYZ, cubeFace_mem_unitCubeSurface .rightYZ, rfl⟩,
    dyadicCell_mem_cells _ _⟩

theorem outwardXFineFarProbeFace_not_mem_smallLift :
    outwardXFineFarProbeFace ∉ outwardXFineSmallLiftSurface := by
  simp [outwardXFineFarProbeFace, outwardXFineSmallLiftSurface,
    outwardXFineSmallLiftOffset, axisCubeSurface, unitCubeSurface,
    axisShiftPlaquette, axisShiftVertex, doubleAxisOffset, xAxisOffset,
    cubeFace, dyadicCell, dyadicVertex]

theorem outwardYFineRootProbeFace_not_mem_smallLift :
    outwardYFineRootProbeFace ∉ outwardXFineSmallLiftSurface := by
  simp [outwardYFineRootProbeFace, outwardXFineSmallLiftSurface,
    outwardXFineSmallLiftOffset, axisCubeSurface, unitCubeSurface,
    axisShiftPlaquette, axisShiftVertex, doubleAxisOffset, zeroAxisOffset,
    xAxisOffset, cubeFace, dyadicCell, dyadicVertex]

theorem outwardZFineRootProbeFace_not_mem_smallLift :
    outwardZFineRootProbeFace ∉ outwardXFineSmallLiftSurface := by
  simp [outwardZFineRootProbeFace, outwardXFineSmallLiftSurface,
    outwardXFineSmallLiftOffset, axisCubeSurface, unitCubeSurface,
    axisShiftPlaquette, axisShiftVertex, doubleAxisOffset, zeroAxisOffset,
    xAxisOffset, cubeFace, dyadicCell, dyadicVertex]

theorem outwardXFineRoot_not_subset_smallLift :
    ¬ (∀ id, id ∈ outwardXFineRoot →
      id ∈ outwardXFineSmallLiftRoot) := by
  unfold outwardXFineRoot outwardXFineSmallLiftRoot
  exact geometricSupportIds_not_subset_of_witness
    outwardXFineSurface_subset_box_six outwardXFineFarProbeFace
    outwardXFineFarProbeFace_mem_X
    outwardXFineFarProbeFace_not_mem_smallLift

theorem outwardYFineRoot_not_subset_smallLift :
    ¬ (∀ id, id ∈ outwardYFineRoot →
      id ∈ outwardXFineSmallLiftRoot) := by
  unfold outwardYFineRoot outwardXFineSmallLiftRoot
  exact geometricSupportIds_not_subset_of_witness
    outwardYFineSurface_subset_box_six outwardYFineRootProbeFace
    outwardYFineRootProbeFace_mem_Y
    outwardYFineRootProbeFace_not_mem_smallLift

theorem outwardZFineRoot_not_subset_smallLift :
    ¬ (∀ id, id ∈ outwardZFineRoot →
      id ∈ outwardXFineSmallLiftRoot) := by
  unfold outwardZFineRoot outwardXFineSmallLiftRoot
  exact geometricSupportIds_not_subset_of_witness
    outwardZFineSurface_subset_box_six outwardZFineRootProbeFace
    outwardZFineRootProbeFace_mem_Z
    outwardZFineRootProbeFace_not_mem_smallLift

theorem outwardXFineSmallLift_fullX_false :
    physicalComponentSubsupportEvent 6 outwardXFineRoot
        (componentLabel outwardXFineSmallLiftRoot) = false :=
  componentLabel_subsupportEvent_false
    outwardXFineSmallLiftRoot_mem_canonical
    outwardXFineRoot_not_subset_smallLift

theorem outwardXFineSmallLift_fullY_false :
    physicalComponentSubsupportEvent 6 outwardYFineRoot
        (componentLabel outwardXFineSmallLiftRoot) = false :=
  componentLabel_subsupportEvent_false
    outwardXFineSmallLiftRoot_mem_canonical
    outwardYFineRoot_not_subset_smallLift

theorem outwardXFineSmallLift_fullZ_false :
    physicalComponentSubsupportEvent 6 outwardZFineRoot
        (componentLabel outwardXFineSmallLiftRoot) = false :=
  componentLabel_subsupportEvent_false
    outwardXFineSmallLiftRoot_mem_canonical
    outwardZFineRoot_not_subset_smallLift

/-- Existential form of the refutation fence keeps the concrete finite edge
labelling opaque while exhibiting it constructively. -/
theorem distinguishedChildQuery_does_not_characterize_fullFineRoot :
    ∃ physical : EdgeLabelling,
      physicalComponentSubsupportEvent 6
          outwardXDistinguishedFineChildQuery physical = true ∧
      physicalComponentSubsupportEvent 6 outwardXFineRoot physical = false ∧
      physicalComponentSubsupportEvent 6 outwardYFineRoot physical = false ∧
      physicalComponentSubsupportEvent 6 outwardZFineRoot physical = false := by
  exact ⟨componentLabel outwardXFineSmallLiftRoot,
    outwardXFineSmallLift_childQuery_true,
    outwardXFineSmallLift_fullX_false,
    outwardXFineSmallLift_fullY_false,
    outwardXFineSmallLift_fullZ_false⟩

#print axioms geometricSupportIds_mono
#print axioms geometricSupportIds_not_subset_of_witness
#print axioms physicalComponentSubsupportPattern_eq_of_event_entries
#print axioms outwardXYZRoot_fullX_true
#print axioms outwardXYZRoot_fullY_true
#print axioms outwardXYZRoot_fullZ_true
#print axioms outwardFineRootProbeFace_membership_matrix
#print axioms outwardXYZFineRoot_fullX_true
#print axioms outwardXYZFineRoot_fullY_true
#print axioms outwardXYZFineRoot_fullZ_true
#print axioms outwardXFineSmallLiftRoot_mem_canonical
#print axioms outwardXFineRoot_not_subset_smallLift
#print axioms distinguishedChildQuery_does_not_characterize_fullFineRoot

end YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries
