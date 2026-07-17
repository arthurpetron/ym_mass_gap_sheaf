/-
# Four exact seven-cube boundary carriers for an outward-query cycle

These four literal 28-face supports are rigid images of one seven-cube
polycube boundary.  Their outward coarse/fine truth-table edges form the
directed cycle

`011 -> 100 -> 000 -> 111 -> 011`.

Every support has exactly one four-valent touched link; all other touched
links are bivalent.  The statements below are exact finite geometry, not a
numerical approximation.
-/

import YMGap.Continuum.Z4OutwardCentralSmallLiftActivityPair
import YMGap.Continuum.Z4SingleFourIncidenceActivity

namespace YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

/-! ## 1. The four literal boundaries -/

def sevenCube011To100Surface : List Z4Plaq :=
  [((0, 0, 0, 0), .p12), ((0, 1, 1, 0), .p12),
   ((0, 2, 1, 0), .p12), ((1, 0, 1, 0), .p12),
   ((1, 1, 0, 0), .p12), ((1, 2, 1, 0), .p12),
   ((2, 0, 0, 0), .p12), ((2, 0, 1, 0), .p12),
   ((2, 1, 0, 0), .p12), ((2, 1, 1, 0), .p12),
   ((0, 0, 0, 0), .p02), ((0, 1, 0, 0), .p02),
   ((0, 1, 1, 0), .p02), ((0, 3, 1, 0), .p02),
   ((1, 0, 0, 0), .p02), ((1, 0, 1, 0), .p02),
   ((1, 2, 0, 0), .p02), ((1, 2, 1, 0), .p02),
   ((0, 0, 0, 0), .p01), ((0, 0, 1, 0), .p01),
   ((0, 1, 1, 0), .p01), ((0, 1, 2, 0), .p01),
   ((0, 2, 1, 0), .p01), ((0, 2, 2, 0), .p01),
   ((1, 0, 0, 0), .p01), ((1, 0, 2, 0), .p01),
   ((1, 1, 0, 0), .p01), ((1, 1, 2, 0), .p01)]

def sevenCube100To000Surface : List Z4Plaq :=
  [((1, 0, 0, 0), .p12), ((1, 0, 1, 0), .p12),
   ((1, 1, 0, 0), .p12), ((2, 1, 0, 0), .p12),
   ((2, 1, 1, 0), .p12), ((2, 1, 2, 0), .p12),
   ((3, 0, 0, 0), .p12), ((3, 0, 1, 0), .p12),
   ((3, 1, 1, 0), .p12), ((3, 1, 2, 0), .p12),
   ((1, 0, 0, 0), .p02), ((1, 0, 1, 0), .p02),
   ((1, 1, 1, 0), .p02), ((1, 2, 0, 0), .p02),
   ((2, 0, 0, 0), .p02), ((2, 0, 1, 0), .p02),
   ((2, 1, 0, 0), .p02), ((2, 1, 2, 0), .p02),
   ((2, 2, 1, 0), .p02), ((2, 2, 2, 0), .p02),
   ((1, 0, 0, 0), .p01), ((1, 0, 2, 0), .p01),
   ((1, 1, 0, 0), .p01), ((1, 1, 1, 0), .p01),
   ((2, 0, 0, 0), .p01), ((2, 0, 2, 0), .p01),
   ((2, 1, 1, 0), .p01), ((2, 1, 3, 0), .p01)]

def sevenCube000To111Surface : List Z4Plaq :=
  [((0, 0, 0, 0), .p12), ((0, 0, 1, 0), .p12),
   ((0, 1, 0, 0), .p12), ((1, 1, 0, 0), .p12),
   ((1, 1, 1, 0), .p12), ((1, 1, 2, 0), .p12),
   ((2, 0, 0, 0), .p12), ((2, 0, 1, 0), .p12),
   ((2, 1, 1, 0), .p12), ((2, 1, 2, 0), .p12),
   ((0, 0, 0, 0), .p02), ((0, 0, 1, 0), .p02),
   ((0, 1, 1, 0), .p02), ((0, 2, 0, 0), .p02),
   ((1, 0, 0, 0), .p02), ((1, 0, 1, 0), .p02),
   ((1, 1, 0, 0), .p02), ((1, 1, 2, 0), .p02),
   ((1, 2, 1, 0), .p02), ((1, 2, 2, 0), .p02),
   ((0, 0, 0, 0), .p01), ((0, 0, 2, 0), .p01),
   ((0, 1, 0, 0), .p01), ((0, 1, 1, 0), .p01),
   ((1, 0, 0, 0), .p01), ((1, 0, 2, 0), .p01),
   ((1, 1, 1, 0), .p01), ((1, 1, 3, 0), .p01)]

def sevenCube111To011Surface : List Z4Plaq :=
  [((0, 0, 1, 0), .p12), ((0, 1, 0, 0), .p12),
   ((0, 1, 1, 0), .p12), ((1, 0, 0, 0), .p12),
   ((1, 0, 1, 0), .p12), ((2, 1, 0, 0), .p12),
   ((2, 1, 1, 0), .p12), ((3, 0, 0, 0), .p12),
   ((0, 0, 1, 0), .p02), ((0, 1, 0, 0), .p02),
   ((0, 2, 0, 0), .p02), ((0, 2, 1, 0), .p02),
   ((1, 0, 0, 0), .p02), ((1, 1, 1, 0), .p02),
   ((1, 2, 0, 0), .p02), ((1, 2, 1, 0), .p02),
   ((2, 0, 0, 0), .p02), ((2, 1, 0, 0), .p02),
   ((0, 0, 1, 0), .p01), ((0, 0, 2, 0), .p01),
   ((0, 1, 0, 0), .p01), ((0, 1, 2, 0), .p01),
   ((1, 0, 0, 0), .p01), ((1, 0, 1, 0), .p01),
   ((1, 1, 0, 0), .p01), ((1, 1, 2, 0), .p01),
   ((2, 0, 0, 0), .p01), ((2, 0, 1, 0), .p01)]

theorem sevenCubeCycleSurface_lengths :
    sevenCube011To100Surface.length = 28 ∧
    sevenCube100To000Surface.length = 28 ∧
    sevenCube000To111Surface.length = 28 ∧
    sevenCube111To011Surface.length = 28 := by
  decide

theorem sevenCubeCycleSurface_nodups :
    sevenCube011To100Surface.Nodup ∧
    sevenCube100To000Surface.Nodup ∧
    sevenCube000To111Surface.Nodup ∧
    sevenCube111To011Surface.Nodup := by
  unfold sevenCube011To100Surface sevenCube100To000Surface
    sevenCube000To111Surface sevenCube111To011Surface
  simp

/-! ## 2. Exact outward-query truth tables -/

theorem sevenCube011To100_queryFaces :
    (outwardXQueryFace ∉ sevenCube011To100Surface ∧
      outwardYQueryFace ∈ sevenCube011To100Surface ∧
      outwardZQueryFace ∈ sevenCube011To100Surface) ∧
    (outwardXFineQueryFace ∈ sevenCube011To100Surface ∧
      outwardYFineQueryFace ∉ sevenCube011To100Surface ∧
      outwardZFineQueryFace ∉ sevenCube011To100Surface) := by
  unfold sevenCube011To100Surface outwardXQueryFace outwardYQueryFace
    outwardZQueryFace outwardXFineQueryFace outwardYFineQueryFace
    outwardZFineQueryFace
  simp [axisShiftPlaquette, axisShiftVertex, zeroAxisOffset, cubeFace,
    dyadicCell, dyadicVertex]

theorem sevenCube100To000_queryFaces :
    (outwardXQueryFace ∈ sevenCube100To000Surface ∧
      outwardYQueryFace ∉ sevenCube100To000Surface ∧
      outwardZQueryFace ∉ sevenCube100To000Surface) ∧
    (outwardXFineQueryFace ∉ sevenCube100To000Surface ∧
      outwardYFineQueryFace ∉ sevenCube100To000Surface ∧
      outwardZFineQueryFace ∉ sevenCube100To000Surface) := by
  unfold sevenCube100To000Surface outwardXQueryFace outwardYQueryFace
    outwardZQueryFace outwardXFineQueryFace outwardYFineQueryFace
    outwardZFineQueryFace
  simp [axisShiftPlaquette, axisShiftVertex, zeroAxisOffset, cubeFace,
    dyadicCell, dyadicVertex]

theorem sevenCube000To111_queryFaces :
    (outwardXQueryFace ∉ sevenCube000To111Surface ∧
      outwardYQueryFace ∉ sevenCube000To111Surface ∧
      outwardZQueryFace ∉ sevenCube000To111Surface) ∧
    (outwardXFineQueryFace ∈ sevenCube000To111Surface ∧
      outwardYFineQueryFace ∈ sevenCube000To111Surface ∧
      outwardZFineQueryFace ∈ sevenCube000To111Surface) := by
  unfold sevenCube000To111Surface outwardXQueryFace outwardYQueryFace
    outwardZQueryFace outwardXFineQueryFace outwardYFineQueryFace
    outwardZFineQueryFace
  simp [axisShiftPlaquette, axisShiftVertex, zeroAxisOffset, cubeFace,
    dyadicCell, dyadicVertex]

theorem sevenCube111To011_queryFaces :
    (outwardXQueryFace ∈ sevenCube111To011Surface ∧
      outwardYQueryFace ∈ sevenCube111To011Surface ∧
      outwardZQueryFace ∈ sevenCube111To011Surface) ∧
    (outwardXFineQueryFace ∉ sevenCube111To011Surface ∧
      outwardYFineQueryFace ∈ sevenCube111To011Surface ∧
      outwardZFineQueryFace ∈ sevenCube111To011Surface) := by
  unfold sevenCube111To011Surface outwardXQueryFace outwardYQueryFace
    outwardZQueryFace outwardXFineQueryFace outwardYFineQueryFace
    outwardZFineQueryFace
  simp [axisShiftPlaquette, axisShiftVertex, zeroAxisOffset, cubeFace,
    dyadicCell, dyadicVertex]

/-! ## 3. One four-valent link and otherwise bivalent incidence -/

def sevenCube011To100FourLink : Z4Link := ((0, 1, 1, 0), .x0)
def sevenCube100To000FourLink : Z4Link := ((2, 1, 1, 0), .x1)
def sevenCube000To111FourLink : Z4Link := ((1, 1, 1, 0), .x1)
def sevenCube111To011FourLink : Z4Link := ((1, 0, 1, 0), .x1)

theorem sevenCube011To100_four_incidence :
    (geometricIncidentPlaquettes sevenCube011To100Surface
      sevenCube011To100FourLink).length = 4 := by
  decide

theorem sevenCube011To100_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks sevenCube011To100Surface)
    (hne : link ≠ sevenCube011To100FourLink) :
    (geometricIncidentPlaquettes sevenCube011To100Surface link).length = 2 := by
  unfold sevenCube011To100FourLink at hne
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  simp only [sevenCube011To100Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;>
      simp [dirsOf, addE] at hne <;> decide

theorem sevenCube100To000_four_incidence :
    (geometricIncidentPlaquettes sevenCube100To000Surface
      sevenCube100To000FourLink).length = 4 := by
  decide

theorem sevenCube100To000_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks sevenCube100To000Surface)
    (hne : link ≠ sevenCube100To000FourLink) :
    (geometricIncidentPlaquettes sevenCube100To000Surface link).length = 2 := by
  unfold sevenCube100To000FourLink at hne
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  simp only [sevenCube100To000Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;>
      simp [dirsOf, addE] at hne <;> decide

theorem sevenCube000To111_four_incidence :
    (geometricIncidentPlaquettes sevenCube000To111Surface
      sevenCube000To111FourLink).length = 4 := by
  decide

theorem sevenCube000To111_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks sevenCube000To111Surface)
    (hne : link ≠ sevenCube000To111FourLink) :
    (geometricIncidentPlaquettes sevenCube000To111Surface link).length = 2 := by
  unfold sevenCube000To111FourLink at hne
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  simp only [sevenCube000To111Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;>
      simp [dirsOf, addE] at hne <;> decide

theorem sevenCube111To011_four_incidence :
    (geometricIncidentPlaquettes sevenCube111To011Surface
      sevenCube111To011FourLink).length = 4 := by
  decide

theorem sevenCube111To011_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks sevenCube111To011Surface)
    (hne : link ≠ sevenCube111To011FourLink) :
    (geometricIncidentPlaquettes sevenCube111To011Surface link).length = 2 := by
  unfold sevenCube111To011FourLink at hne
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  simp only [sevenCube111To011Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;>
      simp [dirsOf, addE] at hne <;> decide

theorem sevenCubeCycle_fourLinks_mem_touched :
    sevenCube011To100FourLink ∈
        geometricTouchedLinks sevenCube011To100Surface ∧
    sevenCube100To000FourLink ∈
        geometricTouchedLinks sevenCube100To000Surface ∧
    sevenCube000To111FourLink ∈
        geometricTouchedLinks sevenCube000To111Surface ∧
    sevenCube111To011FourLink ∈
        geometricTouchedLinks sevenCube111To011Surface := by
  unfold geometricTouchedLinks sevenCube011To100FourLink
    sevenCube100To000FourLink sevenCube000To111FourLink
    sevenCube111To011FourLink sevenCube011To100Surface
    sevenCube100To000Surface sevenCube000To111Surface
    sevenCube111To011Surface
  decide

/-! ## 4. All four supports lie in the fixed volume-six plaquette box -/

theorem sevenCube011To100Surface_subset_box_six :
    ∀ plaquette, plaquette ∈ sevenCube011To100Surface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  simp only [sevenCube011To100Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem sevenCube100To000Surface_subset_box_six :
    ∀ plaquette, plaquette ∈ sevenCube100To000Surface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  simp only [sevenCube100To000Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem sevenCube000To111Surface_subset_box_six :
    ∀ plaquette, plaquette ∈ sevenCube000To111Surface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  simp only [sevenCube000To111Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem sevenCube111To011Surface_subset_box_six :
    ∀ plaquette, plaquette ∈ sevenCube111To011Surface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  simp only [sevenCube111To011Surface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

#print axioms sevenCubeCycleSurface_lengths
#print axioms sevenCube011To100_queryFaces
#print axioms sevenCube011To100_four_incidence
#print axioms sevenCube011To100_other_incidence_two
#print axioms sevenCube100To000_other_incidence_two
#print axioms sevenCube000To111_other_incidence_two
#print axioms sevenCube111To011_other_incidence_two
#print axioms sevenCubeCycle_fourLinks_mem_touched
#print axioms sevenCube011To100Surface_subset_box_six

end YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
