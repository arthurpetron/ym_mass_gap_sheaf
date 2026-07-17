/-
# No translated six-face cube realizes the missing `100 → 111` edge

The distinguished x and y fine queries are plaquettes on incompatible
translated unit-cube boundaries.  Consequently no literal six-face axis cube
can contain all three fine queries, independently of its coarse pattern.
This permanently rules out the smallest equal-activity carrier family.
-/

import YMGap.Continuum.Z4OutwardCentralSmallLiftSignedPath

namespace YMGap.Continuum.Z4OutwardFine111AxisCubeObstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-- Even the x and y distinguished fine faces cannot lie on one translated
six-face unit cube. -/
theorem outwardFineXYQueryFaces_not_both_mem_axisCubeSurface
    (offset : AxisOffset) :
    ¬ (outwardXFineQueryFace ∈ axisCubeSurface offset ∧
      outwardYFineQueryFace ∈ axisCubeSurface offset) := by
  rintro ⟨hx, hy⟩
  simp [outwardXFineQueryFace, outwardYFineQueryFace,
    axisCubeSurface, unitCubeSurface, axisShiftPlaquette,
    axisShiftVertex, zeroAxisOffset, cubeFace, dyadicCell,
    dyadicVertex] at hx hy
  omega

theorem outwardFineXYZQueryFaces_not_all_mem_axisCubeSurface
    (offset : AxisOffset) :
    ¬ (outwardXFineQueryFace ∈ axisCubeSurface offset ∧
      outwardYFineQueryFace ∈ axisCubeSurface offset ∧
      outwardZFineQueryFace ∈ axisCubeSurface offset) := by
  rintro ⟨hx, hy, _⟩
  exact outwardFineXYQueryFaces_not_both_mem_axisCubeSurface offset ⟨hx, hy⟩

#print axioms outwardFineXYQueryFaces_not_both_mem_axisCubeSurface
#print axioms outwardFineXYZQueryFaces_not_all_mem_axisCubeSurface

end YMGap.Continuum.Z4OutwardFine111AxisCubeObstruction
