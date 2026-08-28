/-
# Production profile of the outward Y/Z one-link cut carrier

Embed the certified twelve-face edge-touch carrier into the corrected slab of
extent five.  Its unique cut link carries the exact production word
`[1,1,1,1,0]`; every other link carries a sparse binary word of total zero or
two.  This is the geometry-to-recoupling interface required before selecting
the two alternative pivot pairings.

Constructive contract: literal finite geometry and the production binary
support encoding only; no choice, `native_decide`, unchecked existence claim,
or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
import YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. The selected production support -/

abbrev outwardYZSwitchSurface : List Z4Plaq := outwardYZSurface

abbrev outwardYZSwitchPivot : Z4Link := outwardYZCutPivot

theorem outwardYZSwitchSurface_subset_slab_five :
    forall plaquette, plaquette ∈ outwardYZSwitchSurface ->
      plaquette ∈ boundaryCompleteSlabPlaquettes 5 := by
  intro plaquette hplaquette
  rw [mem_boundaryCompleteSlabPlaquettes]
  constructor
  · exact outwardYZSurface_subset_box_six plaquette hplaquette
  · simp only [outwardYZSwitchSurface, outwardYZSurface,
      outwardYSurface, outwardZSurface, axisCubeSurface,
      unitCubeSurface, List.map, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with hY | hZ
    · rcases hY with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · rcases hZ with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide

theorem outwardYZSwitchSurface_nodup : outwardYZSwitchSurface.Nodup :=
  outwardYZSurface_nodup

theorem outwardYZSwitchSurface_evenFaceIncidence :
    EvenFaceIncidence outwardYZSwitchSurface :=
  outwardYZSurface_evenFaceIncidence

/-! ## 2. Sparse nonpivot words and the exact pivot word -/

/-- Every nonpivot production link has a binary external word of total zero
or two. -/
theorem outwardYZSwitch_nonpivot_sparseFundamentalWord
    (link : Z4Link) (hne : link ≠ outwardYZSwitchPivot) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 outwardYZSwitchSurface) link) :=
  slabBinarySupport_sparseFundamentalWord
    outwardYZSwitchSurface_subset_slab_five
    outwardYZSwitchSurface_nodup
    outwardYZSwitchSurface_evenFaceIncidence link
    (outwardYZ_other_faceIncidenceCount_le_two link hne)

/-- The spatial cut link has four selected physical faces and one additional
vacuum slab face-coordinate. -/
theorem outwardYZSwitchPivot_degree_five :
    (slabIncidentPlaqIds 5 outwardYZSwitchPivot).length = 5 := by
  decide

/-- In corrected-slab face order, the four selected faces precede the extra
vacuum coordinate. -/
theorem outwardYZSwitchPivot_spinList :
    (slabIncidentPlaqIds 5 outwardYZSwitchPivot).map
        (slabBinarySupportLabelling 5 outwardYZSwitchSurface) =
      [1, 1, 1, 1, 0] := by
  decide

theorem outwardYZSwitchPivot_localExternalSpinSum :
    localExternalSpinSum
      (slabIncidentPlaqIds 5 outwardYZSwitchPivot).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 outwardYZSwitchSurface)
        outwardYZSwitchPivot) = 4 := by
  unfold slabLinkExternalSpins
  rw [slabBinarySupport_localExternalSpinSum
    outwardYZSwitchSurface_subset_slab_five
    outwardYZSwitchSurface_nodup outwardYZSwitchPivot]
  exact outwardYZCutPivot_faceIncidenceCount

#print axioms outwardYZSwitchSurface_subset_slab_five
#print axioms outwardYZSwitch_nonpivot_sparseFundamentalWord
#print axioms outwardYZSwitchPivot_degree_five
#print axioms outwardYZSwitchPivot_spinList
#print axioms outwardYZSwitchPivot_localExternalSpinSum

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
