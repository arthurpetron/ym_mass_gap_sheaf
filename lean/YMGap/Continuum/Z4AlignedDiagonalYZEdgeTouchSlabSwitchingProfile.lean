/-
# Production profile of the aligned diagonal cut carrier

Embed the aligned twelve-face diagonal carrier in the corrected slab of
extent five.  Its unique cut link has physical word `[1,1,1,1,0]`; every
other link has a sparse binary word of total zero or two.  In parallel, the
component tags at the pivot are `[near,near,far,far,vacuum]`, so the written
SU(2) left carrier `(0,1)` is the component-preserving target.

Constructive contract: literal finite geometry and the production binary
support encoding only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. Exact slab embedding -/

abbrev alignedDiagonalSwitchSurface : List Z4Plaq :=
  alignedDiagonalYZSurface

abbrev alignedDiagonalSwitchPivot : Z4Link := alignedDiagonalYZPivot

theorem alignedDiagonalSwitchSurface_subset_slab_five :
    forall plaquette, plaquette ∈ alignedDiagonalSwitchSurface ->
      plaquette ∈ boundaryCompleteSlabPlaquettes 5 := by
  intro plaquette hplaquette
  rw [mem_boundaryCompleteSlabPlaquettes]
  simp only [alignedDiagonalSwitchSurface, alignedDiagonalYZSurface,
    alignedDiagonalNearSurface, alignedDiagonalFarSurface,
    alignedDiagonalYZOffset, axisCubeSurface, unitCubeSurface,
    List.map, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hplaquette
  rcases hplaquette with hnear | hfar
  · rcases hnear with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · rcases hfar with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem alignedDiagonalSwitchSurface_nodup :
    alignedDiagonalSwitchSurface.Nodup :=
  alignedDiagonalYZSurface_nodup

theorem alignedDiagonalSwitchSurface_evenFaceIncidence :
    EvenFaceIncidence alignedDiagonalSwitchSurface :=
  alignedDiagonalYZSurface_evenFaceIncidence

/-! ## 2. Sparse nonpivot words and the aligned pivot word -/

theorem alignedDiagonalSwitch_nonpivot_sparseFundamentalWord
    (link : Z4Link) (hne : link ≠ alignedDiagonalSwitchPivot) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 alignedDiagonalSwitchSurface) link) :=
  slabBinarySupport_sparseFundamentalWord
    alignedDiagonalSwitchSurface_subset_slab_five
    alignedDiagonalSwitchSurface_nodup
    alignedDiagonalSwitchSurface_evenFaceIncidence link
    (alignedDiagonal_other_faceIncidenceCount_le_two link hne)

theorem alignedDiagonalSwitchPivot_degree_five :
    (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).length = 5 := by
  decide

theorem alignedDiagonalSwitchPivot_spinList :
    (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).map
        (slabBinarySupportLabelling 5 alignedDiagonalSwitchSurface) =
      [1, 1, 1, 1, 0] := by
  decide

theorem alignedDiagonalSwitchPivot_componentTagList :
    (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).map
        alignedDiagonalComponentTag = [1, 1, 2, 2, 0] :=
  alignedDiagonalPivot_componentTagList

theorem alignedDiagonalSwitchPivot_localExternalSpinSum :
    localExternalSpinSum
      (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).length
      (slabLinkExternalSpins 5
        (slabBinarySupportLabelling 5 alignedDiagonalSwitchSurface)
        alignedDiagonalSwitchPivot) = 4 := by
  unfold slabLinkExternalSpins
  rw [slabBinarySupport_localExternalSpinSum
    alignedDiagonalSwitchSurface_subset_slab_five
    alignedDiagonalSwitchSurface_nodup alignedDiagonalSwitchPivot]
  exact alignedDiagonalPivot_faceIncidenceCount

#print axioms alignedDiagonalSwitchSurface_subset_slab_five
#print axioms alignedDiagonalSwitch_nonpivot_sparseFundamentalWord
#print axioms alignedDiagonalSwitchPivot_degree_five
#print axioms alignedDiagonalSwitchPivot_spinList
#print axioms alignedDiagonalSwitchPivot_componentTagList
#print axioms alignedDiagonalSwitchPivot_localExternalSpinSum

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
