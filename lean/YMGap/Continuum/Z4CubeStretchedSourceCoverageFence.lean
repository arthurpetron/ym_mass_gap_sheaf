/-
# The stretched cube source does not cover all physical fine supports

The all-cutoff adjacent-cube kernel is normalized on
`CubeStretchedCompatibleSource`: the four fine spins above each of the six
coarse faces may vary, but their six totals must be one common number.  This
condition supplies a positive stretched-channel witness; it was never proved
to follow from physical fine-link closure.

Here the elementary fine unit-cube boundary gives an exact counterexample.
It is a closed six-face spin foam with strictly positive cutoff-one physical
activity.  Relative to the dyadic coarse cube, however, it meets the bottom
coarse face once and the top coarse face zero times.  Hence no
`CubeStretchedCompatibleSource 1` can have all six packets induced by this
single physical fine spin field.

Therefore the restricted adjacent kernel cannot be tiled into the whole
corrected slab merely by adding a global projector.  The next constructor
must accept general physical face packets and obtain positivity from the
global fine intertwiner witness (equivalently, retain the full fine auxiliary
channels through recoupling).

## Axiom gate

Exact finite geometry and rational positivity only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.Z4AdjacentCubeJointConditionalKernel
import YMGap.Continuum.Z4AxisCubeSixFaceActivity

namespace YMGap.Continuum.Z4CubeStretchedSourceCoverageFence

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One closed physical fine field -/

/-- Translation placing the two horizontal faces in one nondegenerate
dyadic packet while leaving the other four faces in degenerate slots. -/
def lowerOddFineCubeOffset : AxisOffset := ⟨1, 1, 0, 0⟩

/-- Indicator of the six plaquettes bounding the fine unit cube based at
`(1,1,0,0)`.  Structural recursion keeps the carrier computational. -/
def originUnitCubeFineFaceB : Z4Plaq → Bool
  | ((1, 1, 0, 0), .p01) => true
  | ((1, 1, 1, 0), .p01) => true
  | ((1, 1, 0, 0), .p02) => true
  | ((1, 2, 0, 0), .p02) => true
  | ((1, 1, 0, 0), .p12) => true
  | ((2, 1, 0, 0), .p12) => true
  | _ => false

def originUnitCubeFineSpin (plaquette : Z4Plaq) : Nat :=
  match originUnitCubeFineFaceB plaquette with
  | true => 1
  | false => 0

theorem originUnitCubeFineSpin_bounded (plaquette : Z4Plaq) :
    originUnitCubeFineSpin plaquette ≤ 1 := by
  unfold originUnitCubeFineSpin
  cases hface : originUnitCubeFineFaceB plaquette <;> simp

/-- The geometric support of the field, as a translated unit-cube boundary. -/
def lowerOddFineCubeSurface : List Z4Plaq :=
  axisCubeSurface lowerOddFineCubeOffset

/-- The support is physically closed: every touched lattice link meets
exactly two excited plaquettes. -/
theorem originUnitCubeFineSpin_closed
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks lowerOddFineCubeSurface) :
    (geometricIncidentPlaquettes lowerOddFineCubeSurface link).length = 2 :=
  axisCubeSurface_incidentPlaquettes_length_eq_two
    lowerOddFineCubeOffset hlink

/-- Canonical numerical encoding of the same closed carrier. -/
def lowerOddFineCubeSupportIds : List Nat :=
  geometricSupportIds 6 lowerOddFineCubeSurface

theorem lowerOddFineCubeSupportIds_mem :
    lowerOddFineCubeSupportIds ∈ cutoffOneFaceSupports 6 :=
  geometricSupportIds_mem_cutoffOneFaceSupports
    6 lowerOddFineCubeSurface

theorem lowerOddFineCubeSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ lowerOddFineCubeSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  unfold lowerOddFineCubeSurface axisCubeSurface at hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  apply boxPlaquettes_mono (n := 4) (m := 6) (by omega)
  exact axisShiftPlaquette_mem_extended_box lowerOddFineCubeOffset
    (unitCubeSurface_mem_box (by omega) hsource)

theorem lowerOddFineCubeSupportIds_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 lowerOddFineCubeSupportIds)
      lowerOddFineCubeSurface :=
  geometricSupportIds_sameSupport
    lowerOddFineCubeSurface_subset_box_six

theorem lowerOddFineCubeSupportIds_length :
    lowerOddFineCubeSupportIds.length = 6 := by
  have hlength := sameSupport_length_eq_of_nodup
    lowerOddFineCubeSupportIds_sameSupport
    (geometricPolymer_nodup lowerOddFineCubeSupportIds_mem)
    (axisCubeSurface_nodup lowerOddFineCubeOffset)
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength.trans (axisCubeSurface_length lowerOddFineCubeOffset)

theorem lowerOddFineCubeRoot_incidence_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 6
      (componentLabel lowerOddFineCubeSupportIds)) :
    (geometricIncidentPlaquettes
      (geometricPolymer 6 lowerOddFineCubeSupportIds) link).length = 2 := by
  have hsurfaceTouched :
      link ∈ geometricTouchedLinks lowerOddFineCubeSurface :=
    touchedSurface_of_sameSupport lowerOddFineCubeSupportIds_mem
      lowerOddFineCubeSupportIds_sameSupport hlink
  have hsame := geometricIncidentPlaquettes_sameSupport
    lowerOddFineCubeSupportIds_sameSupport link
  have hlength := sameSupport_length_eq_of_nodup hsame
    (geometricIncidentPlaquettes_nodup
      lowerOddFineCubeSupportIds_mem link)
    (by
      unfold geometricIncidentPlaquettes lowerOddFineCubeSurface
      exact List.filter_sublist.nodup
        (axisCubeSurface_nodup lowerOddFineCubeOffset))
  exact hlength.trans
    (axisCubeSurface_incidentPlaquettes_length_eq_two
      lowerOddFineCubeOffset hsurfaceTouched)

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

/-- The same closed geometric carrier is an actual strictly positive
cutoff-one physical spin-foam summand. -/
theorem originUnitCubePhysicalSummand_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') <
      canonicalSurfaceActivity coupling 6
        lowerOddFineCubeSupportIds := by
  have hcoefficient : (0 : Q') < coeffW coupling 1 :=
    coeffW_pos hcoupling 1
  have hpower := qpow_pos_local hcoefficient 6
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv
      (canonicalSurfaceActivity_eqv_pow_six_of_incidence_two
        coupling lowerOddFineCubeSupportIds_mem
        lowerOddFineCubeSupportIds_length
        lowerOddFineCubeRoot_incidence_two))

/-! ## 2. Its dyadic coarse-face totals are not stretched -/

theorem originUnitCube_bottom_packet :
    dyadicFaceSpinPacket originUnitCubeFineSpin
        (cubeFace .bottomXY) = ⟨1, 1, 0, 0⟩ := by
  decide

theorem originUnitCube_top_packet :
    dyadicFaceSpinPacket originUnitCubeFineSpin
        (cubeFace .topXY) = ⟨0, 0, 0, 0⟩ := by
  rfl

theorem originUnitCube_bottom_total :
    faceSpinTotal
        (dyadicFaceSpinPacket originUnitCubeFineSpin
          (cubeFace .bottomXY)) = 2 := by
  rw [originUnitCube_bottom_packet]
  rfl

theorem originUnitCube_top_total :
    faceSpinTotal
        (dyadicFaceSpinPacket originUnitCubeFineSpin
          (cubeFace .topXY)) = 0 := by
  rw [originUnitCube_top_packet]
  rfl

/-- No stretched source row is induced by this positive physical fine field.
The obstruction already appears between the bottom and top face totals. -/
theorem originUnitCube_not_covered_by_stretched_source
    (source : CubeStretchedCompatibleSource 1) :
    ¬ ∀ face,
      (source.packet face).val =
        dyadicFaceSpinPacket originUnitCubeFineSpin (cubeFace face) := by
  intro hcovered
  have hbottomPacket := congrArg faceSpinTotal (hcovered .bottomXY)
  have htopPacket := congrArg faceSpinTotal (hcovered .topXY)
  have hbottomCommon := source.total_eq .bottomXY
  have htopCommon := source.total_eq .topXY
  rw [originUnitCube_bottom_total] at hbottomPacket
  rw [originUnitCube_top_total] at htopPacket
  omega

end YMGap.Continuum.Z4CubeStretchedSourceCoverageFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CubeStretchedSourceCoverageFence.originUnitCubeFineSpin_bounded
#print axioms YMGap.Continuum.Z4CubeStretchedSourceCoverageFence.originUnitCubeFineSpin_closed
#print axioms YMGap.Continuum.Z4CubeStretchedSourceCoverageFence.originUnitCubePhysicalSummand_pos
#print axioms YMGap.Continuum.Z4CubeStretchedSourceCoverageFence.originUnitCube_bottom_packet
#print axioms YMGap.Continuum.Z4CubeStretchedSourceCoverageFence.originUnitCube_top_packet
#print axioms YMGap.Continuum.Z4CubeStretchedSourceCoverageFence.originUnitCube_not_covered_by_stretched_source
