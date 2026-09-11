/-
# Canonical reflected dyadic geometry for the positive-time observable

The abstract selected-face compiler asks for two incidence witnesses.  This
module constructs them for the canonical bottom spatial coarse face.  The
selected fine face is the first dyadic child `((1,1,0,0), p01)`.  Its
reflection is the last child of the reflected coarse packet because the
boundary-complete fine extent is exactly `2 * coarse.extent + 1`.

This closes the coordinate bridge from the literal same-object
positive-time observable to the strict packet estimate.  It remains a
finite-volume, cutoff-one, anchor-coupling bridge; no scaling uniformity or
completed OS gap is asserted here.

Constructive contract: explicit corrected-slab indexing, finite list
membership, and natural-number arithmetic only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, trusted
external computation, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeSelectedFaceDyadicIncidence
import YMGap.Continuum.CompactDualSlabObservableFaceRecedingVolumeClustering

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCanonicalDyadicGeometry

set_option autoImplicit false
set_option maxRecDepth 100000

open ClusterCount4DProgress
open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeSelectedFaceDyadicIncidence
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabObservableFaceRecedingVolumeClustering
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The canonical fine child -/

/-- First dyadic child of the bottom spatial coarse plaquette. -/
def bottomDyadicFinePlaquette : Z4Plaq :=
  ((1, 1, 0, 0), .p01)

private theorem fineExtent_pos_local (S : SlabScalePair) :
    0 < S.fine.extent := by
  rw [S.fine_extent]
  unfold dyadicSlabFineExtent
  omega

private theorem bottomDyadicFinePlaquette_mem_box_local
    (S : SlabScalePair) :
    bottomDyadicFinePlaquette ∈ boxPlaquettes (S.fine.extent + 1) := by
  rw [mem_boxPlaquettes]
  change
    1 < S.fine.extent + 1 ∧
      1 < S.fine.extent + 1 ∧
      0 < S.fine.extent + 1 ∧
      0 < S.fine.extent + 1
  have hfineExtent := fineExtent_pos_local S
  have hone : 1 ≤ S.fine.extent := hfineExtent
  have honeLt : 1 < S.fine.extent + 1 := Nat.lt_succ_of_le hone
  have hzeroLt : 0 < S.fine.extent + 1 := Nat.zero_lt_succ _
  exact ⟨honeLt, honeLt, hzeroLt, hzeroLt⟩

private theorem bottomDyadicFinePlaquette_timeAdmissible_local
    (S : SlabScalePair) :
    plaquetteTimeAdmissible S.fine.extent
      bottomDyadicFinePlaquette := by
  unfold plaquetteTimeAdmissible bottomDyadicFinePlaquette
  exact Nat.zero_le _

/-- The canonical fine child is present in every fine corrected slab arising
in a slab scale pair. -/
theorem bottomDyadicFinePlaquette_mem_fineSlab (S : SlabScalePair) :
    bottomDyadicFinePlaquette ∈
      boundaryCompleteSlabPlaquettes S.fine.extent := by
  rw [mem_boundaryCompleteSlabPlaquettes]
  exact ⟨bottomDyadicFinePlaquette_mem_box_local S,
    bottomDyadicFinePlaquette_timeAdmissible_local S⟩

/-- Physical identifier of the canonical fine child. -/
def canonicalBottomDyadicFineFaceId (S : SlabScalePair) : Nat :=
  slabFaceIdOfPlaquette S.fine.extent bottomDyadicFinePlaquette

theorem canonicalBottomDyadicFineFaceId_physical (S : SlabScalePair) :
    canonicalBottomDyadicFineFaceId S ∈ S.fine.faceEdges := by
  unfold canonicalBottomDyadicFineFaceId SlabPhysicalData.faceEdges
  exact slabFaceIdOfPlaquette_physical
    (bottomDyadicFinePlaquette_mem_fineSlab S)

@[simp] theorem slabPlaquetteAt_canonicalBottomDyadicFineFaceId
    (S : SlabScalePair) :
    slabPlaquetteAt S.fine.extent
        (canonicalBottomDyadicFineFaceId S) =
      bottomDyadicFinePlaquette := by
  unfold canonicalBottomDyadicFineFaceId
  exact slabPlaquetteAt_faceIdOfPlaquette
    (bottomDyadicFinePlaquette_mem_fineSlab S)

theorem canonicalBottomDyadicFineFaceId_lower (S : SlabScalePair) :
    canonicalBottomDyadicFineFaceId S ∈
      centralLowerFaceIds S.fine.half := by
  rw [mem_centralLowerFaceIds]
  constructor
  · simpa only [SlabPhysicalData.extent] using
      canonicalBottomDyadicFineFaceId_physical S
  · change plaquetteHalfSide S.fine.half
      (slabPlaquetteAt S.fine.extent
        (canonicalBottomDyadicFineFaceId S)) = .lower
    rw [slabPlaquetteAt_canonicalBottomDyadicFineFaceId]
    simp [bottomDyadicFinePlaquette, plaquetteHalfSide,
      spatialHalfSide]

/-! ## 2. Root and reflected packet incidence -/

theorem canonicalBottomDyadicFineFaceId_mem_rootPacket
    (S : SlabScalePair) :
    canonicalBottomDyadicFineFaceId S ∈
      dyadicCoarseFaceFineFaceIds S
        (centralBottomSpatialFaceId S.coarse.half) := by
  unfold dyadicCoarseFaceFineFaceIds
  rw [show S.coarse.extent = centralExtent S.coarse.half by rfl]
  rw [slabPlaquetteAt_centralBottomSpatialFaceId]
  simp [bottomSpatialPlaquette, dyadicFacePreimages,
    canonicalBottomDyadicFineFaceId, bottomDyadicFinePlaquette]

/-- Reflection of the chosen fine child is the last child in the dyadic
packet over the reflected canonical coarse root. -/
theorem canonicalBottomDyadicFineFaceId_reflected_mem_packet
    (S : SlabScalePair) :
    slabFaceReflectId S.fine.extent
        (canonicalBottomDyadicFineFaceId S) ∈
      dyadicCoarseFaceFineFaceIds S
        (slabFaceReflectId S.coarse.extent
          (centralBottomSpatialFaceId S.coarse.half)) := by
  have hcoarsePhysical :
      centralBottomSpatialFaceId S.coarse.half ∈
        slabPhysicalFaceEdges S.coarse.extent := by
    simpa only [SlabPhysicalData.extent] using
      centralBottomSpatialFaceId_physical S.coarse.half
  unfold dyadicCoarseFaceFineFaceIds
  rw [slabPlaquetteAt_slabFaceReflectId hcoarsePhysical]
  rw [show S.coarse.extent = centralExtent S.coarse.half by rfl]
  rw [slabPlaquetteAt_centralBottomSpatialFaceId]
  unfold slabFaceReflectId canonicalBottomDyadicFineFaceId
  rw [slabPlaquetteAt_faceIdOfPlaquette
    (bottomDyadicFinePlaquette_mem_fineSlab S)]
  rw [S.fine_extent]
  rw [show S.coarse.extent = centralExtent S.coarse.half by rfl]
  simp [bottomSpatialPlaquette, bottomDyadicFinePlaquette,
    dyadicFacePreimages, timeReflectPlaquette,
    dyadicSlabFineExtent, slabFaceIdOfPlaquette]

/-! ## 3. The canonical inhabited incidence bundle -/

def canonicalBottomDyadicEnrichedLowerFaceGeometry
    (S : SlabScalePair) : DyadicEnrichedLowerFaceGeometry S where
  base := {
    fineRoot := canonicalBottomDyadicFineFaceId S
    coarseRoot := centralBottomSpatialFaceId S.coarse.half
    fineRoot_lower := canonicalBottomDyadicFineFaceId_lower S
    coarseRoot_lower := centralBottomSpatialFaceId_lower S.coarse.half
  }
  fineRoot_mem_packet :=
    canonicalBottomDyadicFineFaceId_mem_rootPacket S
  fineReflected_mem_packet :=
    canonicalBottomDyadicFineFaceId_reflected_mem_packet S

/-! ## 4. Unconditional canonical strict-defect endpoints -/

theorem canonicalBottomEnrichedLowerPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedLowerPositiveTimeDefectAverage S
        (canonicalBottomDyadicEnrichedLowerFaceGeometry S).base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact enrichedLowerPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    S cutoff half (canonicalBottomDyadicEnrichedLowerFaceGeometry S)
    hfine hfineCutoff

theorem canonicalBottomEnrichedReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedReflectedPositiveTimeDefectAverage S
        (canonicalBottomDyadicEnrichedLowerFaceGeometry S).base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact enrichedReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    S cutoff half (canonicalBottomDyadicEnrichedLowerFaceGeometry S)
    hfine hfineCutoff

theorem canonicalBottomEnrichedLowerReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedLowerReflectedPositiveTimeDefectAverage S
        (canonicalBottomDyadicEnrichedLowerFaceGeometry S).base ≤
      Q'.mkPos 256 425 (by decide) := by
  exact enrichedLowerReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
    S cutoff half (canonicalBottomDyadicEnrichedLowerFaceGeometry S)
    hfine hfineCutoff

#print axioms bottomDyadicFinePlaquette_mem_fineSlab
#print axioms canonicalBottomDyadicFineFaceId_mem_rootPacket
#print axioms canonicalBottomDyadicFineFaceId_reflected_mem_packet
#print axioms canonicalBottomDyadicEnrichedLowerFaceGeometry
#print axioms canonicalBottomEnrichedLowerPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
#print axioms canonicalBottomEnrichedReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive
#print axioms canonicalBottomEnrichedLowerReflectedPositiveTimeDefectAverage_le_twoFiftySixFourTwentyFive

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCanonicalDyadicGeometry
