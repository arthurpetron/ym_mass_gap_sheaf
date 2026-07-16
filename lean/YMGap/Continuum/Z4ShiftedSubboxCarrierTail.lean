/-
# Translation-independent shifted-subbox carrier tails

The existing boundary comparison is phrased for a corner box.  This module
extracts the genuinely translation-independent geometric content needed for
a receding-boundary comparison.  A shifted outer box has lower corner
`lower` and side `inner + 2 * distance`; its protected core has lower corner
`lower + distance` and side `inner`.  Any connected canonical support pinned
in that core and leaving the outer box contains at least `distance + 2`
faces.  Filtering the exact pinned activity sum by this shifted exit event
therefore gives the same derived geometric tail as at the corner.

This closes the carrier-tail half of shifted-subbox stability.  It does not
assert invariance of the finite physical spin weight under an affine shifted
embedding; that separate reindexing is the remaining transport half.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
import YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary

namespace YMGap.Continuum.Z4ShiftedSubboxCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

/-! ## 1. Shifted boxes in the common ambient Nat chart -/

/-- Add the same nonnegative margin to all four coordinates of a lower
corner. -/
def addUniform (lower : Z4Vertex) (margin : Nat) : Z4Vertex :=
  (lower.1 + margin, lower.2.1 + margin,
    lower.2.2.1 + margin, lower.2.2.2 + margin)

/-- Membership of a plaquette base in the half-open shifted box
`[lower, lower + side)^4`. -/
def insideShiftedBoxB (lower : Z4Vertex) (side : Nat)
    (plaquette : Z4Plaq) : Bool :=
  decide
    (vComp lower x0 ≤ cPlaq plaquette x0 ∧
      cPlaq plaquette x0 < vComp lower x0 + side ∧
     vComp lower x1 ≤ cPlaq plaquette x1 ∧
      cPlaq plaquette x1 < vComp lower x1 + side ∧
     vComp lower x2 ≤ cPlaq plaquette x2 ∧
      cPlaq plaquette x2 < vComp lower x2 + side ∧
     vComp lower x3 ≤ cPlaq plaquette x3 ∧
      cPlaq plaquette x3 < vComp lower x3 + side)

/-- Explicit two-sided exit test for a half-open shifted box. -/
def outsideShiftedBoxB (lower : Z4Vertex) (side : Nat)
    (plaquette : Z4Plaq) : Bool :=
  decide
    (cPlaq plaquette x0 < vComp lower x0 ∨
      vComp lower x0 + side ≤ cPlaq plaquette x0 ∨
     cPlaq plaquette x1 < vComp lower x1 ∨
      vComp lower x1 + side ≤ cPlaq plaquette x1 ∨
     cPlaq plaquette x2 < vComp lower x2 ∨
      vComp lower x2 + side ≤ cPlaq plaquette x2 ∨
     cPlaq plaquette x3 < vComp lower x3 ∨
      vComp lower x3 + side ≤ cPlaq plaquette x3)

theorem insideShiftedBoxB_true_iff
    (lower : Z4Vertex) (side : Nat) (plaquette : Z4Plaq) :
    insideShiftedBoxB lower side plaquette = true ↔
      (vComp lower x0 ≤ cPlaq plaquette x0 ∧
        cPlaq plaquette x0 < vComp lower x0 + side ∧
       vComp lower x1 ≤ cPlaq plaquette x1 ∧
        cPlaq plaquette x1 < vComp lower x1 + side ∧
       vComp lower x2 ≤ cPlaq plaquette x2 ∧
        cPlaq plaquette x2 < vComp lower x2 + side ∧
       vComp lower x3 ≤ cPlaq plaquette x3 ∧
        cPlaq plaquette x3 < vComp lower x3 + side) := by
  unfold insideShiftedBoxB
  rw [decide_eq_true_eq]

theorem outsideShiftedBoxB_true_iff
    (lower : Z4Vertex) (side : Nat) (plaquette : Z4Plaq) :
    outsideShiftedBoxB lower side plaquette = true ↔
      (cPlaq plaquette x0 < vComp lower x0 ∨
        vComp lower x0 + side ≤ cPlaq plaquette x0 ∨
       cPlaq plaquette x1 < vComp lower x1 ∨
        vComp lower x1 + side ≤ cPlaq plaquette x1 ∨
       cPlaq plaquette x2 < vComp lower x2 ∨
        vComp lower x2 + side ≤ cPlaq plaquette x2 ∨
       cPlaq plaquette x3 < vComp lower x3 ∨
        vComp lower x3 + side ≤ cPlaq plaquette x3) := by
  unfold outsideShiftedBoxB
  rw [decide_eq_true_eq]

theorem vComp_addUniform (lower : Z4Vertex) (margin : Nat)
    (direction : Dir4) :
    vComp (addUniform lower margin) direction =
      vComp lower direction + margin := by
  obtain ⟨a, b, c, d⟩ := lower
  cases direction <;> rfl

/-! ## 2. Two-sided shifted-shell separation -/

/-- A root in the protected core is at L-infinity distance at least
`distance + 1` from every plaquette outside the outer shifted box. -/
theorem outside_shifted_box_linf_floor
    {lower : Z4Vertex} {inner distance : Nat} {root q : Z4Plaq}
    (hroot : insideShiftedBoxB (addUniform lower distance) inner root = true)
    (hout : outsideShiftedBoxB lower
      (inner + distance + distance) q = true) :
    distance + 1 ≤ linfDist root q := by
  have hr := (insideShiftedBoxB_true_iff
    (addUniform lower distance) inner root).1 hroot
  have ho := (outsideShiftedBoxB_true_iff lower
    (inner + distance + distance) q).1 hout
  simp only [vComp_addUniform] at hr
  rcases ho with h0lo | h0hi | h1lo | h1hi | h2lo | h2hi | h3lo | h3hi
  · have hm := le_linfDist_comp root q x0
    simp only [natDist] at hm
    omega
  · have hm := le_linfDist_comp root q x0
    simp only [natDist] at hm
    omega
  · have hm := le_linfDist_comp root q x1
    simp only [natDist] at hm
    omega
  · have hm := le_linfDist_comp root q x1
    simp only [natDist] at hm
    omega
  · have hm := le_linfDist_comp root q x2
    simp only [natDist] at hm
    omega
  · have hm := le_linfDist_comp root q x2
    simp only [natDist] at hm
    omega
  · have hm := le_linfDist_comp root q x3
    simp only [natDist] at hm
    omega
  · have hm := le_linfDist_comp root q x3
    simp only [natDist] at hm
    omega

/-- Translation-independent size floor for an arbitrary internally connected
cutoff-one face support.  This is the exact geometric statement consumed by
both forward and reverse connected-carrier injections. -/
theorem connectedFaceSupport_shifted_boundary_floor
    {n rootFace : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hconnected : InternallyConnected (faceLinkAdjacentB n) support)
    (hrootFace : rootFace ∈ support)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt n rootFace) = true)
    {exitFace : Nat} (hexitFace : exitFace ∈ support)
    (hexit : outsideShiftedBoxB lower (inner + distance + distance)
      (boxPlaquetteAt n exitFace) = true) :
    distance + 2 ≤ support.length := by
  have hsep := outside_shifted_box_linf_floor hrootCore hexit
  have hfloor := connectedFaceSupport_linf_size_floor
    hsupport hconnected hrootFace
    (List.mem_map.mpr ⟨exitFace, hexitFace, rfl⟩) hsep
  omega

/-- The same shifted-shell floor for an actual canonical surface polymer. -/
theorem canonicalSurfacePolymer_shifted_boundary_floor
    {n rootFace : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hrootFace : rootFace ∈ polymer)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt n rootFace) = true)
    {q : Z4Plaq} (hq : q ∈ geometricPolymer n polymer)
    (hexit : outsideShiftedBoxB lower (inner + distance + distance) q = true) :
    distance + 2 ≤ polymer.length := by
  have hsep := outside_shifted_box_linf_floor hrootCore hexit
  have hfloor := canonicalSurfacePolymer_linf_size_floor
    hpolymer hrootFace hq hsep
  omega

/-! ## 3. Exact shifted-exit activity sums -/

/-- Does the actual geometric support leave a two-sided shifted box? -/
def canonicalPolymerExitsShiftedBoxB
    (n : Nat) (lower : Z4Vertex) (side : Nat)
    (polymer : List Nat) : Bool :=
  (geometricPolymer n polymer).any (outsideShiftedBoxB lower side)

theorem canonicalPolymerExitsShiftedBoxB_implies_reaches
    {n rootFace inner distance : Nat} {lower : Z4Vertex}
    {polymer : List Nat}
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt n rootFace) = true)
    (hexit : canonicalPolymerExitsShiftedBoxB n lower
      (inner + distance + distance) polymer = true) :
    canonicalPolymerReachesB n rootFace (distance + 1) polymer = true := by
  unfold canonicalPolymerExitsShiftedBoxB at hexit
  obtain ⟨q, hq, hout⟩ := List.any_eq_true.mp hexit
  unfold canonicalPolymerReachesB
  exact List.any_eq_true.mpr ⟨q, hq,
    decide_eq_true (outside_shifted_box_linf_floor hrootCore hout)⟩

def canonicalPinnedShiftedExitSizeActivitySum
    (n rootFace : Nat) (lower : Z4Vertex)
    (inner distance size : Nat) : Q' :=
  listQSum (canonicalSurfaceActivity anchorCoupling n)
    ((canonicalPinnedSizePolymers n rootFace size).filter
      (canonicalPolymerExitsShiftedBoxB n lower
        (inner + distance + distance)))

theorem canonicalPinnedShiftedExitSizeActivitySum_le_reach
    {n rootFace inner distance size : Nat} {lower : Z4Vertex}
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt n rootFace) = true) :
    canonicalPinnedShiftedExitSizeActivitySum
        n rootFace lower inner distance size ≤
      canonicalPinnedReachSizeActivitySum
        n rootFace (distance + 1) size := by
  unfold canonicalPinnedShiftedExitSizeActivitySum
    canonicalPinnedReachSizeActivitySum
    canonicalPinnedReachSizePolymers
  exact listQSum_filter_le_filter _ _ _
    (canonicalSurfacePolymer_activity_nonnegative n)
    (fun polymer hexit =>
      canonicalPolymerExitsShiftedBoxB_implies_reaches
        hrootCore hexit)
    (canonicalPinnedSizePolymers n rootFace size)

def canonicalPinnedShiftedExitSizeWeightedActivity
    (n rootFace : Nat) (lower : Z4Vertex)
    (inner distance size : Nat) : Q' :=
  canonicalPinnedShiftedExitSizeActivitySum
      n rootFace lower inner distance size *
    eSurrogate ^ size

theorem canonicalPinnedShiftedExitSizeWeightedActivity_le_reach
    {n rootFace inner distance size : Nat} {lower : Z4Vertex}
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt n rootFace) = true) :
    canonicalPinnedShiftedExitSizeWeightedActivity
        n rootFace lower inner distance size ≤
      canonicalPinnedReachSizeWeightedActivity
        n rootFace (distance + 1) size := by
  unfold canonicalPinnedShiftedExitSizeWeightedActivity
    canonicalPinnedReachSizeWeightedActivity
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (canonicalPinnedShiftedExitSizeActivitySum_le_reach hrootCore)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

def canonicalPinnedShiftedExitTruncatedKPSum
    (n rootFace : Nat) (lower : Z4Vertex)
    (inner distance sizeCutoff : Nat) : Q' :=
  finSum (fun size =>
    canonicalPinnedShiftedExitSizeWeightedActivity
      n rootFace lower inner distance size) sizeCutoff

/-- Exact, uniform and fully derived geometric tail for a protected core in
an arbitrary shifted subbox.  The constant and ratio are the existing exact
rationals; no measured input enters. -/
theorem canonicalPinnedShiftedExitTruncatedKPSum_le_boundaryTail
    {n rootFace inner distance sizeCutoff : Nat} {lower : Z4Vertex}
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt n rootFace) = true) :
    canonicalPinnedShiftedExitTruncatedKPSum
        n rootFace lower inner distance sizeCutoff ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ (distance + 2) := by
  unfold canonicalPinnedShiftedExitTruncatedKPSum
  have hsum :
      finSum (fun size =>
          canonicalPinnedShiftedExitSizeWeightedActivity
            n rootFace lower inner distance size) sizeCutoff ≤
        canonicalPinnedReachTruncatedKPSum
          n rootFace (distance + 1) sizeCutoff :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun size =>
        canonicalPinnedShiftedExitSizeWeightedActivity_le_reach hrootCore)
      sizeCutoff
  have htail := canonicalPinnedReachTruncatedKPSum_le_boundaryTail
    n rootFace (distance + 1) sizeCutoff
  have hindex : distance + 1 + 1 = distance + 2 := by omega
  rw [hindex] at htail
  exact Q'.le_trans' _ _ _ hsum htail

/-! ## 4. Corner compatibility and non-vacuity -/

/-- At lower corner zero, shifted membership is exactly the old corner-box
membership predicate.  This shows the new shell strictly generalizes rather
than replaces the proved corner estimate. -/
theorem insideShiftedBoxB_zero_iff_mem
    (side : Nat) (plaquette : Z4Plaq) :
    insideShiftedBoxB (0, 0, 0, 0) side plaquette = true ↔
      plaquette ∈ boxPlaquettes side := by
  rw [insideShiftedBoxB_true_iff, mem_boxPlaquettes]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp [vComp, cPlaq]

#print axioms insideShiftedBoxB_true_iff
#print axioms outsideShiftedBoxB_true_iff
#print axioms vComp_addUniform
#print axioms outside_shifted_box_linf_floor
#print axioms connectedFaceSupport_shifted_boundary_floor
#print axioms canonicalSurfacePolymer_shifted_boundary_floor
#print axioms canonicalPolymerExitsShiftedBoxB_implies_reaches
#print axioms canonicalPinnedShiftedExitSizeActivitySum_le_reach
#print axioms canonicalPinnedShiftedExitSizeWeightedActivity_le_reach
#print axioms canonicalPinnedShiftedExitTruncatedKPSum_le_boundaryTail
#print axioms insideShiftedBoxB_zero_iff_mem

end YMGap.Continuum.Z4ShiftedSubboxCarrierTail
