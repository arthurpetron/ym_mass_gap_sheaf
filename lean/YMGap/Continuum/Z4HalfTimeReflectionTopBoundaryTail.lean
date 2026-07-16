/-
# Time-directed carrier tail for the corrected reflection slab

The corrected slab omits exactly the top layer of temporal plaquettes from
its ambient corner box.  The reflected central cube stays a distance growing
with `half` from that layer, even though it is not separated from the spatial
walls.  This file records the resulting anisotropic L-infinity separation and
feeds it into the already proved canonical pinned-polymer tail.

This is a finite-volume boundary estimate.  It does not by itself identify
the normalized supported ambient ensemble with the full ambient law; that
requires the connected-component switching comparison built on this tail.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

/-! ## 1. Exact classification of the omitted ambient faces -/

/-- A plaquette of the ambient box that is absent from the corrected slab has
base time exactly `extent`.  Spatial plaquettes on that slice are retained,
so the omitted faces are necessarily temporal; the time equality is the
load-bearing part needed below. -/
theorem ambient_nonSlab_time_eq_extent
    {extent : Nat} {plaquette : Z4Plaq}
    (hbox : plaquette ∈ boxPlaquettes (extent + 1))
    (hnot : plaquette ∉ boundaryCompleteSlabPlaquettes extent) :
    plaquette.1.2.2.2 = extent := by
  have htime := (mem_boxPlaquettes plaquette (extent + 1)).1 hbox |>.2.2.2
  have hnotAdmissible : ¬ plaquetteTimeAdmissible extent plaquette := by
    intro hadmissible
    exact hnot ((mem_boundaryCompleteSlabPlaquettes extent plaquette).2
      ⟨hbox, hadmissible⟩)
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change d < extent + 1 at htime
  cases plane with
  | p01 =>
      change ¬ d ≤ extent at hnotAdmissible
      change d = extent
      omega
  | p02 =>
      change ¬ d ≤ extent at hnotAdmissible
      change d = extent
      omega
  | p03 =>
      change ¬ d < extent at hnotAdmissible
      change d = extent
      omega
  | p12 =>
      change ¬ d ≤ extent at hnotAdmissible
      change d = extent
      omega
  | p13 =>
      change ¬ d < extent at hnotAdmissible
      change d = extent
      omega
  | p23 =>
      change ¬ d < extent at hnotAdmissible
      change d = extent
      omega

/-- Consequently every identifier in the literal ambient complement decodes
to the top time slice. -/
theorem ambientNonSlabFaceId_time_eq_extent
    {extent id : Nat} (hid : id ∈ ambientNonSlabFaceIds extent) :
    (boxPlaquetteAt (extent + 1) id).1.2.2.2 = extent := by
  have hparts := (mem_ambientNonSlabFaceIds_iff extent id).1 hid
  exact ambient_nonSlab_time_eq_extent
    (boxPlaquetteAt_mem_boxPlaquettes_of_physical hparts.1) hparts.2

/-! ## 2. The two central roots and time-directed separation -/

theorem centralLowerCubeRoot_face_time
    {half rootId : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralLowerCubeRoot half) :
    (boxPlaquetteAt (centralAmbient half) rootId).1.2.2.2 = half := by
  apply centeredCubeSurface_timeCoordinate
  apply (centralLowerCubeRoot_sameSupport hhalf).1
  unfold geometricPolymer
  exact List.mem_map.mpr ⟨rootId, hroot, rfl⟩

theorem centralUpperCubeRoot_face_time
    {half rootId : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralUpperCubeRoot half) :
    (boxPlaquetteAt (centralAmbient half) rootId).1.2.2.2 = half + 1 := by
  apply centeredCubeSurface_timeCoordinate
  apply (centralUpperCubeRoot_sameSupport hhalf).1
  unfold geometricPolymer
  exact List.mem_map.mpr ⟨rootId, hroot, rfl⟩

private theorem timeCoordinate_linf_floor
    {root q : Z4Plaq} {rootTime qTime distance : Nat}
    (hrootTime : root.1.2.2.2 = rootTime)
    (hqTime : q.1.2.2.2 = qTime)
    (hseparation : rootTime + distance ≤ qTime) :
    distance ≤ linfDist root q := by
  have hmetric := le_linfDist_comp root q x3
  obtain ⟨⟨a, b, c, d⟩, rootPlane⟩ := root
  obtain ⟨⟨e, f, g, h⟩, qPlane⟩ := q
  change d = rootTime at hrootTime
  change h = qTime at hqTime
  simp only [natDist, cPlaq, vComp] at hmetric
  omega

/-- A lower central root is actually `half + 1` steps from every omitted
ambient face. -/
theorem centralLowerCubeRoot_nonSlab_linf_floor
    {half rootId : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralLowerCubeRoot half)
    {q : Z4Plaq}
    (hqBox : q ∈ boxPlaquettes (centralAmbient half))
    (hqNot : q ∉ boundaryCompleteSlabPlaquettes (centralExtent half)) :
    half + 1 ≤
      linfDist (boxPlaquetteAt (centralAmbient half) rootId) q := by
  have hrtime := centralLowerCubeRoot_face_time hhalf hroot
  have hqtime := ambient_nonSlab_time_eq_extent hqBox hqNot
  exact timeCoordinate_linf_floor hrtime hqtime (by
    unfold centralExtent
    omega)

/-- The upper central root is `half` steps from every omitted ambient face.
This is the common lower bound for the reflected root pair. -/
theorem centralUpperCubeRoot_nonSlab_linf_floor
    {half rootId : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralUpperCubeRoot half)
    {q : Z4Plaq}
    (hqBox : q ∈ boxPlaquettes (centralAmbient half))
    (hqNot : q ∉ boundaryCompleteSlabPlaquettes (centralExtent half)) :
    half ≤ linfDist (boxPlaquetteAt (centralAmbient half) rootId) q := by
  have hrtime := centralUpperCubeRoot_face_time hhalf hroot
  have hqtime := ambient_nonSlab_time_eq_extent hqBox hqNot
  exact timeCoordinate_linf_floor hrtime hqtime (by
    unfold centralExtent
    omega)

/-! ## 3. Exact complement-hit filter and its pinned tail -/

def canonicalPolymerHitsSlabComplementB
    (extent : Nat) (polymer : List Nat) : Bool :=
  (geometricPolymer (extent + 1) polymer).any fun q =>
    decide (q ∉ boundaryCompleteSlabPlaquettes extent)

theorem centralUpper_hit_complement_implies_reaches
    {half rootId : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralUpperCubeRoot half)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers (centralAmbient half))
    (hhit : canonicalPolymerHitsSlabComplementB
      (centralExtent half) polymer = true) :
    canonicalPolymerReachesB
      (centralAmbient half) rootId half polymer = true := by
  unfold canonicalPolymerHitsSlabComplementB at hhit
  obtain ⟨q, hq, hqNot⟩ := List.any_eq_true.mp hhit
  have hqBox := geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports hpolymer) q hq
  unfold canonicalPolymerReachesB
  exact List.any_eq_true.mpr ⟨q, hq, decide_eq_true
    (centralUpperCubeRoot_nonSlab_linf_floor
      hhalf hroot hqBox (of_decide_eq_true hqNot))⟩

theorem centralLower_hit_complement_implies_reaches
    {half rootId : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralLowerCubeRoot half)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers (centralAmbient half))
    (hhit : canonicalPolymerHitsSlabComplementB
      (centralExtent half) polymer = true) :
    canonicalPolymerReachesB
      (centralAmbient half) rootId half polymer = true := by
  unfold canonicalPolymerHitsSlabComplementB at hhit
  obtain ⟨q, hq, hqNot⟩ := List.any_eq_true.mp hhit
  have hqBox := geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports hpolymer) q hq
  unfold canonicalPolymerReachesB
  exact List.any_eq_true.mpr ⟨q, hq, decide_eq_true (Nat.le_trans
    (Nat.le_succ half)
    (centralLowerCubeRoot_nonSlab_linf_floor
      hhalf hroot hqBox (of_decide_eq_true hqNot)))⟩

def centralPinnedComplementHitSizeActivitySum
    (half rootId size : Nat) : Q' :=
  listQSum (canonicalSurfaceActivity anchorCoupling (centralAmbient half))
    ((canonicalPinnedSizePolymers
      (centralAmbient half) rootId size).filter
        (canonicalPolymerHitsSlabComplementB (centralExtent half)))

private theorem listQSum_filter_le_filter_on {A : Type}
    (weight : A → Q') (source target : A → Bool)
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ items : List A,
      (∀ item, item ∈ items → source item = true →
        target item = true) →
      listQSum weight (items.filter source) ≤
        listQSum weight (items.filter target)
  | [], _ => Q'.le_refl' 0
  | head :: tail, himplies => by
      have htail := listQSum_filter_le_filter_on
        weight source target hweight tail
        (fun item hmem => himplies item
          (List.mem_cons_of_mem head hmem))
      cases hsource : source head with
      | false =>
          cases htarget : target head with
          | false =>
              simpa only [List.filter, hsource, htarget, listQSum] using htail
          | true =>
              simp only [List.filter, hsource, htarget, listQSum]
              have hmono : listQSum weight (tail.filter target) ≤
                  weight head + listQSum weight (tail.filter target) := by
                have hscaled := Q'.add_le_add_right
                  (0 : Q') (weight head)
                  (listQSum weight (tail.filter target)) (hweight head)
                rwa [Q'.zero_add'] at hscaled
              exact Q'.le_trans' _ _ _ htail hmono
      | true =>
          have htarget : target head = true :=
            himplies head List.mem_cons_self hsource
          simp only [List.filter, hsource, htarget, listQSum]
          exact Q'.add_le_add_left (weight head) _ _ htail

theorem centralUpperPinnedComplementHitSizeActivitySum_le_reach
    {half rootId size : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralUpperCubeRoot half) :
    centralPinnedComplementHitSizeActivitySum half rootId size ≤
      canonicalPinnedReachSizeActivitySum
        (centralAmbient half) rootId half size := by
  unfold centralPinnedComplementHitSizeActivitySum
    canonicalPinnedReachSizeActivitySum
    canonicalPinnedReachSizePolymers
  exact listQSum_filter_le_filter_on _ _ _
    (canonicalSurfacePolymer_activity_nonnegative (centralAmbient half))
    (canonicalPinnedSizePolymers (centralAmbient half) rootId size)
    (fun polymer hmem hhit =>
      centralUpper_hit_complement_implies_reaches hhalf hroot
        (mem_canonicalPinnedSizePolymers_iff.mp hmem).1 hhit)

theorem centralLowerPinnedComplementHitSizeActivitySum_le_reach
    {half rootId size : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralLowerCubeRoot half) :
    centralPinnedComplementHitSizeActivitySum half rootId size ≤
      canonicalPinnedReachSizeActivitySum
        (centralAmbient half) rootId half size := by
  unfold centralPinnedComplementHitSizeActivitySum
    canonicalPinnedReachSizeActivitySum
    canonicalPinnedReachSizePolymers
  exact listQSum_filter_le_filter_on _ _ _
    (canonicalSurfacePolymer_activity_nonnegative (centralAmbient half))
    (canonicalPinnedSizePolymers (centralAmbient half) rootId size)
    (fun polymer hmem hhit =>
      centralLower_hit_complement_implies_reaches hhalf hroot
        (mem_canonicalPinnedSizePolymers_iff.mp hmem).1 hhit)

def centralPinnedComplementHitSizeWeightedActivity
    (half rootId size : Nat) : Q' :=
  centralPinnedComplementHitSizeActivitySum half rootId size *
    eSurrogate ^ size

def centralPinnedComplementHitTruncatedKPSum
    (half rootId sizeCutoff : Nat) : Q' :=
  finSum (fun size =>
    centralPinnedComplementHitSizeWeightedActivity half rootId size)
      sizeCutoff

theorem centralUpperPinnedComplementHitTruncatedKPSum_le_tail
    {half rootId sizeCutoff : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralUpperCubeRoot half) :
    centralPinnedComplementHitTruncatedKPSum
        half rootId sizeCutoff ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ (half + 1) := by
  unfold centralPinnedComplementHitTruncatedKPSum
    centralPinnedComplementHitSizeWeightedActivity
  have hsum := YMGap.Constructive.CharacterTail.finSum_le_termwise
    (fun size =>
      centralPinnedComplementHitSizeActivitySum half rootId size *
        eSurrogate ^ size)
    (fun size =>
      canonicalPinnedReachSizeActivitySum
          (centralAmbient half) rootId half size * eSurrogate ^ size)
    (fun size => Q'.mul_le_mul_of_nonneg_right _ _ _
      (centralUpperPinnedComplementHitSizeActivitySum_le_reach
        hhalf hroot)
      (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)) sizeCutoff
  exact Q'.le_trans' _ _ _ hsum
    (canonicalPinnedReachTruncatedKPSum_le_boundaryTail
      (centralAmbient half) rootId half sizeCutoff)

theorem centralLowerPinnedComplementHitTruncatedKPSum_le_tail
    {half rootId sizeCutoff : Nat} (hhalf : 1 ≤ half)
    (hroot : rootId ∈ centralLowerCubeRoot half) :
    centralPinnedComplementHitTruncatedKPSum
        half rootId sizeCutoff ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ (half + 1) := by
  unfold centralPinnedComplementHitTruncatedKPSum
    centralPinnedComplementHitSizeWeightedActivity
  have hsum := YMGap.Constructive.CharacterTail.finSum_le_termwise
    (fun size =>
      centralPinnedComplementHitSizeActivitySum half rootId size *
        eSurrogate ^ size)
    (fun size =>
      canonicalPinnedReachSizeActivitySum
          (centralAmbient half) rootId half size * eSurrogate ^ size)
    (fun size => Q'.mul_le_mul_of_nonneg_right _ _ _
      (centralLowerPinnedComplementHitSizeActivitySum_le_reach
        hhalf hroot)
      (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)) sizeCutoff
  exact Q'.le_trans' _ _ _ hsum
    (canonicalPinnedReachTruncatedKPSum_le_boundaryTail
      (centralAmbient half) rootId half sizeCutoff)

#print axioms ambient_nonSlab_time_eq_extent
#print axioms ambientNonSlabFaceId_time_eq_extent
#print axioms centralLowerCubeRoot_face_time
#print axioms centralUpperCubeRoot_face_time
#print axioms centralLowerCubeRoot_nonSlab_linf_floor
#print axioms centralUpperCubeRoot_nonSlab_linf_floor
#print axioms centralUpper_hit_complement_implies_reaches
#print axioms centralLower_hit_complement_implies_reaches
#print axioms centralUpperPinnedComplementHitSizeActivitySum_le_reach
#print axioms centralLowerPinnedComplementHitSizeActivitySum_le_reach
#print axioms centralUpperPinnedComplementHitTruncatedKPSum_le_tail
#print axioms centralLowerPinnedComplementHitTruncatedKPSum_le_tail

end YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
