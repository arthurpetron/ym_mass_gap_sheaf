/-
# Original chart alignment when the unchanged base presentation is enlarged

At the same recentering margin r, inclusion from base to larger shifts the
ambient time by larger-base and does not translate space. The two selected
time intervals coincide, including the terminal spatial slice and strict
temporal-face endpoint. The smaller action is exactly a filtered sublist up
to permutation. Every omitted target face is at least r+1 from the same
recentered base face, irrespective of its time and orientation.

The original reflected insertion is transported by the explicit quaternion
Haar embedding, retaining its signed coefficients and ordered face words.
No equality with the full larger action, or equality of finite-width states,
is asserted. These are the geometry and observable pins for that comparison.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction
import YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBaseAlignedBoxes

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding (Placement)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedChain
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
  (chartExtent chartIds chartIds_physical chartIds_nodup)
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (Span Within Physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe
  (placedSpan_pin translateSpan_comp encodeChart_translate mirrorSpan_translate)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

theorem chartExtent_inclusion {base larger : Nat} (h : base ≤ larger) (r H t : Nat) :
    chartExtent larger r H t = chartExtent base r H t+2*(larger-base) := by
  unfold chartExtent adjacentEvenExtent centralExtent paddedWidth
  omega

theorem chart_start_inclusion {base larger : Nat} (h : base ≤ larger) (r : Nat) :
    paddedWidth base r+1+(larger-base) = paddedWidth larger r+1 := by
  unfold paddedWidth
  omega

/-- Same spatial coordinates and a computed time translation of the original
ambient link carrier, including all fringe links. -/
def placement {base larger : Nat} (h : base ≤ larger) (r H t : Nat) : Placement where
  source := chartExtent base r H t
  target := chartExtent larger r H t
  space := 0
  time := larger-base
  space_room := by rw [chartExtent_inclusion h]; omega
  time_room := by rw [chartExtent_inclusion h]; omega

def translatedChartIds {base larger : Nat} (h : base ≤ larger) (r H t : Nat) : List Nat :=
  (chartIds base r H t).map (placement h r H t).faceId

theorem placement_faceId_pin {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) {id : Nat} (hi : id ∈ chartIds base r H t) :
    slabPlaquetteAt (chartExtent larger r H t) ((placement h r H t).faceId id) =
      shiftFace 0 (larger-base) (slabPlaquetteAt (chartExtent base r H t) id) :=
  (placement h r H t).faceId_pin (chartIds_physical hi)

theorem translatedChartIds_faces_pin {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) :
    (translatedChartIds h r H t).map (slabPlaquetteAt (chartExtent larger r H t)) =
      (chartIds base r H t).map
        (fun id => shiftFace 0 (larger-base) (slabPlaquetteAt (chartExtent base r H t) id)) :=
  translatedIds_faces_pin (placement h r H t).space_room
    (placement h r H t).time_room _ _ _

theorem translatedChartIds_nodup {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) : (translatedChartIds h r H t).Nodup :=
  translatedIds_nodup (placement h r H t).space_room
    (placement h r H t).time_room _ _ _

theorem translatedChartIds_subset {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) {id : Nat} (hi : id ∈ translatedChartIds h r H t) :
    id ∈ chartIds larger r H t := by
  change id ∈ chainIds (chartExtent larger r H t) (paddedWidth larger r)
    (paddedWidth larger r+1) (t+(2*H+t))
  rw [← chart_start_inclusion h r]
  exact translatedIds_subset_chain (placement h r H t).space_room
    (placement h r H t).time_room
    (show paddedWidth base r+0 ≤ paddedWidth larger r by
      simpa only [Nat.add_zero] using paddedWidth_mono h r) hi

/-- The complete time windows agree. Only the smaller three spatial upper
bounds distinguish the actual translated selection inside the target chain. -/
theorem translatedChartIds_mem_iff {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) {id : Nat} (hi : id ∈ chartIds larger r H t) :
    id ∈ translatedChartIds h r H t ↔
      (slabPlaquetteAt (chartExtent larger r H t) id).1.1 < paddedWidth base r ∧
      (slabPlaquetteAt (chartExtent larger r H t) id).1.2.1 < paddedWidth base r ∧
      (slabPlaquetteAt (chartExtent larger r H t) id).1.2.2.1 < paddedWidth base r := by
  have hw : paddedWidth base r ≤ chartExtent base r H t+1 := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hs : paddedWidth base r+1+(t+(2*H+t)) ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hraw := translatedIds_mem_iff (placement h r H t).space_room
    (placement h r H t).time_room hw hs id
  change (id ∈ translatedChartIds h r H t ↔
    id ∈ slabPhysicalFaceEdges (chartExtent larger r H t) ∧
      TranslatedWindow 0 (larger-base) (paddedWidth base r) (paddedWidth base r+1)
        (t+(2*H+t)) (slabPlaquetteAt (chartExtent larger r H t) id)) at hraw
  constructor
  · intro hm
    obtain ⟨_, ha, _, hb, _, hc, _, _⟩ := (hraw.mp hm).2
    exact ⟨by omega, by omega, by omega⟩
  · intro hm
    obtain ⟨ha, hb, hc⟩ := hm
    have htarget := (chainIds_mem_iff (chartExtent larger r H t)
      (paddedWidth larger r) (paddedWidth larger r+1) (t+(2*H+t)) id).mp hi
    obtain ⟨hid, _, _, _, hl, hlast⟩ := htarget
    have hstart := chart_start_inclusion h r
    apply hraw.mpr
    refine ⟨hid, Nat.zero_le _, by omega, Nat.zero_le _, by omega,
      Nat.zero_le _, by omega, by omega, ?_⟩
    rcases hlast with hsp | htemp
    · exact Or.inl ⟨hsp.1, by omega⟩
    · exact Or.inr ⟨htemp.1, by omega⟩

private theorem near_recentered_spatial_box (base r timeOrigin : Nat)
    {p q : Z4Plaq} (hp : p ∈ spatialFaces base)
    (hd : linfDist (shiftFace (r+1) timeOrigin p) q < r+1) :
    q.1.1 < paddedWidth base r ∧ q.1.2.1 < paddedWidth base r ∧
      q.1.2.2.1 < paddedWidth base r := by
  obtain ⟨⟨a,b,c,z⟩, plane⟩ := p
  obtain ⟨⟨a',b',c',z'⟩, plane'⟩ := q
  have hbase := (spatialFaces_mem_iff base _).mp hp
  change a < base ∧ b < base ∧ c < base ∧ z = 0 ∧
    (dirsOf plane).2 ≠ Dir4.x3 at hbase
  obtain ⟨ha, hb, hc, _, _⟩ := hbase
  have h0 := Nat.lt_of_le_of_lt
    (le_linfDist_comp (shiftFace (r+1) timeOrigin ((a,b,c,z),plane))
      ((a',b',c',z'),plane') Dir4.x0) hd
  have h1 := Nat.lt_of_le_of_lt
    (le_linfDist_comp (shiftFace (r+1) timeOrigin ((a,b,c,z),plane))
      ((a',b',c',z'),plane') Dir4.x1) hd
  have h2 := Nat.lt_of_le_of_lt
    (le_linfDist_comp (shiftFace (r+1) timeOrigin ((a,b,c,z),plane))
      ((a',b',c',z'),plane') Dir4.x2) hd
  simp only [cPlaq, vComp, shiftFace, shiftVertex, natDist] at h0 h1 h2
  change a' < paddedWidth base r ∧ b' < paddedWidth base r ∧ c' < paddedWidth base r
  unfold paddedWidth
  exact ⟨by omega, by omega, by omega⟩

/-- Omitted target faces include every orientation and are separated from
the unchanged recentered base probe independently of the ambient time. -/
theorem omitted_separation {base larger : Nat} (h : base ≤ larger)
    (r H t timeOrigin : Nat) {p : Z4Plaq} (hp : p ∈ spatialFaces base)
    {id : Nat} (hi : id ∈ chartIds larger r H t)
    (ho : id ∉ translatedChartIds h r H t) :
    r+1 ≤ linfDist (shiftFace (r+1) timeOrigin p)
      (slabPlaquetteAt (chartExtent larger r H t) id) := by
  by_cases hd : r+1 ≤ linfDist (shiftFace (r+1) timeOrigin p)
      (slabPlaquetteAt (chartExtent larger r H t) id)
  · exact hd
  · exact False.elim (ho ((translatedChartIds_mem_iff h r H t hi).mpr
      (near_recentered_spatial_box base r timeOrigin hp (Nat.lt_of_not_ge hd))))

/-- The literal shared membership mask; no desired comparison is an input. -/
def keep {base larger : Nat} (h : base ≤ larger) (r H t id : Nat) : Bool :=
  decide (id ∈ translatedChartIds h r H t)

def insideIds {base larger : Nat} (h : base ≤ larger) (r H t : Nat) : List Nat :=
  BF4ExactSlabMixedAction.inside (keep h r H t) (chartIds larger r H t)

theorem keep_eq_true {base larger : Nat} (h : base ≤ larger) (r H t id : Nat) :
    keep h r H t id = true ↔ id ∈ translatedChartIds h r H t := by
  simp only [keep, decide_eq_true_eq]

theorem keep_eq_false {base larger : Nat} (h : base ≤ larger) (r H t id : Nat) :
    keep h r H t id = false ↔ id ∉ translatedChartIds h r H t := by
  simp only [keep, decide_eq_false_iff_not]

theorem insideIds_nodup {base larger : Nat} (h : base ≤ larger) (r H t : Nat) :
    (insideIds h r H t).Nodup := List.filter_sublist.nodup (chartIds_nodup larger r H t)

theorem insideIds_mem_iff {base larger : Nat} (h : base ≤ larger) (r H t id : Nat) :
    id ∈ insideIds h r H t ↔ id ∈ translatedChartIds h r H t := by
  constructor
  · intro hi
    exact (keep_eq_true h r H t id).mp (List.mem_filter.mp hi).2
  · intro hi
    exact List.mem_filter.mpr ⟨translatedChartIds_subset h r H t hi,
      (keep_eq_true h r H t id).mpr hi⟩

theorem insideIds_perm {base larger : Nat} (h : base ≤ larger) (r H t : Nat) :
    (insideIds h r H t).Perm (translatedChartIds h r H t) :=
  perm_of_nodup_mem_iff _ _ (insideIds_nodup h r H t)
    (translatedChartIds_nodup h r H t) (insideIds_mem_iff h r H t)

theorem insideIds_physical {base larger : Nat} (h : base ≤ larger) (r H t id : Nat)
    (hi : id ∈ insideIds h r H t) :
    id ∈ slabPhysicalFaceEdges (chartExtent larger r H t) :=
  chartIds_physical (List.mem_filter.mp hi).1

private theorem translate_within {L : Nat} (shift : Nat) (xs : Span)
    (hx : Within L xs) : Within L (translateSpan shift xs) := by
  intro x hm e he
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  exact hx y hy f hf

/-- Time placement is shifted but the recentered spatial words are identical. -/
theorem aligned_span_pin {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) (xs : Span) (hx : Physical base xs) (hwithin : Within (2*H) xs) :
    QuaternionPrefixPolynomialEqv (blocks (chartExtent larger r H t))
      ((placement h r H t).embedding.polynomial
        (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
          (translateSpan (r+1) xs)))
      (placedSpan (chartExtent larger r H t) (paddedWidth larger r+1+t)
        (translateSpan (r+1) xs)) := by
  have hw : paddedWidth base r ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : (paddedWidth base r+1+t)+2*H ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hphysical : Physical (paddedWidth base r) (translateSpan (r+1) xs) :=
    translateSpan_physical (by unfold paddedWidth; omega) xs hx
  have htranslated := placedSpan_pin (placement h r H t)
    (paddedWidth base r+1+t) (translateSpan (r+1) xs)
    (fun x hm => placeWindowProbes_physical hw ht x.2
      (translate_within (r+1) xs hwithin x hm) (hphysical x hm))
  change QuaternionPrefixPolynomialEqv (blocks (chartExtent larger r H t))
    ((placement h r H t).embedding.polynomial
      (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
        (translateSpan (r+1) xs)))
    (placedSpan (chartExtent larger r H t) ((paddedWidth base r+1+t)+(larger-base))
      (translateSpan 0 (translateSpan (r+1) xs))) at htranslated
  have hstart : (paddedWidth base r+1+t)+(larger-base) = paddedWidth larger r+1+t := by
    have hs := chart_start_inclusion h r
    omega
  simpa only [hstart, translateSpan_comp, Nat.add_zero] using htranslated

private theorem mirror_within (H : Nat) (xs : Span) : Within (2*H) (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_within H y.2

private theorem mirror_physical {width : Nat} (H : Nat) (xs : Span)
    (hx : Physical width xs) : Physical width (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces H y.2 (hx y hy)

/-- The original reflected chart insertion for the included presentations,
with the same radius and cutoff stage, not a new coordinate surrogate. -/
theorem aligned_chartInsertion_pin {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) (x y : PhysicalSpan base)
    (_hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    QuaternionPrefixPolynomialEqv (blocks (chartExtent larger r H t))
      ((placement h r H t).embedding.polynomial
        (polyMul
          (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
            (mirrorSpan H (encodeChart H (recenter r x).val)))
          (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
            (encodeChart H (recenter r y).val))))
      (polyMul
        (placedSpan (chartExtent larger r H t) (paddedWidth larger r+1+t)
          (mirrorSpan H (encodeChart H (recenter r (inclusion h x)).val)))
        (placedSpan (chartExtent larger r H t) (paddedWidth larger r+1+t)
          (encodeChart H (recenter r (inclusion h y)).val))) := by
  have hxphysical := encodeChart_physical H x.val x.property
  have hyphysical := encodeChart_physical H y.val y.property
  have hywithin : Within (2*H) (encodeChart H y.val) := by
    intro a ha e he
    have hb := encodeChart_within H y.val hy a ha e he
    omega
  have hleft := aligned_span_pin h r H t (mirrorSpan H (encodeChart H x.val))
    (mirror_physical H _ hxphysical) (mirror_within H _)
  have hright := aligned_span_pin h r H t (encodeChart H y.val) hyphysical hywithin
  rw [BlockEmbedding.polynomial_mul]
  simpa only [inclusion, recenter, encodeChart_translate, mirrorSpan_translate]
    using hleft.mul hright

#print axioms chartExtent_inclusion
#print axioms chart_start_inclusion
#print axioms placement
#print axioms translatedChartIds
#print axioms placement_faceId_pin
#print axioms translatedChartIds_faces_pin
#print axioms translatedChartIds_nodup
#print axioms translatedChartIds_subset
#print axioms translatedChartIds_mem_iff
#print axioms omitted_separation
#print axioms keep
#print axioms insideIds
#print axioms keep_eq_true
#print axioms keep_eq_false
#print axioms insideIds_nodup
#print axioms insideIds_mem_iff
#print axioms insideIds_perm
#print axioms insideIds_physical
#print axioms aligned_span_pin
#print axioms aligned_chartInsertion_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialBaseAlignedBoxes
