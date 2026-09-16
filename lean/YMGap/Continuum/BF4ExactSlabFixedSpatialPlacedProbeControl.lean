/-
# Uniform signed-probe control on the literal recentered chart insertion

The interval cap uses only the original ordered rational coefficients and
spins. Neither recentering margin, temporal buffer, ambient volume, nome nor
cutoff enters it. Locality is proved separately from the literal plaquette
edge lists, not inferred from a polynomial equivalence. The containing
connected box and its size depend only on the original spatial width and
the fixed observation chart. No expectation comparison is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
import YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_slabPlaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (placeProbes)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval (termCap factorCap probeCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe (placeWindowProbes_translation)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (supported_slabPlaquette)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The schedule order, repeated faces and signed spin coefficients survive. -/
def scheduleCap (fs : List (Nat × List FaceFactor)) : Q' :=
  probeCap (fs.flatMap Prod.snd)

/-- Outer signs are controlled by a square-root-free scalar cap. -/
def spanCap : Span → Q'
  | [] => 0
  | x::xs => (x.1*x.1+1)*scheduleCap x.2 + spanCap xs

def pairCap (xs ys : Span) : Q' := spanCap xs * spanCap ys

private def weightCap : List (List (Nat × Q')) → Q'
  | [] => 1
  | terms::rest => factorCap terms * weightCap rest

private theorem probeCap_weights : (fs : List FaceFactor) →
    probeCap fs = weightCap (fs.map Prod.snd)
  | [] => rfl
  | f::fs => by
      change factorCap f.2 * probeCap fs = factorCap f.2 * weightCap (fs.map Prod.snd)
      rw [probeCap_weights fs]

private theorem cap_placed (start : Nat) (fs : List (Nat × List FaceFactor)) :
    probeCap (placeWindowProbes start fs) = scheduleCap fs := by
  unfold scheduleCap
  rw [probeCap_weights, probeCap_weights]
  simp only [placeWindowProbes, placeProbes, List.map_flatMap, List.map_map,
    Function.comp_def]

private theorem scheduleCap_translate (space : Nat) (fs : List (Nat × List FaceFactor)) :
    scheduleCap (translateSchedule space fs) = scheduleCap fs := by
  unfold scheduleCap
  rw [probeCap_weights, probeCap_weights]
  simp only [translateSchedule, translateFactor, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

private theorem scheduleCap_encode (H : Nat) (fs : List (Nat × List FaceFactor)) :
    scheduleCap (encodeSchedule H fs) = scheduleCap fs := by
  unfold scheduleCap
  rw [probeCap_weights, probeCap_weights]
  simp only [encodeSchedule, List.flatMap_map]

private theorem scheduleCap_mirror (H : Nat) (fs : List (Nat × List FaceFactor)) :
    scheduleCap (mirrorSchedule H fs) = scheduleCap fs := by
  unfold scheduleCap
  rw [probeCap_weights, probeCap_weights]
  simp only [mirrorSchedule, List.flatMap_map]

theorem spanCap_translate (space : Nat) : (xs : Span) →
    spanCap (translateSpan space xs) = spanCap xs
  | [] => rfl
  | x::xs => by
      change (x.1*x.1+1)*scheduleCap (translateSchedule space x.2) +
        spanCap (translateSpan space xs) = (x.1*x.1+1)*scheduleCap x.2 + spanCap xs
      rw [scheduleCap_translate, spanCap_translate space xs]

theorem spanCap_encode (H : Nat) : (xs : Span) →
    spanCap (encodeChart H xs) = spanCap xs
  | [] => rfl
  | x::xs => by
      change (x.1*x.1+1)*scheduleCap (encodeSchedule H x.2) +
        spanCap (encodeChart H xs) = (x.1*x.1+1)*scheduleCap x.2 + spanCap xs
      rw [scheduleCap_encode, spanCap_encode H xs]

theorem spanCap_mirror (H : Nat) : (xs : Span) →
    spanCap (mirrorSpan H xs) = spanCap xs
  | [] => rfl
  | x::xs => by
      change (x.1*x.1+1)*scheduleCap (mirrorSchedule H x.2) +
        spanCap (mirrorSpan H xs) = (x.1*x.1+1)*scheduleCap x.2 + spanCap xs
      rw [scheduleCap_mirror, spanCap_mirror H xs]

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def signedInterval {blocks : Nat} {p : RatPoly} {a : Q'}
    (P : Interval blocks p a) (c : Q') :
    Interval blocks (polySmul c p) ((c*c+1)*a) :=
  Interval.ofCoeff (support_smul P.support c) (cap_mul_left c p).symm
    ((Interval.ofSquare (SquareBound.constant blocks c)).mul P)

private def termInterval (extent : Nat) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (term : Nat × Q') :
    Interval (B extent)
      (polySmul term.2
        (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar term.1))
      (termCap term) :=
  Interval.ofSquare ((character_squareBound
    (SquareBound.scalar (supported_slabPlaquette extent face)
      (haarNorm_slabPlaquette hf)) term.1).smul term.2)

private def factorInterval (extent : Nat) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    (terms : List (Nat × Q')) → Interval (B extent)
      (finitePolySum (fun term => polySmul term.2
        (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar term.1)) terms)
      (factorCap terms)
  | [] => Interval.zero (B extent)
  | term::terms => (termInterval extent face hf term).add (factorInterval extent face hf terms)

private def productInterval (extent : Nat) : (fs : List FaceFactor) →
    (∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) →
    Interval (B extent)
      (product (fun face spin =>
        characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) fs)
      (probeCap fs)
  | [], _ => Interval.one (B extent)
  | f::fs, hf => (factorInterval extent f.1 (hf f (by simp)) f.2).mul
      (productInterval extent fs (fun g hg => hf g (by simp [hg])))

/-- An ambient certificate for the actual zero-sweep original product. -/
def sweptProduct_interval (extent : Nat) (fs : List FaceFactor)
    (hf : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    Interval (B extent) (sweptProduct extent 0 fs) (probeCap fs) := by
  rw [swept_zero]
  exact productInterval extent fs hf

/-- Physicality is checked for the actual placed faces, not for a surrogate. -/
def placedSpan_interval (extent start : Nat) : (xs : Span) →
    (∀ x, x ∈ xs → ∀ f, f ∈ placeWindowProbes start x.2 →
      f.1 ∈ boundaryCompleteSlabPlaquettes extent) →
    Interval (B extent) (placedSpan extent start xs) (spanCap xs)
  | [], _ => Interval.zero (B extent)
  | x::xs, hf => by
      have P := sweptProduct_interval extent (placeWindowProbes start x.2)
        (hf x (by simp))
      rw [cap_placed] at P
      exact (signedInterval P x.1).add
        (placedSpan_interval extent start xs (fun y hy => hf y (by simp [hy])))

private theorem mirror_within (H : Nat) (xs : Span) : Within (2*H) (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_within H y.2

private theorem mirror_physical {width : Nat} (H : Nat) (xs : Span)
    (hx : Physical width xs) : Physical width (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces H y.2 (hx y hy)

private theorem encoded_within {H : Nat} {xs : Span} (hx : radius xs ≤ H) :
    Within (2*H) (encodeChart H xs) := by
  intro a ha e he
  have h := encodeChart_within H xs hx a ha e he
  omega

/-- Definitionally the reflected product appearing in the recentered chartScalar. -/
def chartProbe (base r H t : Nat) (x y : PhysicalSpan base) : RatPoly :=
  let E := chartExtent base r H t
  let A := paddedWidth base r+1+t
  polyMul (placedSpan E A (mirrorSpan H (encodeChart H (recenter r x).val)))
    (placedSpan E A (encodeChart H (recenter r y).val))

/-- Uniform in ambient volume, time buffer, cutoff and nome. -/
def chartProbe_interval (base r H t : Nat) (x y : PhysicalSpan base)
    (_hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    Interval (B (chartExtent base r H t)) (chartProbe base r H t x y)
      (pairCap x.val y.val) := by
  have hw : paddedWidth base r ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+2*H ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hyl : radius (recenter r y).val ≤ H := by rw [recenter_radius]; exact hy
  have Px := placedSpan_interval (chartExtent base r H t) (paddedWidth base r+1+t)
    (mirrorSpan H (encodeChart H (recenter r x).val)) (fun a ha =>
      placeWindowProbes_physical hw ht a.2
        (mirror_within H _ a ha)
        (mirror_physical H _ (encodeChart_physical H _ (recenter r x).property) a ha))
  have Py := placedSpan_interval (chartExtent base r H t) (paddedWidth base r+1+t)
    (encodeChart H (recenter r y).val) (fun a ha =>
      placeWindowProbes_physical hw ht a.2
        (encoded_within hyl a ha) (encodeChart_physical H _ (recenter r y).property a ha))
  have P := Px.mul Py
  simpa only [chartProbe, pairCap, spanCap_mirror, spanCap_encode, recenter,
    spanCap_translate] using P

/-- The fixed connected box contains all source spatial bases and chart times. -/
def boxSize (base H : Nat) : Nat := max base (2*H+1)

theorem boxSize_pos (base H : Nat) : 0 < boxSize base H := by
  have h := Nat.le_max_right base (2*H+1)
  unfold boxSize
  omega

def chartLinks (base r H t : Nat) : List Z4Link :=
  (boxLinks (boxSize base H)).map (shiftLink (r+1) (paddedWidth base r+1+t))

/-- The carrier contains actual connected-path and covering witnesses. -/
def chartCarrier (base r H t : Nat) : ProbeCarrier (chartLinks base r H t) :=
  shiftedBoxProbe (boxSize base H) (r+1) (paddedWidth base r+1+t) (boxSize_pos base H)

theorem chartCarrier_size (base r H t : Nat) :
    (chartCarrier base r H t).animal.support.length =
      (boxSize base H * boxSize base H * boxSize base H * boxSize base H)*6 :=
  shiftedBoxProbe_size _ _ _ _

theorem chartCarrier_root (base r H t : Nat) :
    (chartCarrier base r H t).animal.root =
      shiftFace (r+1) (paddedWidth base r+1+t) originFace := rfl

theorem chartLinks_length (base r H t : Nat) :
    (chartLinks base r H t).length =
      (boxSize base H * boxSize base H * boxSize base H * boxSize base H)*24 :=
  shiftedBoxLinks_length _ _ _

private theorem sweptProduct_local (extent : Nat) (links : List Z4Link)
    (fs : List FaceFactor)
    (hl : ∀ f, f ∈ fs → ∀ link, link ∈ edgesOf f.1 → link ∈ links) :
    LinkLocal extent links (sweptProduct extent 0 fs) := by
  rw [swept_zero]
  apply BlockLocal.fold
  intro f hf
  apply BlockLocal.finiteSum
  intro term _
  exact (((face_scalar_local extent f.1).mono (hl f hf)).character term.1).smul term.2

private theorem placedSpan_local (extent start : Nat) (links : List Z4Link)
    (xs : Span)
    (hl : ∀ x, x ∈ xs → ∀ f, f ∈ placeWindowProbes start x.2 →
      ∀ link, link ∈ edgesOf f.1 → link ∈ links) :
    LinkLocal extent links (placedSpan extent start xs) :=
  BlockLocal.finiteSum _ xs (fun x hx =>
    (sweptProduct_local extent links (placeWindowProbes start x.2) (hl x hx)).smul x.1)

private theorem original_face_box {base L : Nat} (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces base)
    {f : FaceFactor} (hf : f ∈ placeWindowProbes 0 fs) :
    f.1 ∈ boxPlaquettes (max base (L+1)) := by
  obtain ⟨e, he, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  have hp := (spatialFaces_mem_iff base g.1).mp (hfaces e he g hg)
  have ho := hwithin e he
  have hb := Nat.le_max_left base (L+1)
  have ht := Nat.le_max_right base (L+1)
  obtain ⟨⟨⟨a,b,c,z⟩, plane⟩, terms⟩ := g
  change a < base ∧ b < base ∧ c < base ∧ z = 0 ∧
    (dirsOf plane).2 ≠ Dir4.x3 at hp
  apply (mem_boxPlaquettes _ _).mpr
  simp only [timeShiftPlaquette, timeShiftVertex, Nat.zero_add]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Syntactic locality follows each literal placed face and its four edges. -/
theorem placedSpan_translated_local (base L space extent start : Nat) (xs : Span)
    (hx : Physical base xs) (hwithin : Within L xs) :
    LinkLocal extent ((boxLinks (max base (L+1))).map (shiftLink space start))
      (placedSpan extent start (translateSpan space xs)) := by
  apply placedSpan_local
  intro a ha f hf link hl
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have hplace := placeWindowProbes_translation space start 0 b.2
  simp only [Nat.zero_add] at hplace
  rw [hplace] at hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  rw [edgesOf_shiftFace] at hl
  obtain ⟨ell, hell, rfl⟩ := List.mem_map.mp hl
  exact List.mem_map.mpr ⟨ell,
    boundary_mem_boxLinks (original_face_box b.2 (hwithin b hb) (hx b hb) hg) hell, rfl⟩

private theorem encode_translate (H space : Nat) (xs : Span) :
    encodeChart H (translateSpan space xs) = translateSpan space (encodeChart H xs) := by
  simp only [encodeChart, translateSpan, encodeSchedule, translateSchedule,
    List.map_map, Function.comp_def]

private theorem mirror_translate (H space : Nat) (xs : Span) :
    mirrorSpan H (translateSpan space xs) = translateSpan space (mirrorSpan H xs) := by
  simp only [mirrorSpan, translateSpan, mirrorSchedule, translateSchedule,
    List.map_map, Function.comp_def]

/-- No polynomial-equivalence transport is used for this literal link support. -/
theorem chartProbe_local (base r H t : Nat) (x y : PhysicalSpan base)
    (_hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    LinkLocal (chartExtent base r H t) (chartLinks base r H t)
      (chartProbe base r H t x y) := by
  have Px := placedSpan_translated_local base (2*H) (r+1)
    (chartExtent base r H t) (paddedWidth base r+1+t)
    (mirrorSpan H (encodeChart H x.val))
    (mirror_physical H _ (encodeChart_physical H _ x.property))
    (mirror_within H _)
  have Py := placedSpan_translated_local base (2*H) (r+1)
    (chartExtent base r H t) (paddedWidth base r+1+t)
    (encodeChart H y.val) (encodeChart_physical H _ y.property) (encoded_within hy)
  have P := BlockLocal.mul Px Py
  simpa only [chartProbe, chartLinks, boxSize, recenter, encode_translate,
    mirror_translate] using P

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.spanCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.pairCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.spanCap_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.spanCap_encode
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.spanCap_mirror
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.sweptProduct_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.placedSpan_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.chartProbe_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.boxSize_pos
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.chartCarrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.chartCarrier_size
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.chartCarrier_root
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.chartLinks_length
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.placedSpan_translated_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl.chartProbe_local
