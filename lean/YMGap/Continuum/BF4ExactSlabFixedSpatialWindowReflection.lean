/-
# Literal site reflection of ordered spatial-probe schedules

The source mirror changes an offset j to 2*h-j and retains the complete
signed character factor and list order. At a placement A with A+h equal
to the actual even-slab reflection center, this is the original geometric
reflection of every placed spatial face. The resulting ReflectionImage
uses the original oriented plaquette theorem, not a coordinate-reversal
surrogate. The lower schedule is one-sided, including the central slice.

These are finite observable placement and locality identities. No action,
normalization, reflection-positive limit, OS quotient or transfer operator
is constructed here. The consumer combines them with selected-chain site
reflection positivity and the existing whole-window original-action pin.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
import YMGap.Continuum.BF4ExactSlabSiteHeatAction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality

local notation:max "E" radius:arg => adjacentEvenExtent radius
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Reflect only offsets; signed factors, repetitions and order are unchanged. -/
def mirrorSchedule (h : Nat) (fs : List (Nat × List FaceFactor)) :
    List (Nat × List FaceFactor) :=
  fs.map (fun e => (2*h-e.1, e.2))

/-- Truncated subtraction always places the output inside the doubled window. -/
theorem mirrorSchedule_within (h : Nat) (fs : List (Nat × List FaceFactor)) :
    ∀ e, e ∈ mirrorSchedule h fs → e.1 ≤ 2*h := by
  intro e he
  obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
  exact Nat.sub_le _ _

theorem mirrorSchedule_faces {width : Nat} (h : Nat)
    (fs : List (Nat × List FaceFactor))
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ e, e ∈ mirrorSchedule h fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  exact hfaces g hg

/-- The mirrored compact polynomial has the exact doubled-window support. -/
theorem mirrorProbe_supported (width h : Nat) (fs : List (Nat × List FaceFactor)) :
    SupportedQuaternionBlocks ((2*h+1)*(N width))
      (windowProbe width (mirrorSchedule h fs)) :=
  windowProbe_supported width (2*h) _ (mirrorSchedule_within h fs)

/-- Every original placed product has ambient support, without geometric guards. -/
theorem placed_supported (extent A : Nat) (fs : List (Nat × List FaceFactor)) :
    SupportedQuaternionBlocks (B extent)
      (sweptProduct extent 0 (placeWindowProbes A fs)) :=
  product_supported (sweptCharacter extent 0) (swept_character_supported extent 0) _

theorem symmetric_window_contained {radius A h : Nat}
    (hcenter : A+h=radius+1) : A+2*h ≤ E radius := by
  unfold adjacentEvenExtent centralExtent
  omega

theorem placed_physical {width radius A h : Nat}
    (hw : width ≤ E radius) (hcenter : A+h=radius+1)
    (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ h)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeWindowProbes A fs → f.1 ∈ boundaryCompleteSlabPlaquettes (E radius) :=
  placeWindowProbes_physical hw
    (by
      have hc := symmetric_window_contained hcenter
      omega) fs hwithin hfaces

theorem mirrored_physical {width radius A h : Nat}
    (hw : width ≤ E radius) (hcenter : A+h=radius+1)
    (fs : List (Nat × List FaceFactor))
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeWindowProbes A (mirrorSchedule h fs) →
      f.1 ∈ boundaryCompleteSlabPlaquettes (E radius) :=
  placeWindowProbes_physical hw (symmetric_window_contained hcenter) _
    (mirrorSchedule_within h fs) (mirrorSchedule_faces h fs hfaces)

private theorem shifted_face_reflection {width radius A h j : Nat}
    (hcenter : A+h=radius+1) (hj : j ≤ h) {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) :
    timeReflectPlaquette (E radius) (timeShiftPlaquette (A+j) face) =
      timeShiftPlaquette (A+(2*h-j)) face := by
  obtain ⟨⟨x,y,z,d⟩, plane⟩ := face
  have hdata := (spatialFaces_mem_iff width ((x,y,z,d),plane)).mp hf
  have hd : d=0 := hdata.2.2.2.1
  have hsp := hdata.2.2.2.2
  subst d
  have ht : E radius - (A+j) = A+(2*h-j) := by
    unfold adjacentEvenExtent centralExtent
    omega
  cases plane <;> simp only [dirsOf] at hsp <;> try exact False.elim (hsp rfl)
  all_goals simp only [timeShiftPlaquette, timeShiftVertex, timeReflectPlaquette,
    Nat.zero_add, ht]

private theorem placeProbes_reflected {width radius A h j : Nat}
    (hcenter : A+h=radius+1) (hj : j ≤ h) (fs : List FaceFactor)
    (hfaces : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    (placeProbes (A+j) fs).map (fun f => (timeReflectPlaquette (E radius) f.1, f.2)) =
      placeProbes (A+(2*h-j)) fs := by
  simp only [placeProbes, List.map_map]
  apply List.map_congr_left
  intro f hf
  change (timeReflectPlaquette (E radius) (timeShiftPlaquette (A+j) f.1), f.2) =
    (timeShiftPlaquette (A+(2*h-j)) f.1, f.2)
  rw [shifted_face_reflection hcenter hj (hfaces f hf)]

/-- Literal list identity, including every signed factor and its original order. -/
theorem placed_faces_reflection {width radius A h : Nat}
    (hcenter : A+h=radius+1) :
    (fs : List (Nat × List FaceFactor)) →
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ h) →
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) →
    (placeWindowProbes A fs).map (fun f => (timeReflectPlaquette (E radius) f.1, f.2)) =
      placeWindowProbes A (mirrorSchedule h fs)
  | [], _, _ => rfl
  | e::es, hwithin, hfaces => by
      change (placeProbes (A+e.1) e.2 ++ placeWindowProbes A es).map
          (fun f => (timeReflectPlaquette (E radius) f.1, f.2)) =
        placeProbes (A+(2*h-e.1)) e.2 ++ placeWindowProbes A (mirrorSchedule h es)
      rw [List.map_append,
        placeProbes_reflected hcenter (hwithin e List.mem_cons_self) e.2
          (hfaces e List.mem_cons_self),
        placed_faces_reflection hcenter es
          (fun a ha => hwithin a (List.mem_cons_of_mem e ha))
          (fun a ha => hfaces a (List.mem_cons_of_mem e ha))]

private theorem reflection_sum {T : Type} (extent : Nat) (f g : T → RatPoly) :
    (xs : List T) → (∀ a, a ∈ xs → ReflectionImage extent (f a) (g a)) →
    ReflectionImage extent (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => ReflectionImage.zero extent
  | a::xs, h => (h a List.mem_cons_self).add
      (reflection_sum extent f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem factor_reflection {extent : Nat} (f : FaceFactor)
    (hf : f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    ReflectionImage extent
      (factor (fun face spin => characterPolynomial
        (correctedSlabPlaquettePolynomial extent face).scalar spin) f)
      (factor (fun face spin => characterPolynomial
        (correctedSlabPlaquettePolynomial extent face).scalar spin)
        (timeReflectPlaquette extent f.1, f.2)) :=
  reflection_sum extent _ _ f.2 (fun term _ =>
    (plaquette_character_reflection hf term.1).smul term.2)

private theorem product_reflection (extent : Nat) :
    (fs : List FaceFactor) →
    (∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) →
    ReflectionImage extent
      (product (fun face spin => characterPolynomial
        (correctedSlabPlaquettePolynomial extent face).scalar spin) fs)
      (product (fun face spin => characterPolynomial
        (correctedSlabPlaquettePolynomial extent face).scalar spin)
        (fs.map (fun f => (timeReflectPlaquette extent f.1, f.2))))
  | [], _ => ReflectionImage.one extent
  | f::fs, h => (factor_reflection f (h f List.mem_cons_self)).mul
      (product_reflection extent fs (fun g hg => h g (List.mem_cons_of_mem f hg)))

/-- Original geometric reflection of the placed signed schedule on the SAME slab. -/
theorem placed_reflection {width radius A h : Nat}
    (hw : width ≤ E radius) (hcenter : A+h=radius+1)
    (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ h)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ReflectionImage (E radius)
      (sweptProduct (E radius) 0 (placeWindowProbes A fs))
      (sweptProduct (E radius) 0 (placeWindowProbes A (mirrorSchedule h fs))) := by
  have hr := product_reflection (E radius) (placeWindowProbes A fs)
    (placed_physical hw hcenter fs hwithin hfaces)
  rw [placed_faces_reflection hcenter fs hwithin hfaces] at hr
  simpa only [swept_zero] using hr

private theorem spatial_not_upper {radius : Nat} {face : Z4Plaq}
    (hsp : (dirsOf face.2).2 ≠ Dir4.x3) (ht : face.1.2.2.2 ≤ radius+1) :
    adjacentEvenPlaquetteSide radius face ≠ .upper := by
  obtain ⟨⟨x,y,z,time⟩, plane⟩ := face
  change time ≤ radius+1 at ht
  cases plane <;> simp only [dirsOf] at hsp <;> try exact False.elim (hsp rfl)
  all_goals change adjacentEvenSpatialSide radius time ≠ .upper
  all_goals
    by_cases hl : time < radius+1
    · simp [adjacentEvenSpatialSide, adjacentEvenCenter, hl]
    · have he : time=radius+1 := by omega
      simp [adjacentEvenSpatialSide, adjacentEvenCenter, he]

private theorem character_oneSided {radius : Nat} {face : Z4Plaq}
    (hside : adjacentEvenPlaquetteSide radius face ≠ .upper) (spin : Nat) :
    OneSided radius (characterPolynomial
      (correctedSlabPlaquettePolynomial (E radius) face).scalar spin) := by
  intro term ht b hb hn
  apply ((face_scalar_local (E radius) face).character spin) term ht b hb
  intro hm
  apply hn
  intro hu
  exact hside (adjacentEven_upper_link_incident_face_upper hu hm)

private theorem product_oneSided (radius : Nat) (fs : List FaceFactor)
    (hside : ∀ f, f ∈ fs → adjacentEvenPlaquetteSide radius f.1 ≠ .upper) :
    OneSided radius (sweptProduct (E radius) 0 fs) := by
  rw [swept_zero]
  apply BlockLocal.fold
  intro f hf
  exact BlockLocal.finiteSum _ f.2 (fun term _ =>
    (character_oneSided (hside f hf) term.1).smul term.2)

/-- All original lower-window factors are one-sided; the central slice is allowed. -/
theorem placed_oneSided {width radius A h : Nat}
    (_hw : width ≤ E radius) (hcenter : A+h=radius+1)
    (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ h)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    OneSided radius (sweptProduct (E radius) 0 (placeWindowProbes A fs)) := by
  apply product_oneSided
  intro f hf
  obtain ⟨e, he, hfe⟩ := List.mem_flatMap.mp hf
  have ht := placeProbes_time (A+e.1) e.2 (hfaces e he) f hfe
  have hsp := placeProbes_spatial (A+e.1) e.2 (hfaces e he) f hfe
  apply spatial_not_upper hsp
  rw [ht]
  have hj := hwithin e he
  omega

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.mirrorSchedule
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.mirrorSchedule_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.mirrorSchedule_faces
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.mirrorProbe_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.placed_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.symmetric_window_contained
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.placed_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.mirrored_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.placed_faces_reflection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.placed_reflection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection.placed_oneSided
