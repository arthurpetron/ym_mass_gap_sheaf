/-
# Temporal gauge on the literal corrected-slab faces

One common vertex field uses the actual fixed-time link at each spatial
vertex (the existing identity fallback off the carrier). Only upper links
are transformed. Every lower face is unchanged, every upper face character
is Haar-equivalent to the original, and every crossing face loses its two
fixed-time factors under arbitrary spectator insertions.

These are identities for one globally consistent link assignment. Realizing
that assignment by the scan-free Haar-preserving translation chain, and
gluing the resulting interface into reflected squares, remain separate.
-/

import YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

namespace YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram

/-- The fixed-time link at a vertex's spatial location. -/
def fixedTimeLink (half : Nat) (v : Z4Vertex) : Z4Link :=
  ((v.1, v.2.1, v.2.2.1, half), .x3)

/-- One common gauge field, not independently chosen gauges for each face. -/
def temporalVertexGauge (extent half : Nat) (v : Z4Vertex) : PolyQuaternion :=
  correctedSlabLinkPolynomial extent (fixedTimeLink half v)

/-- Transform only upper links by g_start^-1 U g_end. Lower and fixed
links retain exactly their original polynomial values. -/
def upperTemporalLink (extent half : Nat) (link : Z4Link) : PolyQuaternion :=
  if linkHalfSide half link = .upper then
    gaugeLink (temporalVertexGauge extent half link.1)
      (correctedSlabLinkPolynomial extent link)
      (temporalVertexGauge extent half (addE link.1 link.2))
  else correctedSlabLinkPolynomial extent link

/-- The original oriented plaquette boundary evaluated in that ONE assignment. -/
def temporalFaceWord (extent half : Nat) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (upperTemporalLink extent half (faceLinkA face))
    (upperTemporalLink extent half (faceLinkB face))
    (upperTemporalLink extent half (faceLinkC face))
    (upperTemporalLink extent half (faceLinkD face))

theorem slabLink_haar_unit (extent : Nat) (link : Z4Link) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm (correctedSlabLinkPolynomial extent link)) polyOne := by
  by_cases hm : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hm]
    exact haarNorm_coordinate (List.idxOf_lt_length_of_mem hm)
  · rw [correctedSlabLinkPolynomial_of_not_mem hm]
    exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one

theorem temporalVertexGauge_haar_unit (extent half : Nat) (v : Z4Vertex) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm (temporalVertexGauge extent half v)) polyOne := slabLink_haar_unit _ _

private theorem face_word (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial extent face)
      (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
        (correctedSlabLinkPolynomial extent (faceLinkB face))
        (correctedSlabLinkPolynomial extent (faceLinkC face))
        (correctedSlabLinkPolynomial extent (faceLinkD face))) :=
  (((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
    (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _)

private theorem upper_face_link {half : Nat} {face : Z4Plaq} {link : Z4Link}
    (hu : plaquetteHalfSide half face = .upper) (hi : link ∈ edgesOf face) :
    linkHalfSide half link = .upper := by
  cases hs : linkHalfSide half link with
  | upper => rfl
  | lower => exact False.elim ((lower_link_incident_face_ne_upper hs hi) hu)
  | fixed => have hf := fixed_link_incident_face_fixed hs hi; rw [hu] at hf; cases hf

private theorem lower_face_link {half : Nat} {face : Z4Plaq} {link : Z4Link}
    (hl : plaquetteHalfSide half face = .lower) (hi : link ∈ edgesOf face) :
    linkHalfSide half link ≠ .upper := fun hu => (upper_link_incident_face_ne_lower hu hi) hl

/-- Every lower face is literally untouched apart from removal of the
redundant initial unit in the original oriented fold. -/
theorem lower_face_unchanged (extent half : Nat) (face : Z4Plaq)
    (hl : plaquetteHalfSide half face = .lower) :
    PolyQuaternionCoeffEqv (temporalFaceWord extent half face) (correctedSlabPlaquettePolynomial extent face) := by
  have ha := lower_face_link hl (by simp [faceLinkA, edgesOf] : faceLinkA face ∈ edgesOf face)
  have hb := lower_face_link hl (by simp [faceLinkB, edgesOf] : faceLinkB face ∈ edgesOf face)
  have hc := lower_face_link hl (by simp [faceLinkC, edgesOf] : faceLinkC face ∈ edgesOf face)
  have hd := lower_face_link hl (by simp [faceLinkD, edgesOf] : faceLinkD face ∈ edgesOf face)
  simpa only [temporalFaceWord, upperTemporalLink, if_neg ha, if_neg hb, if_neg hc, if_neg hd]
    using (face_word extent face).symm

private theorem far_corner (face : Z4Plaq) :
    addE (addE face.1 (dirsOf face.2).2) (dirsOf face.2).1 =
      addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2 := by
  rcases face with ⟨⟨x,y,z,t⟩, plane⟩
  cases plane <;> rfl

/-- Every upper plaquette's all-spin character is preserved by the common
vertex field, under EVERY polynomial insertion on the original Haar carrier. -/
theorem upper_face_character (extent half : Nat) (face : Z4Plaq)
    (hu : plaquetteHalfSide half face = .upper) (spin : Nat) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (temporalFaceWord extent half face).scalar spin)
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) := by
  have ha := upper_face_link hu (by simp [faceLinkA, edgesOf] : faceLinkA face ∈ edgesOf face)
  have hb := upper_face_link hu (by simp [faceLinkB, edgesOf] : faceLinkB face ∈ edgesOf face)
  have hc := upper_face_link hu (by simp [faceLinkC, edgesOf] : faceLinkC face ∈ edgesOf face)
  have hd := upper_face_link hu (by simp [faceLinkD, edgesOf] : faceLinkD face ∈ edgesOf face)
  have h := plaquette_gauge_character
    (temporalVertexGauge extent half face.1)
    (temporalVertexGauge extent half (addE face.1 (dirsOf face.2).1))
    (temporalVertexGauge extent half (addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2))
    (temporalVertexGauge extent half (addE face.1 (dirsOf face.2).2))
    (correctedSlabLinkPolynomial extent (faceLinkA face))
    (correctedSlabLinkPolynomial extent (faceLinkB face))
    (correctedSlabLinkPolynomial extent (faceLinkC face))
    (correctedSlabLinkPolynomial extent (faceLinkD face))
    (temporalVertexGauge_haar_unit extent half _) (temporalVertexGauge_haar_unit extent half _)
    (temporalVertexGauge_haar_unit extent half _) (temporalVertexGauge_haar_unit extent half _) spin
  have hp : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (temporalFaceWord extent half face).scalar spin)
      (characterPolynomial (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
        (correctedSlabLinkPolynomial extent (faceLinkB face))
        (correctedSlabLinkPolynomial extent (faceLinkC face))
        (correctedSlabLinkPolynomial extent (faceLinkD face))).scalar spin) := by
    simp only [temporalFaceWord, upperTemporalLink, if_pos ha, if_pos hb, if_pos hc, if_pos hd]
    simp only [faceLinkA, faceLinkB, faceLinkC, faceLinkD]
    rw [far_corner face]
    exact h
  exact HaarCarrierEqv.trans hp
    (RatPolyCoeffEqv.haarCarrier (characterPolynomial_coeffEqv (face_word extent face).symm.scalar spin))

private theorem crossing_gauge_endpoints {half : Nat} {face : Z4Plaq}
    (hf : plaquetteHalfSide half face = .fixed) :
    fixedTimeLink half (faceLinkC face).1 = faceLinkD face ∧
      fixedTimeLink half (addE (faceLinkC face).1 (faceLinkC face).2) = faceLinkB face := by
  rcases face with ⟨⟨x,y,z,t⟩, plane⟩
  cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hf
  all_goals repeat' split at hf
  all_goals try cases hf
  all_goals subst t
  all_goals constructor <;> rfl

/-- BOTH literal fixed-time links disappear from the crossing word under
Haar; the remaining links are the original lower/upper spatial pair. -/
theorem crossing_face_word (extent half : Nat) (face : Z4Plaq)
    (hf : plaquetteHalfSide half face = .fixed) :
    PolyQuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (temporalFaceWord extent half face)
      (PolyQuaternion.mul (correctedSlabLinkPolynomial extent (faceLinkA face))
        (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (faceLinkC face)))) := by
  have hs := crossing_face_path_sides hf
  have hg := crossing_gauge_endpoints hf
  have ha : linkHalfSide half (faceLinkA face) ≠ .upper := by rw [hs.1]; decide
  have hb : linkHalfSide half (faceLinkB face) ≠ .upper := by rw [hs.2.1]; decide
  have hd : linkHalfSide half (faceLinkD face) ≠ .upper := by rw [hs.2.2.2]; decide
  simp only [temporalFaceWord, upperTemporalLink, if_neg ha, if_neg hb, if_pos hs.2.2.1, if_neg hd,
    temporalVertexGauge, hg.1, hg.2]
  exact crossing_temporal_shear _ _ _ _ (slabLink_haar_unit extent _) (slabLink_haar_unit extent _)

theorem crossing_face_character (extent half : Nat) (face : Z4Plaq)
    (hf : plaquetteHalfSide half face = .fixed) (spin : Nat) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (temporalFaceWord extent half face).scalar spin)
      (characterPolynomial (PolyQuaternion.mul (correctedSlabLinkPolynomial extent (faceLinkA face))
        (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (faceLinkC face)))).scalar spin) :=
  character_haar_congr (crossing_face_word extent half face hf).scalar spin

/-- The two remaining spatial links are the literal reflected pair at
every odd slab extent; no independent replacement coordinates are used. -/
theorem crossing_face_reflected_link {half : Nat} {face : Z4Plaq}
    (hf : plaquetteHalfSide half face = .fixed) :
    timeReflectLink (centralExtent half) (faceLinkA face) = faceLinkC face := by
  have ht : half + half + 1 - half = half + 1 := by omega
  rcases face with ⟨⟨x,y,z,t⟩, plane⟩
  cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hf
  all_goals repeat' split at hf
  all_goals try cases hf
  all_goals subst t
  all_goals simp only [faceLinkA, faceLinkC, dirsOf, addE, timeReflectLink, centralExtent, ht]

/-- Actual symmetric-power Gram kernel of a spatial link and its literal
time reflection, before either open half is integrated. -/
def reflectedSpatialLinkGram (extent : Nat) (link : Z4Link) (spin : Nat) :=
  polynomialGramKernel
    (asRepresentationQuaternion (correctedSlabLinkPolynomial extent (timeReflectLink extent link)))
    (asRepresentationQuaternion (correctedSlabLinkPolynomial extent link)) spin

/-- After the stated temporal link assignment, a crossing character is its
actual reflected spatial-link Gram kernel. This is still an identity, not
global slab positivity or a proof of the assignment's Haar invariance. -/
theorem crossing_face_reflected_gram (half : Nat) (face : Z4Plaq)
    (hf : plaquetteHalfSide half face = .fixed) (spin : Nat) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length
      (characterPolynomial (temporalFaceWord (centralExtent half) half face).scalar spin)
      (reflectedSpatialLinkGram (centralExtent half) (faceLinkA face) spin).1 ∧
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length
      (reflectedSpatialLinkGram (centralExtent half) (faceLinkA face) spin).2 polyZero := by
  have h := character_haar_gram_of_unit_radii
    (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half) (faceLinkC face)))
    (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half) (faceLinkA face)))
    (slabLink_haar_unit (centralExtent half) (faceLinkC face))
    (slabLink_haar_unit (centralExtent half) (faceLinkA face)) spin
  have hs := characterPolynomial_coeffEqv (pathProduct_scalar
    (correctedSlabLinkPolynomial (centralExtent half) (faceLinkC face))
    (correctedSlabLinkPolynomial (centralExtent half) (faceLinkA face))) spin
  simp only [reflectedSpatialLinkGram, crossing_face_reflected_link hf]
  exact ⟨QuaternionHaarCarrierEqv.trans (crossing_face_character (centralExtent half) half face hf spin)
    (QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier hs) h.1), h.2⟩

end YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces

#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.fixedTimeLink
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.temporalVertexGauge
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.upperTemporalLink
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.temporalFaceWord
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.slabLink_haar_unit
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.temporalVertexGauge_haar_unit
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.lower_face_unchanged
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.upper_face_character
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.crossing_face_word
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.crossing_face_character
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.crossing_face_reflected_link
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.reflectedSpatialLinkGram
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces.crossing_face_reflected_gram
