/-
# The original plaquette as an actual closed Wilson source word

Every supplied physical spatial plaquette gives a closed endpoint-compatible
SourceLoop on the same width-only link carrier. Quaternion associativity and
the two unit laws identify the Wilson right fold with the original plaquette
left fold, without commuting factors or replacing a trace of a word by a
product of traces. The coefficient identity holds for every spin.

Literal time placement and spatial recentering retain this identity. The
fundamental character is also pinned to the old singleton face presentation,
so its original first and second finite moments can be compared without an
action or partition change. No equality of limits, completed-carrier map,
normalization, density or extension of a strict bound is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors (spatial_face_edge)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

private theorem boundary_compatible (face : Z4Plaq) :
    Compatible face.1 (orientedPlaquetteBoundary face) := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;>
    simp [Compatible, orientedPlaquetteBoundary, entryStart, entryFinish, dirsOf, addE]

private theorem boundary_physical {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) {entry : OrientedBF4Link}
    (he : entry ∈ orientedPlaquetteBoundary face) : entry.link ∈ baseLinks width := by
  have hl := orientedPlaquetteBoundary_link_mem_edgesOf he
  obtain ⟨hx, hy, hz, ht, hsp⟩ := (spatialFaces_mem_iff width face).mp hf
  have hb := face_edge_box hx hy hz hl
  have hs := spatial_face_edge face hsp entry.link hl
  exact (baseLinks_mem_iff width entry.link).mpr
    ⟨hs.1, hb.1, hb.2.1, hb.2.2, hs.2.trans ht⟩

/-- The four ORIGINAL oriented edges, with all source geometry proved. -/
def plaquetteLoop {width : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    SourceLoop width where
  start := face.1
  edges := orientedPlaquetteBoundary face
  compatible := boundary_compatible face
  closed := rfl
  physical := fun _ he => boundary_physical hf he

private theorem foldl_wordWith (value : OrientedBF4Link → PolyQuaternion) :
    ∀ (edges : List OrientedBF4Link) (q : PolyQuaternion),
    PolyQuaternionCoeffEqv
      (edges.foldl (fun acc entry => PolyQuaternion.mul acc (value entry)) q)
      (PolyQuaternion.mul q (wordWith value edges))
  | [], q => (PolyQuaternionCoeffEqv.mul_one q).symm
  | entry :: edges, q =>
      (foldl_wordWith value edges (PolyQuaternion.mul q (value entry))).trans
        (PolyQuaternionCoeffEqv.mul_assoc q (value entry) (wordWith value edges))

private theorem wordWith_foldl (value : OrientedBF4Link → PolyQuaternion)
    (edges : List OrientedBF4Link) :
    PolyQuaternionCoeffEqv (wordWith value edges)
      (edges.foldl (fun acc entry => PolyQuaternion.mul acc (value entry)) PolyQuaternion.one) :=
  ((foldl_wordWith value edges PolyQuaternion.one).trans
    (PolyQuaternionCoeffEqv.one_mul (wordWith value edges))).symm

/-- The source plaquette identity includes all four quaternion components. -/
theorem sourceWord_plaquette (width : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (sourceWord width (orientedPlaquetteBoundary face))
      (BF4ExactSlabFixedSpatialSliceHeat.plaquette width face) :=
  wordWith_foldl (orientedLink width) (orientedPlaquetteBoundary face)

theorem sourceCharacter_plaquette (width : Nat) (face : Z4Plaq) (spin : Nat) :
    RatPolyCoeffEqv (sourceCharacter width (orientedPlaquetteBoundary face) spin)
      (characterPolynomial (BF4ExactSlabFixedSpatialSliceHeat.plaquette width face).scalar spin) :=
  characterPolynomial_coeffEqv (sourceWord_plaquette width face).scalar spin

/-- The SAME ambient ordered word, independent of whether the face is physical. -/
theorem word_plaquette (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (word extent (orientedPlaquetteBoundary face))
      (correctedSlabPlaquettePolynomial extent face) :=
  wordWith_foldl (orientedCorrectedSlabLinkPolynomial extent) (orientedPlaquetteBoundary face)

theorem character_plaquette (extent : Nat) (face : Z4Plaq) (spin : Nat) :
    RatPolyCoeffEqv (character extent (orientedPlaquetteBoundary face) spin)
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) :=
  characterPolynomial_coeffEqv (word_plaquette extent face).scalar spin

theorem boundary_timeShift (time : Nat) (face : Z4Plaq) :
    orientedPlaquetteBoundary (timeShiftPlaquette time face) =
      (orientedPlaquetteBoundary face).map (shiftEntry time) := by
  simp only [orientedPlaquetteBoundary, timeShiftPlaquette, timeShiftLink, shiftEntry,
    List.map_cons, List.map_nil, timeShiftVertex_addE]

theorem boundary_translate (space : Nat) (face : Z4Plaq) :
    orientedPlaquetteBoundary (shiftFace space 0 face) =
      (orientedPlaquetteBoundary face).map (translateEntry space) := by
  simp only [orientedPlaquetteBoundary, shiftFace, shiftLink, translateEntry,
    List.map_cons, List.map_nil, shiftVertex_addE]

/-- Actual recenterLoop, not a separately chosen loop at the same face. -/
theorem recenterLoop_edges {width targetWidth space : Nat}
    (hroom : width+space ≤ targetWidth) (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    (recenterLoop hroom (plaquetteLoop face hf)).edges =
      orientedPlaquetteBoundary (shiftFace space 0 face) :=
  (boundary_translate space face).symm

/-- Placement agrees with the literal time-shifted old plaquette, for every spin. -/
theorem placed_character_plaquette {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (spin : Nat) :
    RatPolyCoeffEqv (character extent (placeLoop hw ht (plaquetteLoop face hf)).edges spin)
      (characterPolynomial
        (correctedSlabPlaquettePolynomial extent (timeShiftPlaquette time face)).scalar spin) := by
  change RatPolyCoeffEqv
    (character extent ((orientedPlaquetteBoundary face).map (shiftEntry time)) spin) _
  rw [← boundary_timeShift]
  exact character_plaquette extent (timeShiftPlaquette time face) spin

/-- Offset placement preserves the original all-spin character. -/
theorem placed_expression_plaquette {width : Nat} (extent start offset : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (spin : Nat) :
    RatPolyCoeffEqv
      (placedPolynomial extent start (.loop offset (plaquetteLoop face hf) spin))
      (characterPolynomial
        (correctedSlabPlaquettePolynomial extent (timeShiftPlaquette (start+offset) face)).scalar spin) := by
  change RatPolyCoeffEqv
    (character extent ((orientedPlaquetteBoundary face).map (shiftEntry (start+offset))) spin) _
  rw [← boundary_timeShift]
  exact character_plaquette extent (timeShiftPlaquette (start+offset) face) spin

theorem recentered_character_plaquette {width targetWidth space : Nat}
    (hroom : width+space ≤ targetWidth) (extent time : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (spin : Nat) :
    RatPolyCoeffEqv
      (character extent ((recenterLoop hroom (plaquetteLoop face hf)).edges.map (shiftEntry time)) spin)
      (characterPolynomial (correctedSlabPlaquettePolynomial extent
        (timeShiftPlaquette time (shiftFace space 0 face))).scalar spin) := by
  rw [recenterLoop_edges, ← boundary_timeShift]
  exact character_plaquette extent (timeShiftPlaquette time (shiftFace space 0 face)) spin

/-- The actual recentered window generator, at its original time offset. -/
theorem recentered_expression_plaquette {width targetWidth space : Nat}
    (hroom : width+space ≤ targetWidth) (extent start offset : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (spin : Nat) :
    RatPolyCoeffEqv
      (placedPolynomial extent start (recenterExpression hroom (.loop offset (plaquetteLoop face hf) spin)))
      (characterPolynomial (correctedSlabPlaquettePolynomial extent
        (timeShiftPlaquette (start+offset) (shiftFace space 0 face))).scalar spin) :=
  recentered_character_plaquette hroom extent (start+offset) face hf spin

/-- The exact old singleton presentation, including its coefficient/unit bookkeeping. -/
theorem fundamental_placedSpan {width : Nat} (extent time : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv (placedPolynomial extent time (.loop 0 (plaquetteLoop face hf) 1))
      (placedSpan extent time (facePresentation face)) := by
  have h := placed_expression_plaquette extent time 0 face hf 1
  simp only [Nat.add_zero] at h
  exact h.trans (placedSpan_character extent time face).symm

/-- Same finite fundamental insertion after the actual source-box recentering. -/
theorem recentered_fundamental_placedSpan {width targetWidth space : Nat}
    (hroom : width+space ≤ targetWidth) (extent time : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv
      (placedPolynomial extent time (recenterExpression hroom (.loop 0 (plaquetteLoop face hf) 1)))
      (placedSpan extent time (facePresentation (shiftFace space 0 face))) := by
  have h := recentered_expression_plaquette hroom extent time 0 face hf 1
  simp only [Nat.add_zero] at h
  exact h.trans (placedSpan_character extent time (shiftFace space 0 face)).symm

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.plaquetteLoop
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.sourceWord_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.sourceCharacter_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.word_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.character_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.boundary_timeShift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.boundary_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.recenterLoop_edges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.placed_character_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.placed_expression_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.recentered_character_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.recentered_expression_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.fundamental_placedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette.recentered_fundamental_placedSpan
